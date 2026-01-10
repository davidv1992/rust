use rustc_ast::Mutability;
use rustc_hir::LangItem;
use rustc_index::IndexVec;
use rustc_middle::mir::visit::MutVisitor;
use rustc_middle::mir::{
    BasicBlock, BasicBlockData, Body, BorrowKind, CallSource, Local, LocalDecl, Location,
    MutBorrowKind, Operand, Place, PlaceElem, Rvalue, SourceInfo, Statement, StatementKind,
    Terminator, TerminatorKind, UnwindAction, UnwindTerminateReason,
};
use rustc_middle::ty::{Ty, TyCtxt};
use rustc_span::DUMMY_SP;
use rustc_span::source_map::Spanned;

pub(super) struct ElaboratePlaceDerefs;

impl<'tcx> crate::MirPass<'tcx> for ElaboratePlaceDerefs {
    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        if tcx.lang_items().place_trait().is_none() || tcx.lang_items().deref_target().is_none() {
            // There can't be place dereferences unless these traits are present
            return;
        }

        let basic_blocks = body.basic_blocks.as_mut();

        for block in basic_blocks.indices().rev() {
            let location =
                Location { block, statement_index: basic_blocks[block].statements.len() };
            let source_info = basic_blocks[block].terminator().source_info;

            let mut finder = PlaceDerefFinder::new(tcx, &mut body.local_decls);
            finder.visit_terminator(basic_blocks[block].terminator_mut(), location);

            for task in finder.tasks() {
                insert_fixup(tcx, basic_blocks, &mut body.local_decls, location, source_info, task)
            }

            for statement_index in (0..basic_blocks[block].statements.len()).rev() {
                let location = Location { block, statement_index };
                let source_info = basic_blocks[block].statements[statement_index].source_info;

                let mut finder = PlaceDerefFinder::new(tcx, &mut body.local_decls);
                finder.visit_statement(
                    &mut basic_blocks[block].statements[statement_index],
                    location,
                );

                for task in finder.tasks() {
                    insert_fixup(
                        tcx,
                        basic_blocks,
                        &mut body.local_decls,
                        location,
                        source_info,
                        task,
                    );
                }
            }
        }
    }

    fn is_required(&self) -> bool {
        true
    }
}

fn insert_fixup<'tcx>(
    tcx: TyCtxt<'tcx>,
    basic_blocks: &mut IndexVec<BasicBlock, BasicBlockData<'tcx>>,
    local_decls: &mut IndexVec<Local, LocalDecl<'tcx>>,
    location: Location,
    source_info: SourceInfo,
    task: TaskDescriptor<'tcx>,
) {
    let block_data = &mut basic_blocks[location.block];

    // Drain every statement after this one and move the current terminator to a new basic block.
    let new_block = BasicBlockData::new_stmts(
        block_data.statements.split_off(location.statement_index),
        block_data.terminator.take(),
        block_data.is_cleanup,
    );

    let new_block = basic_blocks.push(new_block);

    let block_data = &mut basic_blocks[location.block];

    let ref_ty = Ty::new_ref(
        tcx,
        tcx.lifetimes.re_erased,
        task.original_ty,
        if task.mutating { Mutability::Mut } else { Mutability::Not },
    );

    let ref_local =
        local_decls.push(LocalDecl::new(ref_ty, local_decls[task.original].source_info.span));

    block_data.statements.push(Statement::new(
        source_info,
        StatementKind::Assign(Box::new((
            Place::from(ref_local),
            Rvalue::Ref(
                tcx.lifetimes.re_erased,
                if task.mutating {
                    BorrowKind::Mut { kind: MutBorrowKind::Default }
                } else {
                    BorrowKind::Shared
                },
                Place::from(task.original),
            ),
        ))),
    ));

    block_data.terminator = Some(Terminator {
        source_info,
        kind: TerminatorKind::Call {
            func: Operand::function_handle(
                tcx,
                tcx.require_lang_item(LangItem::PlaceDeref, source_info.span),
                [task.original_ty.into()],
                source_info.span,
            ),
            args: [Spanned { node: Operand::Move(Place::from(ref_local)), span: DUMMY_SP }].into(),
            destination: Place::from(task.pointer),
            target: Some(new_block),
            //FIXME: Make this a dedicated unwind reason (or actually allow unwinding of places somehow)
            unwind: UnwindAction::Terminate(UnwindTerminateReason::Abi),
            call_source: CallSource::Misc,
            fn_span: source_info.span,
        },
    })
}

struct TaskDescriptor<'tcx> {
    original: Local,
    pointer: Local,
    original_ty: Ty<'tcx>,
    mutating: bool,
}

#[allow(unused)]
struct PlaceDerefFinder<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    local_decls: &'a mut IndexVec<Local, LocalDecl<'tcx>>,
    tasks: Vec<TaskDescriptor<'tcx>>,
}

impl<'a, 'tcx> PlaceDerefFinder<'a, 'tcx> {
    fn new(tcx: TyCtxt<'tcx>, local_decls: &'a mut IndexVec<Local, LocalDecl<'tcx>>) -> Self {
        Self { tcx, local_decls, tasks: vec![] }
    }

    fn tasks(self) -> impl Iterator<Item = TaskDescriptor<'tcx>> + 'tcx {
        self.tasks.into_iter()
    }
}

impl<'a, 'tcx> MutVisitor<'tcx> for PlaceDerefFinder<'a, 'tcx> {
    fn tcx<'b>(&'b self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_place(
        &mut self,
        place: &mut rustc_middle::mir::Place<'tcx>,
        context: rustc_middle::mir::visit::PlaceContext,
        location: rustc_middle::mir::Location,
    ) {
        let base_ty = self.local_decls[place.local].ty;

        if let Some(PlaceElem::Deref) = place.projection.first()
            && !(base_ty.is_any_ptr() || base_ty.is_box())
        {
            let pointer_ty = Ty::new_imm_ptr(
                self.tcx,
                Ty::new_projection(
                    self.tcx,
                    self.tcx.lang_items().deref_target().unwrap(),
                    [base_ty],
                ),
            );

            let source_info = self.local_decls[place.local].source_info;

            let new_local = self.local_decls.push(LocalDecl::new(pointer_ty, source_info.span));

            self.tasks.push(TaskDescriptor {
                original: place.local,
                pointer: new_local,
                original_ty: base_ty,
                mutating: context.is_mutating_use(),
            });

            place.local = new_local;
        }

        self.super_place(place, context, location);
    }
}
