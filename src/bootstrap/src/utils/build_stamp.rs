//! Module for managing build stamp files.
//!
//! Contains the core implementation of how bootstrap utilizes stamp files on build processes.

use std::path::{Path, PathBuf};
use std::{fs, io};

use crate::core::builder::Builder;
use crate::core::config::TargetSelection;
use crate::utils::helpers::mtime;
use crate::{Compiler, Mode, t};

#[cfg(test)]
mod tests;

/// Manages a stamp file to track build state. The file is created in the given
/// directory and can have custom content and name.
#[derive(Clone)]
pub struct BuildStamp {
    path: PathBuf,
    pub(crate) stamp: String,
}

impl AsRef<Path> for BuildStamp {
    fn as_ref(&self) -> &Path {
        &self.path
    }
}

impl BuildStamp {
    /// Creates a new `BuildStamp` for a given directory.
    ///
    /// By default, stamp will be an empty file named `.stamp` within the specified directory.
    pub fn new(dir: &Path) -> Self {
        Self { path: dir.join(".stamp"), stamp: String::new() }
    }

    /// Sets stamp content to the specified value.
    pub fn with_stamp<S: ToString>(mut self, stamp: S) -> Self {
        self.stamp = stamp.to_string();
        self
    }

    /// Adds a prefix to stamp's name.
    ///
    /// Prefix cannot start or end with a dot (`.`).
    pub fn with_prefix(mut self, prefix: &str) -> Self {
        assert!(
            !prefix.starts_with('.') && !prefix.ends_with('.'),
            "prefix can not start or end with '.'"
        );

        let stamp_filename = self.path.components().last().unwrap().as_os_str().to_str().unwrap();
        let stamp_filename = stamp_filename.strip_prefix('.').unwrap_or(stamp_filename);
        self.path.set_file_name(format!(".{prefix}-{stamp_filename}"));

        self
    }

    /// Removes the stamp file if it exists.
    pub fn remove(&self) -> io::Result<()> {
        match fs::remove_file(&self.path) {
            Ok(()) => Ok(()),
            Err(e) => {
                if e.kind() == io::ErrorKind::NotFound {
                    Ok(())
                } else {
                    Err(e)
                }
            }
        }
    }

    /// Creates the stamp file.
    pub fn write(&self) -> io::Result<()> {
        fs::write(&self.path, &self.stamp)
    }

    /// Checks if the stamp file is up-to-date.
    ///
    /// It is considered up-to-date if file content matches with the stamp string.
    pub fn is_up_to_date(&self) -> bool {
        match fs::read(&self.path) {
            Ok(h) => self.stamp.as_bytes() == h.as_slice(),
            Err(e) if e.kind() == io::ErrorKind::NotFound => false,
            Err(e) => {
                panic!("failed to read stamp file `{}`: {}", self.path.display(), e);
            }
        }
    }
}

/// Clear out `dir` if `input` is newer.
///
/// After this executes, it will also ensure that `dir` exists.
pub fn clear_if_dirty(builder: &Builder<'_>, dir: &Path, input: &Path) -> bool {
    let stamp = BuildStamp::new(dir);
    let mut cleared = false;
    if mtime(stamp.as_ref()) < mtime(input) {
        builder.verbose(|| println!("Dirty - {}", dir.display()));
        let _ = fs::remove_dir_all(dir);
        cleared = true;
    } else if stamp.as_ref().exists() {
        return cleared;
    }
    t!(fs::create_dir_all(dir));
    t!(fs::File::create(stamp));
    cleared
}

/// Cargo's output path for librustc_codegen_llvm in a given stage, compiled by a particular
/// compiler for the specified target and backend.
pub fn codegen_backend_stamp(
    builder: &Builder<'_>,
    compiler: Compiler,
    target: TargetSelection,
    backend: &str,
) -> BuildStamp {
    BuildStamp::new(&builder.cargo_out(compiler, Mode::Codegen, target))
        .with_prefix(&format!("librustc_codegen_{backend}"))
}

/// Cargo's output path for the standard library in a given stage, compiled
/// by a particular compiler for the specified target.
pub fn libstd_stamp(
    builder: &Builder<'_>,
    compiler: Compiler,
    target: TargetSelection,
) -> BuildStamp {
    BuildStamp::new(&builder.cargo_out(compiler, Mode::Std, target)).with_prefix("libstd")
}

/// Cargo's output path for librustc in a given stage, compiled by a particular
/// compiler for the specified target.
pub fn librustc_stamp(
    builder: &Builder<'_>,
    compiler: Compiler,
    target: TargetSelection,
) -> BuildStamp {
    BuildStamp::new(&builder.cargo_out(compiler, Mode::Rustc, target)).with_prefix("librustc")
}
