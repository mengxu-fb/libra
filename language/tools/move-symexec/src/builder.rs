// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use anyhow::{bail, Result};
use std::{
    fmt, fs,
    io::{stderr, Write},
    path::Path,
};
use tempfile::tempdir;

use move_lang::{
    self, compiled_unit::CompiledUnit, errors::report_errors_to_buffer, shared::Address,
    MOVE_COMPILED_EXTENSION,
};
use vm::{file_format::CompiledScript, CompiledModule};

use crate::utils;

/// Default directory containing interfaces under the builder workdir
const MOVE_COMPILED_INTERFACES_DIR: &str = "mv_interfaces";

/// Report compilation errors
#[derive(Debug)]
struct MoveCompilationError(String);

impl fmt::Display for MoveCompilationError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "\n\n{}", self.0)
    }
}

impl std::error::Error for MoveCompilationError {}

/// A stateful builder that can build Move programs in steps
pub(crate) struct MoveBuilder {
    workdir: String,
    all_interface_dirs: Vec<String>,
    clean_on_destroy: bool,
}

impl MoveBuilder {
    pub fn new(
        workdir: String,
        prior_builder: Option<&MoveBuilder>,
        clean_on_destroy: bool,
    ) -> Result<Self> {
        // prepare the directory
        let workdir_interfaces = join_path_items!(&workdir, MOVE_COMPILED_INTERFACES_DIR);
        utils::maybe_recreate_dir(&workdir)?;
        fs::create_dir_all(&workdir_interfaces)?;

        // collect interface dir from prior builder
        let mut all_interface_dirs = vec![workdir_interfaces];
        if let Some(builder) = prior_builder {
            all_interface_dirs.extend_from_slice(&builder.all_interface_dirs);
        }

        // done
        Ok(Self {
            workdir,
            all_interface_dirs,
            clean_on_destroy,
        })
    }

    pub fn load_modules(&self, move_bin: &[String], commit: bool) -> Result<Vec<CompiledModule>> {
        // load
        let compiled_modules = move_lang::find_filenames(move_bin, |fpath| {
            match fpath.extension().and_then(|s| s.to_str()) {
                None => false,
                Some(ext) => ext == MOVE_COMPILED_EXTENSION,
            }
        })?
        .iter()
        .map(|entry| {
            CompiledModule::deserialize(
                &fs::read(Path::new(entry))
                    .expect("Error: unable to read from compiled module file"),
            )
            .expect("Error: unable to deserialize compiled module")
        })
        .collect();

        // generate interfaces if commit: once committed, these modules
        // will serve as dependencies for the next round of compilation
        // as well as execution.
        if commit {
            move_lang::generate_interface_files(move_bin, Some(self.workdir.clone()), false)?;
        }

        // done
        Ok(compiled_modules)
    }

    pub fn compile(
        &self,
        move_src: &[String],
        sender: Option<Address>,
        commit: bool,
    ) -> Result<(Vec<CompiledModule>, Vec<CompiledScript>)> {
        // compile
        let (files, units_or_errors) =
            move_lang::move_compile_no_report(move_src, &self.all_interface_dirs, sender, None)?;

        let compiled_units = match units_or_errors {
            Err(errors) => {
                stderr()
                    .lock()
                    .write_all(&report_errors_to_buffer(files, errors))?;
                bail!("Unexpected failure in Move compilation");
            }
            Ok(units) => units,
        };

        // collect modules and scripts
        let mut compiled_modules = vec![];
        let mut compiled_scripts = vec![];
        for unit in compiled_units.iter() {
            match unit {
                CompiledUnit::Script { script, .. } => {
                    compiled_scripts.push(script.clone());
                }
                CompiledUnit::Module { module, .. } => {
                    compiled_modules.push(module.clone());
                }
            }
        }

        // generate interfaces if commit: once committed, these modules
        // will be serve as dependencies for next round of compilation
        if commit {
            // filter out scripts from compiled units
            let compiled_units_modules = compiled_units
                .into_iter()
                .filter(|unit| match unit {
                    CompiledUnit::Script { .. } => false,
                    CompiledUnit::Module { .. } => true,
                })
                .collect();

            let mv_dir = tempdir()?;
            let mv_dir_path = mv_dir.path().to_str().unwrap();
            move_lang::output_compiled_units(false, files, compiled_units_modules, mv_dir_path)?;
            move_lang::generate_interface_files(
                &[mv_dir_path.to_owned()],
                Some(self.workdir.clone()),
                false,
            )?;
        }

        // done
        Ok((compiled_modules, compiled_scripts))
    }
}

impl Drop for MoveBuilder {
    fn drop(&mut self) {
        if self.clean_on_destroy {
            utils::maybe_remove_dir(&self.workdir).unwrap_or_else(|_| {
                panic!(
                    "Unable to remove workdir for Move builder: {}",
                    &self.workdir
                )
            });
        }
    }
}
