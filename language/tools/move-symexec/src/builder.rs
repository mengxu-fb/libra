// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use log::debug;
use std::{
    collections::BTreeSet,
    fs,
    io::{self, stdout, Write},
    path::{Path, PathBuf},
};

use move_lang::{
    compiled_unit::CompiledUnit,
    errors::{report_errors_to_buffer, report_errors_to_color_buffer},
    move_compile,
    shared::Address,
};
use vm::{file_format::CompiledScript, CompiledModule};

use crate::{
    configs::is_in_pretty_mode,
    utils::{PathToString, PathsToStrings},
    worker::{MoveStatefulWorker, MoveWorker, MoveWorkerAttr},
};

/// Tag added to log messages
const LOG_TAG: &str = "[compile]";

/// Attributes for a single-stage builder
#[derive(Clone, Default)]
pub(crate) struct MoveBuilderAttr {
    deps: BTreeSet<PathBuf>,
}

impl MoveWorkerAttr for MoveBuilderAttr {}

impl MoveBuilderAttr {
    fn dependencies(&self) -> Result<Vec<String>> {
        self.deps.iter().map(|p| p.path_to_string()).collect()
    }
}

/// A stackable builder that can compile Move programs in steps and backtracking to a prior state
pub(crate) type MoveBuilder = MoveWorker<(), MoveBuilderAttr>;

impl MoveBuilder {
    pub fn compile<P: AsRef<Path>, A: AsRef<[P]>>(
        &mut self,
        move_src: A,
        sender: Option<Address>,
        commit: bool,
    ) -> Result<(Vec<CompiledModule>, Vec<CompiledScript>)> {
        // compile
        let (files, units_or_errors) = move_compile(
            &move_src.paths_to_strings()?,
            &self.attr().dependencies()?,
            sender,
            None,
            true,
        )?;

        let compiled_units = match units_or_errors {
            Err(errors) => {
                let error_buffer = if is_in_pretty_mode() {
                    report_errors_to_color_buffer(files, errors)
                } else {
                    report_errors_to_buffer(files, errors)
                };
                stdout().lock().write_all(&error_buffer)?;
                bail!("Compilation failed");
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

        // find source locations in this compilation
        let canonicalized_src_paths = move_src
            .as_ref()
            .iter()
            .map(|p| p.as_ref().canonicalize())
            .collect::<io::Result<Vec<_>>>()?;
        let canonicalized_all_paths = files
            .into_iter()
            .map(|(key, _)| Path::new(key).canonicalize())
            .collect::<io::Result<Vec<_>>>()?;
        let src_files: BTreeSet<_> = canonicalized_all_paths
            .into_iter()
            .filter(|d| canonicalized_src_paths.iter().any(|s| d.starts_with(s)))
            .collect();

        // check duplicated compilation
        let deps = &self.attr().deps;
        let dups: BTreeSet<_> = deps.intersection(&src_files).collect();
        if !dups.is_empty() {
            if is_in_pretty_mode() {
                for dup in &dups {
                    writeln!(
                        stdout().lock(),
                        "Duplicated compilation of '{}'",
                        dup.file_name().unwrap().to_string_lossy()
                    )?;
                }
            }
            bail!("Duplicated compilation of source files: {}", dups.len());
        }

        // save files to dependencies (if commit)
        if commit {
            let attrs = self.attr_mut();
            attrs.deps.extend(src_files);
        }

        Ok((compiled_modules, compiled_scripts))
    }
}

/// Holds the current build state
#[derive(Default)]
pub(crate) struct MoveBuilderState {
    compiled_modules: Vec<CompiledModule>,
    compiled_scripts: Vec<CompiledScript>,
    source_locations: Vec<PathBuf>,
    sender_addresses: BTreeSet<Address>,
}

/// A stateful controller to run multiple build operations on Move programs
pub(crate) type MoveStatefulBuilder = MoveStatefulWorker<(), MoveBuilderAttr, MoveBuilderState>;

impl MoveStatefulBuilder {
    //
    // core operations
    //

    pub fn compile<P: AsRef<Path>, A: AsRef<[P]>>(
        &mut self,
        move_src: A,
        sender: Option<Address>,
        commit: bool,
    ) -> Result<()> {
        let (worker, state) = self.top_mut();

        let (mut modules, mut scripts) = worker.compile(move_src.as_ref(), sender, commit)?;
        debug!(
            "{} Sources compiled - modules: {}, scripts: {}",
            LOG_TAG,
            modules.len(),
            scripts.len(),
        );

        if commit {
            if !scripts.is_empty() {
                if let Some(address) = sender {
                    state.sender_addresses.insert(address);
                }
            }
            state.compiled_modules.append(&mut modules);
            state.compiled_scripts.append(&mut scripts);
            state.source_locations.extend(
                move_src
                    .as_ref()
                    .iter()
                    .map(fs::canonicalize)
                    .collect::<Result<Vec<_>, _>>()?,
            );
            debug!("{} Results committed", LOG_TAG);
        }

        Ok(())
    }

    //
    // get results (maybe across stack)
    //

    pub fn get_compiled_modules_recent(&self) -> Vec<&CompiledModule> {
        self.top_data().compiled_modules.iter().collect()
    }

    pub fn get_compiled_scripts_recent(&self) -> Vec<&CompiledScript> {
        self.top_data().compiled_scripts.iter().collect()
    }

    pub fn get_compiled_modules_all(&self) -> Vec<&CompiledModule> {
        self.iter_data()
            .map(|state| state.compiled_modules.iter())
            .flatten()
            .collect()
    }

    pub fn get_compiled_scripts_all(&self) -> Vec<&CompiledScript> {
        self.iter_data()
            .map(|state| state.compiled_scripts.iter())
            .flatten()
            .collect()
    }

    pub fn get_source_locations_all(&self) -> Vec<&Path> {
        self.iter_data()
            .map(|state| state.source_locations.iter())
            .flatten()
            .map(|path| path.as_path())
            .collect()
    }

    pub fn get_sender_addresses_all(&self) -> BTreeSet<&Address> {
        self.iter_data()
            .map(|state| state.sender_addresses.iter())
            .flatten()
            .collect()
    }

    pub fn get_compilation_dependencies(&self) -> Result<Vec<String>> {
        self.top_attr().dependencies()
    }
}
