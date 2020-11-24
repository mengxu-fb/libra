// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use log::debug;
use std::{
    fs,
    io::{stderr, Write},
    path::{Path, PathBuf},
};
use tempfile::tempdir;

use move_lang::{
    compiled_unit::CompiledUnit, errors::report_errors_to_buffer, move_compile_no_report,
    shared::Address,
};
use vm::{file_format::CompiledScript, CompiledModule};

use crate::utils::{PathToString, PathsToStrings};

/// Default directory containing interfaces under the builder workdir
const MOVE_COMPILED_INTERFACES_DIR: &str = "mv_interfaces";

/// A builder worker in a stateful implementation that can build Move programs in steps
struct MoveBuilder {
    workdir: PathBuf,
    all_interface_dir: Vec<PathBuf>,
}

impl MoveBuilder {
    /// Create a new builder, assuming that `workdir` is already created.
    pub fn new(workdir: PathBuf, parent: Option<&MoveBuilder>) -> Result<Self> {
        // prepare the directory
        let interface_dir = workdir.join(MOVE_COMPILED_INTERFACES_DIR);
        fs::create_dir(&interface_dir)?;

        // append the interface dir
        let mut all_interface_dir =
            parent.map_or(vec![], |builder| builder.all_interface_dir.clone());
        all_interface_dir.push(interface_dir);

        // done
        Ok(Self {
            workdir,
            all_interface_dir,
        })
    }

    pub fn compile<P: AsRef<Path>, A: AsRef<[P]>>(
        &self,
        move_src: A,
        sender: Option<Address>,
        commit: bool,
    ) -> Result<(Vec<CompiledModule>, Vec<CompiledScript>)> {
        // compile
        let (files, units_or_errors) = move_compile_no_report(
            &move_src.paths_to_strings()?,
            &self.all_interface_dir.paths_to_strings()?,
            sender,
            None,
        )?;

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

        // generate interfaces if commit: once committed, these modules will serve as dependencies
        // for next round of compilation
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
            let mv_dir_path = mv_dir.path().path_to_string()?;
            move_lang::output_compiled_units(false, files, compiled_units_modules, &mv_dir_path)?;
            move_lang::generate_interface_files(
                &[mv_dir_path],
                Some(self.workdir.path_to_string()?),
                false,
            )?;
        }

        // done
        Ok((compiled_modules, compiled_scripts))
    }
}

/// Holds the current build state
struct OpBuildState {
    builder: MoveBuilder,
    compiled_modules: Vec<CompiledModule>,
    compiled_scripts: Vec<CompiledScript>,
    source_locations: Vec<PathBuf>,
}

impl OpBuildState {
    pub fn new(workdir: PathBuf, parent: Option<&MoveBuilder>) -> Result<Self> {
        fs::create_dir(&workdir)?;
        Ok(Self {
            builder: MoveBuilder::new(workdir, parent)?,
            compiled_modules: vec![],
            compiled_scripts: vec![],
            source_locations: vec![],
        })
    }
}

/// A stateful controller to run multiple build operations on Move programs
pub struct MoveStatefulBuilder {
    workdir: PathBuf,
    op_stack: Vec<OpBuildState>,
    num_contexts: usize,
}

impl MoveStatefulBuilder {
    /// Create a new controller, assuming that `workdir` is already created
    pub fn new(workdir: PathBuf) -> Result<Self> {
        // create the initial states
        let state = OpBuildState::new(workdir.join("0"), None)?;

        // done
        Ok(Self {
            workdir,
            op_stack: vec![state],
            num_contexts: 1,
        })
    }

    // core operations
    pub fn compile<P: AsRef<Path>, A: AsRef<[P]>>(
        &mut self,
        move_src: A,
        sender: Option<Address>,
        commit: bool,
    ) -> Result<()> {
        let state = self.get_state_mut();

        let (mut modules, mut scripts) =
            state.builder.compile(move_src.as_ref(), sender, commit)?;
        debug!(
            "{} module(s) + {} script(s) compiled",
            modules.len(),
            scripts.len()
        );

        if commit {
            state.compiled_modules.append(&mut modules);
            state.compiled_scripts.append(&mut scripts);
            state.source_locations.extend(
                move_src
                    .as_ref()
                    .iter()
                    .map(|path| path.as_ref().to_path_buf()),
            );
        }

        Ok(())
    }

    // stack operations
    fn get_state(&self) -> &OpBuildState {
        self.op_stack.last().unwrap()
    }

    fn get_state_mut(&mut self) -> &mut OpBuildState {
        self.op_stack.last_mut().unwrap()
    }

    pub fn push(&mut self) -> Result<()> {
        let old_state = self.get_state();
        let new_state = OpBuildState::new(
            self.workdir.join(self.num_contexts.to_string()),
            Some(&old_state.builder),
        )?;

        self.op_stack.push(new_state);
        self.num_contexts += 1;
        Ok(())
    }

    pub fn pop(&mut self) -> Result<()> {
        if self.op_stack.len() == 1 {
            bail!("Build controller: more pops than push?");
        } else {
            self.op_stack.pop();
        }
        Ok(())
    }

    // get results (maybe across stack)
    pub fn get_compiled_modules_recent(&self) -> Vec<&CompiledModule> {
        self.get_state().compiled_modules.iter().collect()
    }

    pub fn get_compiled_scripts_recent(&self) -> Vec<&CompiledScript> {
        self.get_state().compiled_scripts.iter().collect()
    }

    pub fn get_compiled_modules_all(&self) -> Vec<&CompiledModule> {
        self.op_stack
            .iter()
            .map(|state| state.compiled_modules.iter())
            .flatten()
            .collect()
    }

    pub fn get_compiled_scripts_all(&self) -> Vec<&CompiledScript> {
        self.op_stack
            .iter()
            .map(|state| state.compiled_scripts.iter())
            .flatten()
            .collect()
    }

    pub fn get_source_locations_all(&self) -> Vec<&Path> {
        self.op_stack
            .iter()
            .map(|state| state.source_locations.iter())
            .flatten()
            .map(|path| path.as_path())
            .collect()
    }
}
