// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use log::debug;

use move_core_types::language_storage::TypeTag;
use move_model::model::GlobalEnv;

use crate::{
    sym_env::{SymEnv, SymTypeArg},
    worker::{MoveStatefulWorker, MoveWorker, MoveWorkerAttr},
};

/// Tag added to log messages
const LOG_TAG: &str = "[symeval]";

/// Attributes for a single-stage symbolizer
#[derive(Clone, Default)]
pub(crate) struct MoveSymbolizerAttr {}

impl MoveWorkerAttr for MoveSymbolizerAttr {}

/// A symbolizer worker that can symbolic Move programs
pub(crate) type MoveSymbolizer = MoveWorker<GlobalEnv, MoveSymbolizerAttr>;

impl MoveSymbolizer {
    pub fn symbolize(&self, type_args: &[TypeTag], no_pipeline: bool) -> Result<()> {
        // transform the program
        let sym_env = SymEnv::new(self.info(), no_pipeline);
        debug!(
            "{} Transformation finished: tracking {} functions and {} structs",
            LOG_TAG,
            sym_env.num_functions(),
            sym_env.num_structs(),
        );

        // check and convert the type arguments
        let script = sym_env.get_script_exec_unit();
        let type_params = script.func_env.get_named_type_parameters();
        if type_params.len() != type_args.len() {
            bail!(
                "Wrong number of type arguments specified: expect {}, got {}",
                type_params.len(),
                type_args.len()
            );
        }
        let sym_type_args = type_args
            .iter()
            .map(|ty_arg| SymTypeArg::from_type_tag(ty_arg, &sym_env))
            .collect::<Result<Vec<_>>>()?;
        for (sym_ty_arg, ty_param) in sym_type_args.iter().zip(type_params.iter()) {
            if !sym_ty_arg.satisfies_abilities_constraints(ty_param.1) {
                bail!(
                    "Invalid type argument for '{}': abilities constraints not satisfied",
                    sym_env.script_env.symbol_pool().string(ty_param.0)
                );
            }
        }

        // TODO: implement the logic
        debug!("{} Program symbolized", LOG_TAG);
        Ok(())
    }
}

/// A stateful controller to run multiple symbolization operations on Move programs
pub(crate) type MoveStatefulSymbolizer = MoveStatefulWorker<GlobalEnv, MoveSymbolizerAttr, ()>;

impl MoveStatefulSymbolizer {
    //
    // core operations
    //

    pub fn symbolize(&self, type_args: &[TypeTag], use_pipeline: bool) -> Result<()> {
        self.top_worker().symbolize(type_args, use_pipeline)
    }
}
