// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use log::debug;
use std::io::{stdout, Write};

use move_core_types::{
    account_address::AccountAddress,
    gas_schedule::{GasAlgebra, GasUnits},
    language_storage::TypeTag,
    transaction_argument::{convert_txn_args, TransactionArgument},
};
use move_vm_runtime::{logging::NoContextLog, move_vm::MoveVM};
use move_vm_types::gas_schedule::{zero_cost_schedule, CostStrategy};
use vm::file_format::{CompiledModule, CompiledScript};

use crate::{
    data_store::MoveDataStore,
    worker::{MoveStatefulWorker, MoveWorker, MoveWorkerAttr},
};

/// Tag added to log messages
const LOG_TAG: &str = "[execute]";

impl MoveWorkerAttr for MoveDataStore {}

/// An executor worker (backed by the MoveDataStore) that can execute Move programs.
pub(crate) type MoveExecutor = MoveWorker<(), MoveDataStore>;

impl MoveExecutor {
    pub fn preload_modules<'a>(
        &mut self,
        modules: impl Iterator<Item = &'a CompiledModule>,
    ) -> Result<()> {
        let data_store = self.attr_mut();
        for module in modules {
            data_store.save_module(module)?;
        }
        Ok(())
    }

    pub fn execute_script(
        &mut self,
        script: &CompiledScript,
        signers: &[AccountAddress],
        val_args: &[TransactionArgument],
        type_args: &[TypeTag],
        commit: bool,
    ) -> Result<()> {
        // serialize script
        let mut script_bytes = vec![];
        script.serialize(&mut script_bytes)?;

        // convert args to values
        let exec_args = convert_txn_args(val_args);

        // init setup
        let log_context = NoContextLog::new();
        let cost_table = zero_cost_schedule();
        let mut cost_strategy = CostStrategy::system(&cost_table, GasUnits::new(0));

        // execution
        let vm = MoveVM::new();
        let mut session = vm.new_session(self.attr());
        let result = session.execute_script(
            script_bytes,
            type_args.to_owned(),
            exec_args,
            signers.to_owned(),
            &mut cost_strategy,
            &log_context,
        );

        // handle errors
        if let Err(err) = result {
            writeln!(stdout().lock(), "{}", err)?;
            bail!("Script execution failed");
        }

        // collect effects
        match session.finish() {
            Ok((change_set, events)) => {
                debug!(
                    "{} Script executed - changes: {}, events: {}",
                    LOG_TAG,
                    change_set
                        .accounts
                        .values()
                        .map(|c| c.resources.len())
                        .sum::<usize>(),
                    events.len(),
                );

                if commit {
                    let data_store = self.attr_mut();
                    data_store.apply_change_set(change_set)?;
                    for event in events {
                        data_store.save_event(event)?;
                    }
                    debug!("{} Results committed", LOG_TAG);
                }
            }
            Err(err) => {
                bail!("Session termination failed: {}", err);
            }
        }

        Ok(())
    }
}

/// A stateful controller to run multiple execution operations on Move programs
pub(crate) type MoveStatefulExecutor = MoveStatefulWorker<(), MoveDataStore, ()>;

impl MoveStatefulExecutor {
    //
    // core operations
    //

    pub fn preload_modules<'a>(
        &mut self,
        modules: impl Iterator<Item = &'a CompiledModule>,
    ) -> Result<()> {
        let (worker, _) = self.top_mut();
        worker.preload_modules(modules)
    }

    pub fn execute_script(
        &mut self,
        script: &CompiledScript,
        signers: &[AccountAddress],
        val_args: &[TransactionArgument],
        type_args: &[TypeTag],
        commit: bool,
    ) -> Result<()> {
        let (worker, _) = self.top_mut();
        worker.execute_script(script, signers, val_args, type_args, commit)
    }
}
