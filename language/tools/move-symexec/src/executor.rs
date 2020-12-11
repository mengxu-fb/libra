// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use log::debug;
use std::{
    collections::HashMap,
    io::{stderr, Write},
    path::PathBuf,
};

use diem_vm::txn_effects_to_writeset_and_events;
use language_e2e_tests::data_store::FakeDataStore;
use move_core_types::{
    account_address::AccountAddress,
    gas_schedule::{GasAlgebra, GasUnits},
    language_storage::TypeTag,
    transaction_argument::TransactionArgument,
};
use move_vm_runtime::{logging::NoContextLog, move_vm::MoveVM};
use move_vm_types::{gas_schedule::CostStrategy, values::Value};
use vm::file_format::{CompiledModule, CompiledScript};
use vm_genesis::genesis_gas_schedule::INITIAL_GAS_SCHEDULE;

/// An executor worker (backed by the FakeDataStore) that can execute Move programs that consist of
/// a sequence of Move scripts in steps.
/// The `data_store` is in-memory only and has no on-disk effect (this might change in the future)
#[derive(Clone, Debug)]
pub(crate) struct MoveExecutor {
    _workdir: PathBuf,
    data_store: FakeDataStore,
}

impl MoveExecutor {
    /// Create a new symbolizer, assuming that `workdir` is already created.
    pub fn new(workdir: PathBuf) -> Self {
        Self {
            _workdir: workdir,
            data_store: FakeDataStore::new(HashMap::new()),
        }
    }

    pub fn preload_modules(&mut self, modules: &[&CompiledModule]) {
        for module in modules {
            self.data_store.add_module(&module.self_id(), module);
        }
    }

    pub fn execute_script(
        &mut self,
        script: &CompiledScript,
        signers: &[AccountAddress],
        val_args: &[TransactionArgument],
        type_args: &[TypeTag],
        expect_failure: bool,
        commit: bool,
    ) -> Result<()> {
        // serialize script
        let mut script_bytes = vec![];
        script.serialize(&mut script_bytes)?;

        // convert args to values
        let exec_args = val_args
            .iter()
            .map(|arg| match arg {
                TransactionArgument::U8(i) => Value::u8(*i),
                TransactionArgument::U64(i) => Value::u64(*i),
                TransactionArgument::U128(i) => Value::u128(*i),
                TransactionArgument::Address(a) => Value::address(*a),
                TransactionArgument::Bool(b) => Value::bool(*b),
                TransactionArgument::U8Vector(v) => Value::vector_u8(v.clone()),
            })
            .collect();

        // init setup
        let log_context = NoContextLog::new();
        let mut cost_strategy = CostStrategy::system(&INITIAL_GAS_SCHEDULE, GasUnits::new(0));

        // execution
        let vm = MoveVM::new();
        let mut session = vm.new_session(&self.data_store);
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
            if expect_failure {
                debug!("{}", err);
            } else {
                writeln!(stderr().lock(), "{}", err)?;
                bail!("Unexpected failure in Move script execution");
            }
        } else if expect_failure {
            bail!("Expected failure in script execution but none reported");
        }

        // collect effects
        match session.finish() {
            Ok(effects) => {
                debug!(
                    "Script executed - modules: {}, resources: {}, events: {}",
                    effects.modules.len(),
                    effects.resources.len(),
                    effects.events.len(),
                );

                // effects are discarded and not committed to states
                match txn_effects_to_writeset_and_events(effects) {
                    Ok((writeset, _events)) => {
                        if commit {
                            self.data_store.add_write_set(&writeset);
                        }
                    }
                    Err(err) => {
                        writeln!(stderr().lock(), "{}", err)?;
                        bail!("Unexpected failure in Move effect committing");
                    }
                };
            }
            Err(err) => {
                writeln!(stderr().lock(), "{}", err)?;
                bail!("Unexpected failure in Move execution");
            }
        }

        // done
        Ok(())
    }
}
