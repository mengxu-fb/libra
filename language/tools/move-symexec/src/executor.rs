// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use anyhow::{bail, Result};
use log::debug;
use std::{
    collections::HashMap,
    io::{stderr, Write},
};

use language_e2e_tests::data_store::FakeDataStore;
use libra_vm::txn_effects_to_writeset_and_events;
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

/// A stateful executor (backed by the FakeDataStore) that can execute
/// Move programs, consisting of a sequence of Move scripts, in steps
#[derive(Clone, Debug)]
pub(crate) struct MoveExecutor {
    data_store: FakeDataStore,
}

impl MoveExecutor {
    pub fn new(modules: &[CompiledModule]) -> Self {
        let mut data_store = FakeDataStore::new(HashMap::new());
        for module in modules {
            data_store.add_module(&module.self_id(), &module);
        }
        Self { data_store }
    }

    pub fn preload_modules(&mut self, modules: &[CompiledModule]) {
        for module in modules {
            self.data_store.add_module(&module.self_id(), &module);
        }
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
        let exec_args: Vec<Value> = val_args
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
            writeln!(stderr().lock(), "{}", err)?;
            bail!("Unexpected failure in Move execution");
        };

        // collect effects
        match session.finish() {
            Ok(effects) => {
                debug!(
                    "Script executed - modules: {}, resources: {}, events: {}",
                    effects.modules.len(),
                    effects.resources.len(),
                    effects.events.len(),
                );

                // effects are discarded and not commited to states
                match txn_effects_to_writeset_and_events(effects) {
                    Ok((writeset, _events)) => {
                        if commit {
                            self.data_store.add_write_set(&writeset);
                        }
                    }
                    Err(err) => {
                        writeln!(stderr().lock(), "{}", err)?;
                        bail!("Unexpected failure in Move execution");
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
