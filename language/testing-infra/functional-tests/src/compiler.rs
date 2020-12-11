// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use diem_types::{account_address::AccountAddress, transaction::SignedTransaction};
use vm::file_format::{CompiledModule, CompiledScript};

pub trait Compiler {
    /// Compile a transaction script or module.
    fn compile<Logger: FnMut(String)>(
        &mut self,
        log: Logger,
        address: AccountAddress,
        input: &str,
    ) -> Result<ScriptOrModule>;

    fn use_compiled_genesis(&self) -> bool;

    /// A hook to notify a pre-compiled script is used
    fn hook_notify_precompiled_script(&mut self, _input: &str) -> Result<()> {
        Ok(())
    }

    /// A hook before executing a script transaction
    fn hook_pre_exec_script_txn(&mut self, _txn: &SignedTransaction) -> Result<()> {
        Ok(())
    }

    /// A hook before executing a module transaction
    fn hook_pre_exec_module_txn(&mut self, _txn: &SignedTransaction) -> Result<()> {
        Ok(())
    }
}

pub enum ScriptOrModule {
    Script(CompiledScript),
    Module(CompiledModule),
}
