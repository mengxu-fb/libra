// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use once_cell::sync::Lazy;
use std::{
    collections::HashSet,
    convert::TryFrom,
    io::Write,
    path::{Path, PathBuf},
};
use tempfile::NamedTempFile;

use datatest_stable::{self, harness};
use functional_tests::{
    compiler::{Compiler, ScriptOrModule},
    testsuite,
};
use libra_types::{
    account_address::AccountAddress,
    transaction::{SignedTransaction, TransactionPayload, WriteSetPayload},
};
use move_lang::{shared::Address, MOVE_COMPILED_EXTENSION};

use move_symexec::{
    configs::{MOVE_LIBNURSERY, MOVE_LIBRA_BIN_SCRIPTS, MOVE_LIBSYMEXEC, MOVE_STDLIB_BIN_MODULES},
    controller::MoveController,
    crate_path, crate_path_string,
    sym_vm_types::SymTransactionArgument,
};

// Path to the directory of move-lang functional testsuites
crate_path_string!(
    MOVE_FUNCTIONAL_TESTS,
    "..",
    "..",
    "move-lang",
    "functional-tests",
    "tests"
);

// Path to the testing workspace
crate_path!(
    MOVE_FUNCTIONAL_TESTS_WORKDIR,
    "tests",
    "workspace",
    "move-functional-tests"
);

/// An error mark that the test validator expects
const MOVE_COMPILER_ERROR_MARK: &str = "MoveSourceCompilerError";

/// A blacklist of tests that we do not want to run
static TEST_BLACKLIST: Lazy<HashSet<PathBuf>> = Lazy::new(|| {
    vec![
        // this test has intentional signer - value argument mismatch
        ["move", "signer", "address_arg_is_not_signer"]
            .iter()
            .collect(),
    ]
    .into_iter()
    .collect()
});

/// Piggyback on the test-infra to run tests
struct MoveFunctionalTestCompiler<'a> {
    controller: &'a mut MoveController,
}

impl Compiler for MoveFunctionalTestCompiler<'_> {
    fn compile<Logger: FnMut(String)>(
        &mut self,
        _log: Logger,
        address: AccountAddress,
        input: &str,
    ) -> Result<ScriptOrModule> {
        // save content to a file first
        let tmp_file = NamedTempFile::new()?;
        tmp_file.reopen()?.write_all(input.as_bytes())?;

        // parse sender address
        let sender = Address::try_from(address.as_ref()).unwrap();

        // compile in a separate session
        self.controller.push()?;

        if self
            .controller
            .compile(&[tmp_file.path()], Some(sender), true, true)
            .is_err()
        {
            bail!(MOVE_COMPILER_ERROR_MARK);
        }

        // get the compiled units
        let (mut modules, mut scripts) = self.controller.get_compiled_units_recent(None);

        // return results
        if !modules.is_empty() {
            if !scripts.is_empty() || modules.len() != 1 {
                bail!(
                    "Expecting only one compilation unit, got {} module(s) and {} script(s)",
                    modules.len(),
                    scripts.len()
                );
            }
            Ok(ScriptOrModule::Module(modules.pop().unwrap().clone()))
        } else {
            if scripts.len() != 1 {
                bail!(
                    "Expecting only one compilation unit, got {} module(s) and {} script(s)",
                    modules.len(),
                    scripts.len()
                );
            }
            Ok(ScriptOrModule::Script(scripts.pop().unwrap().clone()))
        }
    }

    fn use_compiled_genesis(&self) -> bool {
        false
    }

    fn hook_notify_precompiled_script(&mut self, input: &str) -> Result<()> {
        // find the script path
        let script_name = input.strip_prefix("stdlib_script::").unwrap();
        let script_path = MOVE_LIBRA_BIN_SCRIPTS
            .join(script_name)
            .with_extension(MOVE_COMPILED_EXTENSION);

        // load the script in a separate session
        self.controller.push()?;
        self.controller.load(&[&script_path], true, true, true)
    }

    fn hook_pre_exec_script_txn(&mut self, txn: &SignedTransaction) -> Result<()> {
        // derive signers and symbolic value arguments
        let (signers, val_args, type_tags) = match txn.payload() {
            TransactionPayload::Script(script) => {
                (vec![txn.sender()], script.args(), script.ty_args())
            }
            TransactionPayload::WriteSet(writeset) => match writeset {
                WriteSetPayload::Script { execute_as, script } => (
                    vec![txn.sender(), *execute_as],
                    script.args(),
                    script.ty_args(),
                ),
                WriteSetPayload::Direct(_) => {
                    panic!("Expect a script in transaction");
                }
            },
            TransactionPayload::Module(_) => {
                panic!("Expect a script in transaction");
            }
        };
        let sym_args: Vec<SymTransactionArgument> = val_args
            .iter()
            .map(|arg| SymTransactionArgument::Concrete(arg.clone()))
            .collect();

        // symbolize it
        self.controller
            .symbolize(&signers, &sym_args, &type_tags, None, &[], true, true, true)
    }
}

fn run_one_test(test_path: &Path) -> datatest_stable::Result<()> {
    let test_name = test_path
        .strip_prefix(&*MOVE_FUNCTIONAL_TESTS)?
        .with_extension("");

    // filter ignored test cases
    if TEST_BLACKLIST.contains(&test_name) {
        println!("Test case ignored: {:?}", test_name);
        return Ok(());
    }

    // derive workdir
    let test_workdir = MOVE_FUNCTIONAL_TESTS_WORKDIR.join(&test_name);

    // setup the compiler
    let mut controller = MoveController::new(test_workdir)?;

    // preload libraries, stdlib will be tracked
    controller.load(&[&*MOVE_STDLIB_BIN_MODULES], false, true, true)?;
    controller.compile(&[&*MOVE_LIBNURSERY], None, true, true)?;
    controller.compile(&[&*MOVE_LIBSYMEXEC], None, false, true)?;

    // test
    testsuite::functional_tests(
        MoveFunctionalTestCompiler {
            controller: &mut controller,
        },
        test_path,
    )
}

// runs all the tests
harness!(run_one_test, *MOVE_FUNCTIONAL_TESTS, r".*\.move$");
