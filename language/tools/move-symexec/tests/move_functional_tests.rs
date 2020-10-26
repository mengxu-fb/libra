// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use anyhow::{bail, Result};
use once_cell::sync::Lazy;
use std::{
    collections::HashMap,
    convert::TryFrom,
    io::Write,
    path::{Path, PathBuf},
};
use tempfile::NamedTempFile;

use compiled_stdlib::transaction_scripts::StdlibScript;
use datatest_stable::{self, harness};
use functional_tests::{
    compiler::{Compiler, ScriptOrModule},
    testsuite,
};
use libra_types::{
    account_address::AccountAddress,
    transaction::{SignedTransaction, TransactionPayload, WriteSetPayload},
};
use move_lang::shared::Address;

use move_symexec::{
    configs::{
        MOVE_BIN_EXT, MOVE_LIBNURSERY, MOVE_LIBSYMEXEC, MOVE_STDLIB_BIN_MODULES,
        MOVE_STDLIB_BIN_SCRIPTS,
    },
    controller::MoveController,
    join_path_items,
    sym_vm_types::SymTransactionArgument,
};

/// Path to the directory of move-lang functional testsuites
static MOVE_FUNCTIONAL_TESTS: Lazy<String> = Lazy::new(|| {
    join_path_items!(
        env!("CARGO_MANIFEST_DIR"),
        "..",
        "..",
        "move-lang",
        "functional-tests",
        "tests"
    )
});

/// Path to the testing workspace
static MOVE_FUNCTIONAL_TESTS_WORKDIR: Lazy<String> = Lazy::new(|| {
    join_path_items!(
        env!("CARGO_MANIFEST_DIR"),
        "tests",
        "workspace",
        "move-functional-tests"
    )
});

/// An error mark that the test validator expects
const MOVE_COMPILER_ERROR_MARK: &str = "MoveSourceCompilerError";

/// Piggyback on the test-infra to run tests
struct MoveFunctionalTestCompiler<'a> {
    controller: &'a mut MoveController,
    stdlib_scripts: HashMap<String, StdlibScript>,
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
        let tmp_path = tmp_file.path().to_str().unwrap();

        // parse sender address
        let sender = Address::try_from(address.as_ref()).unwrap();

        // compile in a separate session
        self.controller.push()?;

        if self
            .controller
            .compile(&[tmp_path.to_owned()], Some(sender), true, true)
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
            Ok(ScriptOrModule::Module(modules.pop().unwrap()))
        } else {
            if scripts.len() != 1 {
                bail!(
                    "Expecting only one compilation unit, got {} module(s) and {} script(s)",
                    modules.len(),
                    scripts.len()
                );
            }
            Ok(ScriptOrModule::Script(scripts.pop().unwrap()))
        }
    }

    fn use_compiled_genesis(&self) -> bool {
        false
    }

    fn hook_notify_precompiled_script(&mut self, input: &str) -> Result<()> {
        // find the script path
        let script_name = input.strip_prefix("stdlib_script::").unwrap();
        let mut script_path = PathBuf::from(MOVE_STDLIB_BIN_SCRIPTS.to_owned());
        script_path.push(format!(
            "{}.{}",
            self.stdlib_scripts.get(script_name).unwrap(),
            MOVE_BIN_EXT
        ));

        // load in a separate session
        self.controller.push()?;

        // load the script
        self.controller.load(
            &[script_path.into_os_string().into_string().unwrap()],
            true,
            true,
            true,
        )
    }

    fn hook_pre_exec_script_txn(&mut self, txn: &SignedTransaction) -> Result<()> {
        // derive signers and symbolic value arguments
        let (signers, val_args) = match txn.payload() {
            TransactionPayload::Script(script) => (vec![txn.sender()], script.args()),
            TransactionPayload::WriteSet(writeset) => match writeset {
                WriteSetPayload::Script { execute_as, script } => {
                    (vec![txn.sender(), *execute_as], script.args())
                }
                WriteSetPayload::Direct(_) => {
                    panic!("Expect a script in transaction");
                }
            },
            TransactionPayload::Module(_) => {
                panic!("Expect a script in transaction");
            }
        };
        let sym_val_args: Vec<SymTransactionArgument> = val_args
            .iter()
            .map(|arg| SymTransactionArgument::Concrete(arg.clone()))
            .collect();

        // symbolize it
        self.controller
            .symbolize(&signers, &sym_val_args, None, Some(&[]), false, true, true)
    }
}

fn run_one_test(test_path: &Path) -> datatest_stable::Result<()> {
    let test_name = test_path
        .strip_prefix(&*MOVE_FUNCTIONAL_TESTS)?
        .with_extension("");

    let test_workdir = join_path_items!(&*MOVE_FUNCTIONAL_TESTS_WORKDIR, &test_name);

    // setup the compiler
    let mut controller = MoveController::new(test_workdir, false)?;

    // preload libraries, stdlib will be tracked
    controller.load(&[MOVE_STDLIB_BIN_MODULES.to_owned()], false, true, true)?;
    controller.compile(&[MOVE_LIBNURSERY.to_owned()], None, false, true)?;
    controller.compile(&[MOVE_LIBSYMEXEC.to_owned()], None, false, true)?;

    // test
    testsuite::functional_tests(
        MoveFunctionalTestCompiler {
            controller: &mut controller,
            stdlib_scripts: StdlibScript::all()
                .into_iter()
                .map(|script| (script.name(), script))
                .collect(),
        },
        test_path,
    )
}

// runs all the tests
harness!(run_one_test, *MOVE_FUNCTIONAL_TESTS, r".*\.move$");
