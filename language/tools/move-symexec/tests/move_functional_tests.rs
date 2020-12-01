// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, bail, Result};
use once_cell::sync::Lazy;
use std::{
    collections::HashSet,
    convert::TryFrom,
    fs::{self, File},
    io::{Seek, SeekFrom, Write},
    path::{Path, PathBuf},
};

use datatest_stable::{self, harness};
use functional_tests::{
    compiler::{Compiler, ScriptOrModule},
    testsuite,
};
use libra_types::{
    account_address::AccountAddress,
    transaction::{SignedTransaction, TransactionPayload, WriteSetPayload},
};
use move_lang::{move_compile, shared::Address, MOVE_EXTENSION};

use move_symexec::{
    configs::{MOVE_LIBNURSERY, MOVE_LIBRA_SCRIPTS, MOVE_STDLIB_MODULES},
    controller::MoveController,
    crate_path, crate_path_string,
    sym_vm_types::SymTransactionArgument,
    utils::PathToString,
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

/// Default directory where the generated source code file live
const DEFAULT_SOURCE_LOC: &str = "sources";

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
    source_loc: PathBuf,
    source_num: usize,
}

impl Compiler for MoveFunctionalTestCompiler<'_> {
    fn compile<Logger: FnMut(String)>(
        &mut self,
        _log: Logger,
        address: AccountAddress,
        input: &str,
    ) -> Result<ScriptOrModule> {
        // save content to a file first
        let src_file_path = self
            .source_loc
            .join(self.source_num.to_string())
            .with_extension(MOVE_EXTENSION);
        let mut fp = File::create(&src_file_path)?;
        self.source_num += 1;
        fp.write_all(input.as_bytes())?;

        // parse sender address
        let sender = Address::try_from(address.as_ref()).unwrap();

        // save the compilation dependencies first
        let deps = self
            .controller
            .get_compilation_interfaces()
            .into_iter()
            .map(|path| path.path_to_string())
            .collect::<Result<Vec<_>>>()?;

        // compile in a separate session
        self.controller.push()?;
        if self
            .controller
            .compile(&[&src_file_path], Some(sender), true)
            .is_err()
        {
            bail!(MOVE_COMPILER_ERROR_MARK);
        }

        // get the compiled units
        let (mut modules, mut scripts) = self.controller.get_compiled_units_recent();

        // return results
        if !modules.is_empty() {
            if !scripts.is_empty() || modules.len() != 1 {
                bail!(
                    "Expecting only one compilation unit, got {} module(s) and {} script(s)",
                    modules.len(),
                    scripts.len()
                );
            }

            // NOTE: for compiled modules, we force the sender address to be added to the source.
            // But occasionally, the original source code already has the address info, so we do a
            // compilation on the original source file --- with None as sender_opt --- and see
            // whether it returns with error. If an error is encountered, we further modify the
            // source file by manually adding the `address _ {}` wrap around the original source.
            let (_, result) = move_compile(&[src_file_path.path_to_string()?], &deps, None, None)?;
            if result.is_err() {
                fp.seek(SeekFrom::Start(0))?;
                fp.write_all(
                    format!("address 0x{} {{\n", address.short_str_lossless()).as_bytes(),
                )?;
                fp.write_all(input.as_bytes())?;
                fp.write_all(b"\n}")?;

                // second trial
                let (_, result) =
                    move_compile(&[src_file_path.path_to_string()?], &deps, None, None)?;
                debug_assert!(result.is_ok());
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
        let script_path = MOVE_LIBRA_SCRIPTS
            .join(script_name)
            .with_extension(MOVE_EXTENSION);

        // compile the script in a separate session
        self.controller.push()?;
        self.controller
            .compile(&[&script_path], Some(Address::LIBRA_CORE), true)
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
            .symbolize(&signers, &sym_args, &type_tags, None, &[], true, true)?;

        // now pop the stack to remove the script
        self.controller.pop()
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
    if test_workdir.exists() {
        fs::remove_dir_all(&test_workdir)
            .map_err(|e| anyhow!("Failed to clean up workdir {:?}: {:?}", test_workdir, e))?;
    }
    let source_loc = test_workdir.join(DEFAULT_SOURCE_LOC);
    fs::create_dir_all(&source_loc)?;

    // setup the compiler
    let mut controller = MoveController::new(test_workdir)?;

    // compile stdlib (including nursery)
    controller.compile(&[&*MOVE_STDLIB_MODULES], Some(Address::LIBRA_CORE), true)?;
    controller.compile(&[&*MOVE_LIBNURSERY], Some(Address::LIBRA_CORE), true)?;

    // test
    testsuite::functional_tests(
        MoveFunctionalTestCompiler {
            controller: &mut controller,
            source_loc,
            source_num: 0,
        },
        test_path,
    )
}

// runs all the tests
harness!(run_one_test, *MOVE_FUNCTIONAL_TESTS, r".*\.move$");
