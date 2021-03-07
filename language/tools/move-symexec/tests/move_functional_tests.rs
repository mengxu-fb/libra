// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, bail, Result};
use datatest_stable::{self, harness};
use once_cell::sync::Lazy;
use std::{
    convert::TryFrom,
    error, fmt,
    fs::{self, File},
    io::{Seek, SeekFrom, Write},
    path::{Path, PathBuf},
};
use tempfile::{tempdir, NamedTempFile};

use diem_types::{
    account_address::AccountAddress,
    transaction::{SignedTransaction, TransactionPayload, WriteSetPayload},
};
use functional_tests::{
    compiler::{Compiler, ScriptOrModule},
    testsuite,
};
use move_lang::{errors::report_errors_to_buffer, move_compile, shared::Address, MOVE_EXTENSION};

use move_symexec::{
    configs::{use_workspace, MOVE_DIEM_SCRIPTS, MOVE_LIBNURSERY, MOVE_STDLIB_MODULES},
    controller::MoveController,
    crate_path, crate_path_string,
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

#[derive(Debug)]
struct MoveSourceCompilerError(pub String);

impl fmt::Display for MoveSourceCompilerError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "\n\n{}", self.0)
    }
}

impl error::Error for MoveSourceCompilerError {}

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
        // get deps
        let deps = self.controller.get_compilation_dependencies()?;

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

        // compile in a separate session
        self.controller.push(true, false, false)?;
        if self
            .controller
            .compile(&[&src_file_path], Some(sender), true)
            .is_err()
        {
            // if there is a compilation error, simulate what the actual compiler will do
            let tmp_file = NamedTempFile::new()?;
            tmp_file.reopen()?.write_all(input.as_bytes())?;
            let tmp_path = tmp_file.path().path_to_string()?;

            let (files, units_or_errors) =
                move_compile(&[tmp_path], &deps, Some(sender), None, true)?;
            match units_or_errors {
                Ok(_) => bail!("Expect failure in compilation but no errors reported"),
                Err(errors) => {
                    let error_buffer = report_errors_to_buffer(files, errors);
                    return Err(
                        MoveSourceCompilerError(String::from_utf8(error_buffer).unwrap()).into(),
                    );
                }
            }
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
            let (_, result) =
                move_compile(&[src_file_path.path_to_string()?], &deps, None, None, true)?;
            if result.is_err() {
                fp.seek(SeekFrom::Start(0))?;
                fp.write_all(
                    format!("address 0x{} {{\n", address.short_str_lossless()).as_bytes(),
                )?;
                fp.write_all(input.as_bytes())?;
                fp.write_all(b"\n}")?;

                // second trial
                let (_, result) =
                    move_compile(&[src_file_path.path_to_string()?], &deps, None, None, true)?;
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
        let script_path = MOVE_DIEM_SCRIPTS
            .join(script_name)
            .with_extension(MOVE_EXTENSION);

        // compile the script in a separate session
        self.controller.push(true, false, false)?;
        self.controller
            .compile(&[&script_path], Some(Address::DIEM_CORE), true)
    }

    fn hook_pre_exec_script_txn(&mut self, txn: &SignedTransaction) -> Result<()> {
        // derive signers and symbolic value arguments
        let (_signers, _val_args, type_tags) = match txn.payload() {
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

        // symbolize it
        self.controller.symbolize(type_tags)?;

        // now pop the stack to remove the script
        self.controller.pop(true, false, false)
    }
}

fn run_one_test(test_path: &Path) -> datatest_stable::Result<()> {
    let test_name = test_path
        .strip_prefix(&*MOVE_FUNCTIONAL_TESTS)?
        .with_extension("");

    // derive workdir
    let tmp_wks = if use_workspace() {
        None
    } else {
        Some(tempdir()?)
    };

    let test_workdir = tmp_wks.as_ref().map_or_else(
        || MOVE_FUNCTIONAL_TESTS_WORKDIR.join(&test_name),
        |t| t.path().to_owned(),
    );
    if tmp_wks.is_none() && test_workdir.exists() {
        fs::remove_dir_all(&test_workdir)
            .map_err(|e| anyhow!("Failed to clean up workdir {:?}: {:?}", test_workdir, e))?;
    }
    let source_loc = test_workdir.join(DEFAULT_SOURCE_LOC);
    fs::create_dir_all(&source_loc)?;

    // setup the compiler
    let mut controller = MoveController::new(test_workdir)?;

    // compile stdlib (including nursery)
    controller.compile(&[&*MOVE_STDLIB_MODULES], Some(Address::DIEM_CORE), true)?;
    controller.compile(&[&*MOVE_LIBNURSERY], Some(Address::DIEM_CORE), true)?;

    // test
    testsuite::functional_tests(
        MoveFunctionalTestCompiler {
            controller: &mut controller,
            source_loc,
            source_num: 0,
        },
        test_path,
    )?;

    // clean up (if needed)
    if let Some(t) = tmp_wks {
        t.close()?;
    }
    Ok(())
}

// runs all the tests
harness!(run_one_test, *MOVE_FUNCTIONAL_TESTS, r".*\.move$");
