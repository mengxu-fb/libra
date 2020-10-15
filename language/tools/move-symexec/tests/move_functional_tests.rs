// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use anyhow::{bail, Result};
use once_cell::sync::Lazy;
use std::{convert::TryFrom, io::Write, path::Path};
use tempfile::NamedTempFile;

use datatest_stable::{self, harness};
use functional_tests::{
    compiler::{Compiler, ScriptOrModule},
    testsuite,
};
use libra_types::account_address::AccountAddress;
use move_lang::shared::Address;

use move_symexec::{
    configs::{MOVE_LIBNURSERY, MOVE_LIBSYMEXEC, MOVE_STDLIB_BIN},
    controller::MoveController,
    join_path_items,
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

        // get the compiled units before symbolization
        let (mut modules, mut scripts) = self.controller.get_compiled_units_recent(None);

        // symbolize
        self.controller.symbolize(None, Some(&[]))?;

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
}

fn run_one_test(test_path: &Path) -> datatest_stable::Result<()> {
    let test_name = test_path
        .strip_prefix(&*MOVE_FUNCTIONAL_TESTS)?
        .with_extension("");

    let test_workdir = join_path_items!(&*MOVE_FUNCTIONAL_TESTS_WORKDIR, &test_name);

    // setup the compiler
    let mut controller = MoveController::new(test_workdir, true)?;

    // preload libraries, stdlib will be tracked
    controller.load(&[MOVE_STDLIB_BIN.to_owned()], true, true)?;
    controller.compile(&[MOVE_LIBNURSERY.to_owned()], None, false, true)?;
    controller.compile(&[MOVE_LIBSYMEXEC.to_owned()], None, false, true)?;

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
