// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use std::{io::Write, path::Path, process::Command, str};
use tempfile::NamedTempFile;

use functional_tests::{
    compiler::{Compiler, ScriptOrModule},
    testsuite,
};
use libra_types::account_address::AccountAddress;
use move_symexec::{utils, MOVE_SYMEXEC_BIN_NAME};

/// Path to the directory of move-lang functional testsuites
const MOVE_FUNCTIONAL_TESTS: [&str; 7] = [
    env!("CARGO_MANIFEST_DIR"),
    "..",
    "..",
    "..",
    "move-lang",
    "functional-tests",
    "tests",
];

/// Path to the testing workspace
const MOVE_FUNCTIONAL_TESTS_WORKDIR: [&str; 2] = [env!("CARGO_MANIFEST_DIR"), "tests"];

/// Path to the move-symexec crate
const MOVE_SYMEXEC_PKG_PATH: [&str; 3] = [env!("CARGO_MANIFEST_DIR"), "..", "Cargo.toml"];

/// Name of the default config file
const DEFAULT_SYM_CONFIG_FILE: &str = "sym-default.json";

/// Piggyback on the test-infra to run tests
struct SymExecCompiler<'a, 'b> {
    workdir: &'a str,
    manifest: &'a str,
    test_name: &'b str,
    config_file: &'b str,
}

impl<'a, 'b> SymExecCompiler<'a, 'b> {
    fn new(workdir: &'a str, manifest: &'a str, test_name: &'b str, config_file: &'b str) -> Self {
        Self {
            workdir,
            manifest,
            test_name,
            config_file,
        }
    }
}

impl Compiler for SymExecCompiler<'_, '_> {
    fn compile<Logger: FnMut(String)>(
        &mut self,
        _log: Logger,
        _address: AccountAddress,
        input: &str,
    ) -> Result<ScriptOrModule> {
        // save content to a file first
        let src_file = NamedTempFile::new()?;
        src_file.reopen()?.write_all(input.as_bytes())?;
        let src_file_path = src_file.path().to_str().unwrap();

        // run the symbolic executor
        let output = Command::new("Cargo")
            .current_dir(self.workdir)
            .arg("run")
            .arg("--manifest-path")
            .arg(self.manifest)
            .arg("--bin")
            .arg(MOVE_SYMEXEC_BIN_NAME)
            .arg("--")
            .arg("run")
            .arg("-S")
            .arg("-s")
            .arg(src_file_path)
            .arg("--track-stdlib")
            .arg("-c")
            .arg(self.config_file)
            .arg("-v")
            .output()?;

        // show errors and bail
        if !output.status.success() {
            println!("{}", input);
            println!("{:-<80}", "");
            println!("{}", str::from_utf8(&output.stdout)?);
            println!("{:-<80}", "");
            println!("{}", str::from_utf8(&output.stderr)?);
            println!("{:-<80}", "");
            bail!("Error: symbolic execution on the test case failed");
        } else {
            println!("Test case finished: {}", self.test_name);
        }

        // still compile it normally
        bail!("Error: cannot do much");
    }

    fn use_compiled_genesis(&self) -> bool {
        false
    }
}

#[test]
#[ignore]
fn run_functional_tests() -> Result<()> {
    let manifest_path_str = utils::path_components_to_string(&MOVE_SYMEXEC_PKG_PATH);
    let workdir_path_str = utils::path_components_to_string(&MOVE_FUNCTIONAL_TESTS_WORKDIR);
    let workdir_path = Path::new(&workdir_path_str);

    // derive default config
    let default_config_path_str = workdir_path
        .join(DEFAULT_SYM_CONFIG_FILE)
        .into_os_string()
        .into_string()
        .unwrap();

    // find all test cases
    let tests_path_str = utils::path_components_to_string(&MOVE_FUNCTIONAL_TESTS);
    let tests_path = Path::new(&tests_path_str);

    for test_src_str in move_lang::find_move_filenames(&[tests_path_str.clone()], false)? {
        let test_src_path = Path::new(&test_src_str);
        let test_src_rel = test_src_path.strip_prefix(tests_path)?;

        // derive customized config file path (if it exists)
        let test_config_rel = test_src_rel.with_extension("json");
        let test_config_path = workdir_path.join(test_config_rel);

        // check whether the config file exists
        let test_config_path_str = if test_config_path.exists() {
            test_config_path.to_str().unwrap()
        } else {
            &default_config_path_str
        };

        // invoke the test suite utility
        testsuite::functional_tests(
            SymExecCompiler::new(
                &workdir_path_str,
                &manifest_path_str,
                test_src_rel.to_str().unwrap(),
                test_config_path_str,
            ),
            test_src_path,
        )
        .unwrap();
    }

    // done
    Ok(())
}
