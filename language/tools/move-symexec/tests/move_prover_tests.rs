// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::anyhow;
use datatest_stable::{self, harness};
use once_cell::sync::Lazy;
use std::{
    fs,
    path::{Path, PathBuf},
};
use tempfile::tempdir;

use move_lang::shared::Address;
use move_prover::cli::Options;
use move_prover_test_utils::extract_test_directives;

use move_symexec::{
    configs::{use_workspace, MOVE_LIBNURSERY, MOVE_STDLIB_MODULES},
    controller::MoveController,
    crate_path, crate_path_string,
};

// Path to the testing workspace
crate_path!(MOVE_PROVER_CRATE, "..", "..", "move-prover");

// Path to the directory of move-prover testsuites
crate_path_string!(MOVE_PROVER_TESTS, "..", "..", "move-prover", "tests");

// Path to the testing workspace
crate_path!(
    MOVE_PROVER_TESTS_WORKDIR,
    "tests",
    "workspace",
    "move-prover-tests"
);

fn run_one_test(test_path: &Path) -> datatest_stable::Result<()> {
    let test_name = test_path
        .strip_prefix(&*MOVE_PROVER_TESTS)?
        .with_extension("");

    // derive workdir
    let tmp_wks = if use_workspace() {
        None
    } else {
        Some(tempdir()?)
    };

    let test_workdir = tmp_wks.as_ref().map_or_else(
        || MOVE_PROVER_TESTS_WORKDIR.join(&test_name),
        |t| t.path().to_owned(),
    );
    if tmp_wks.is_none() && test_workdir.exists() {
        fs::remove_dir_all(&test_workdir)
            .map_err(|e| anyhow!("Failed to clean up workdir {:?}: {:?}", test_workdir, e))?;
    }

    // parse the options
    let mut args = vec!["mvp_test".to_owned()];
    let flags = extract_test_directives(test_path, "// flag:")?;
    args.extend(flags);
    let options = Options::create_from_args(&args)?;

    // setup the compiler
    let mut controller = MoveController::new(test_workdir)?;

    // compile stdlib (including nursery)
    controller.compile(&[&*MOVE_STDLIB_MODULES], Some(Address::DIEM_CORE), true)?;
    controller.compile(&[&*MOVE_LIBNURSERY], Some(Address::DIEM_CORE), true)?;

    // compile dependencies
    if !options.move_deps.is_empty() {
        let deps: Vec<_> = options
            .move_deps
            .iter()
            .map(|p| MOVE_PROVER_CRATE.join(p))
            .collect();
        controller.compile(
            &deps,
            Some(Address::parse_str(&options.account_address)?),
            true,
        )?;
    }

    // compile the test case
    controller.compile(
        &[test_path],
        Some(Address::parse_str(&options.account_address)?),
        true,
    )?;

    // clean up (if needed)
    if let Some(t) = tmp_wks {
        t.close()?;
    }
    Ok(())
}

// runs all the tests
harness!(run_one_test, *MOVE_PROVER_TESTS, r".*\.move$");
