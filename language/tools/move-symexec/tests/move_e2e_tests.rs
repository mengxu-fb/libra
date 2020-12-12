// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::anyhow;
use datatest_stable::{self, harness};
use once_cell::sync::Lazy;
use std::{
    collections::{HashMap, HashSet},
    fs::{self, File},
    io::BufReader,
    path::{Path, PathBuf},
};

use compiled_stdlib::transaction_scripts::StdlibScript;
use language_e2e_tests::executor::ExecStepInfo;
use move_lang::{shared::Address, MOVE_EXTENSION};

use move_symexec::{
    configs::{MOVE_DIEM_SCRIPTS, MOVE_LIBNURSERY, MOVE_STDLIB_MODULES},
    controller::MoveController,
    crate_path, crate_path_string,
    sym_vm_types::SymTransactionArgument,
};

static STDLIB_SCRIPT_HASHMAP: Lazy<HashMap<String, String>> = Lazy::new(|| {
    StdlibScript::all()
        .into_iter()
        .map(|script| (script.hash().to_hex(), script.name()))
        .collect()
});

// Path to the directory of micro tests functional testsuites
crate_path_string!(MOVE_E2E_TESTS_SCRIPT, "tests", "move-e2e-tests");

// Path to the testing workspace
crate_path!(
    MOVE_E2E_TESTS_WORKDIR,
    "tests",
    "workspace",
    "move-e2e-tests"
);

/// A list of tests that we do not want to run
static TEST_BLACKLIST: Lazy<HashSet<String>> = Lazy::new(|| {
    vec!["language_e2e_testsuite::tests::vasps::max_child_accounts_for_vasp"]
        .into_iter()
        .map(|item| item.to_owned())
        .collect()
});

fn run_one_test(test_path: &Path) -> datatest_stable::Result<()> {
    let dir_path = test_path.parent().unwrap();

    // read test name
    let test_name = fs::read_to_string(dir_path.join("name"))?;
    if TEST_BLACKLIST.contains(&test_name) {
        println!("Test case ignored: {}", test_name);
        return Ok(());
    }

    // derive workdir
    let test_workdir = MOVE_E2E_TESTS_WORKDIR.join(&test_name);
    if test_workdir.exists() {
        fs::remove_dir_all(&test_workdir)
            .map_err(|e| anyhow!("Failed to clean up workdir {:?}: {:?}", test_workdir, e))?;
    }

    // setup the compiler
    let mut controller = MoveController::new(test_workdir)?;

    // compile stdlib (including nursery)
    controller.compile(&[&*MOVE_STDLIB_MODULES], Some(Address::DIEM_CORE), true)?;
    controller.compile(&[&*MOVE_LIBNURSERY], Some(Address::DIEM_CORE), true)?;

    // follow along the tests
    let num = fs::read_dir(&dir_path)?.count();
    for seq in 1..num {
        let step_path = dir_path.join(seq.to_string());
        let step_file = File::open(step_path)?;
        let reader = BufReader::new(step_file);
        let step_info: ExecStepInfo = serde_json::from_reader(reader)?;

        match step_info {
            ExecStepInfo::WriteSet => {}
            ExecStepInfo::Module { .. } => {
                // TODO: there is nothing much we can do as the module is written in IR
                // shortcut the test and call it successful
                println!(
                    "Test case short-circuited due to module compilation: {}",
                    test_name
                );
                return Ok(());
            }
            ExecStepInfo::Script {
                hval,
                signers,
                ty_args,
                val_args,
            } => {
                // check whether this script belongs to stdlib
                let script_item = STDLIB_SCRIPT_HASHMAP.get(&hval);
                if script_item.is_none() {
                    // TODO: there is nothing much we can do as the script is written in IR
                    // shortcut the test and call it successful
                    println!(
                        "Test case short-circuited due to script compilation: {}",
                        test_name
                    );
                    return Ok(());
                }
                let script_name = script_item.unwrap();

                // compile the script
                let script_path = MOVE_DIEM_SCRIPTS
                    .join(script_name)
                    .with_extension(MOVE_EXTENSION);
                controller.push()?;
                controller.compile(&[&script_path], Some(Address::DIEM_CORE), true)?;

                // pre-mark all args as symbolic
                let sym_args = (0..val_args.len())
                    .map(|i| SymTransactionArgument::Symbolic(format!("v{}", i)))
                    .collect::<Vec<_>>();

                // symbolize it
                controller.symbolize(
                    &signers,
                    &sym_args,
                    &ty_args,
                    None,
                    &[],
                    false,
                    true,
                    true,
                    true,
                    true,  // TODO: disable no-run when development is done
                    false, // TODO: enable strict mode when development is done
                )?;

                // now pop the stack to remove the script
                controller.pop()?;
            }
        }
    }

    Ok(())
}

// runs all the tests
harness!(run_one_test, *MOVE_E2E_TESTS_SCRIPT, r".*/name$");
