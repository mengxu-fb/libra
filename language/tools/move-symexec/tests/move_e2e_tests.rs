// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::anyhow;
use datatest_stable::{self, harness};
use once_cell::sync::Lazy;
use std::{
    collections::HashMap,
    fs::{self, File},
    io::BufReader,
    path::{Path, PathBuf},
};

use compiled_stdlib::transaction_scripts::StdlibScript;
use language_e2e_tests::account::ScriptMainInfo;
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
crate_path_string!(MOVE_E2E_TESTS_SCRIPT, "tests", "move-e2e-tests", "script");

// Path to the testing workspace
crate_path!(
    MOVE_E2E_TESTS_WORKDIR,
    "tests",
    "workspace",
    "move-e2e-tests"
);

fn run_one_test(test_path: &Path) -> datatest_stable::Result<()> {
    let dir_path = test_path.parent().unwrap();
    let script_hash = dir_path.file_name().unwrap().to_str().unwrap();
    let script_item = STDLIB_SCRIPT_HASHMAP.get(script_hash);
    if script_item.is_none() {
        // TODO: if we do not have a hash, this might be a newly compiled script
        return Ok(());
    }
    let script_name = script_item.unwrap();

    // collect the list of type instantiations
    let mut script_info = HashMap::new();
    for item in fs::read_dir(&dir_path)? {
        let item = item?;
        let file = File::open(item.path())?;
        let reader = BufReader::new(file);
        let script_main: ScriptMainInfo = serde_json::from_reader(reader)?;

        // skip processing if we already have a version of this instantiation
        if script_info.contains_key(&script_main.ty_args) {
            continue;
        }

        // pre-mark all args as symbolic
        let sym_args = (0..script_main.args.len())
            .map(|i| SymTransactionArgument::Symbolic(format!("v{}", i)))
            .collect::<Vec<_>>();

        script_info
            .entry(script_main.ty_args)
            .or_insert_with(HashMap::new)
            .insert(script_main.signers, sym_args);
    }

    // derive workdir
    let test_workdir = MOVE_E2E_TESTS_WORKDIR.join(script_name);
    if test_workdir.exists() {
        fs::remove_dir_all(&test_workdir)
            .map_err(|e| anyhow!("Failed to clean up workdir {:?}: {:?}", test_workdir, e))?;
    }

    // setup the compiler
    let mut controller = MoveController::new(test_workdir)?;

    // compile stdlib (including nursery)
    controller.compile(&[&*MOVE_STDLIB_MODULES], Some(Address::DIEM_CORE), true)?;
    controller.compile(&[&*MOVE_LIBNURSERY], Some(Address::DIEM_CORE), true)?;

    // compile the script
    let script_path = MOVE_DIEM_SCRIPTS
        .join(script_name)
        .with_extension(MOVE_EXTENSION);
    controller.compile(&[&script_path], Some(Address::DIEM_CORE), true)?;

    // run a symbolization for each type instantiation
    for (type_tags, sigs_and_args) in script_info {
        for (signers, sym_args) in sigs_and_args {
            controller.symbolize(
                &signers,
                &sym_args,
                &type_tags,
                None,
                &[],
                false,
                true,
                true,
                true,
                true,  // TODO: disable no-run when development is done
                false, // TODO: enable strict mode when development is done
            )?;
        }
    }

    Ok(())
}

// runs all the tests
harness!(run_one_test, *MOVE_E2E_TESTS_SCRIPT, r".*/.{64}/0$");
