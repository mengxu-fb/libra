// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use datatest_stable::{self, harness};
use once_cell::sync::Lazy;
use std::{
    collections::BTreeMap,
    fs::{self, File},
    io::BufReader,
    path::{Path, PathBuf},
};
use tempfile::tempdir;

use compiled_stdlib::legacy::transaction_scripts::LegacyStdlibScript;
use diem_crypto::HashValue;
use diem_types::transaction::{Transaction, TransactionPayload, WriteSetPayload};
use move_lang::{shared::Address, MOVE_EXTENSION};

use move_symexec::{
    configs::{use_workspace, MOVE_DIEM_SCRIPTS, MOVE_LIBNURSERY, MOVE_STDLIB_MODULES},
    controller::MoveController,
    crate_path, crate_path_string,
};

static DIEM_SCRIPTS_HASHMAP: Lazy<BTreeMap<HashValue, String>> = Lazy::new(|| {
    LegacyStdlibScript::all()
        .into_iter()
        .map(|script| (script.hash(), script.name()))
        .collect()
});

// Path to the directory of e2e testsuites
crate_path_string!(
    MOVE_E2E_TESTS_TRACE,
    "tests",
    "workspace",
    "move-e2e-tests",
    "trace"
);

// Path to the testing workspace
crate_path!(
    MOVE_E2E_TESTS_ANALYSIS,
    "tests",
    "workspace",
    "move-e2e-tests",
    "analysis"
);

fn run_one_test(test_path: &Path) -> datatest_stable::Result<()> {
    let dir_path = test_path.parent().unwrap();

    // read test name
    let test_name = fs::read_to_string(dir_path.join("name"))?;
    let file_name = test_name.replace(':', "_");

    // derive workdir
    let tmp_wks = if use_workspace() {
        None
    } else {
        Some(tempdir()?)
    };

    let test_workdir = tmp_wks.as_ref().map_or_else(
        || MOVE_E2E_TESTS_ANALYSIS.join(&file_name),
        |t| t.path().to_owned(),
    );
    if tmp_wks.is_none() && test_workdir.exists() {
        fs::remove_dir_all(&test_workdir)?;
        fs::create_dir_all(&test_workdir)?;
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
        let txn: Transaction = serde_json::from_reader(BufReader::new(step_file))?;
        match txn {
            Transaction::BlockMetadata(_) | Transaction::GenesisTransaction(_) => {}
            Transaction::UserTransaction(signed_txn) => {
                let sender_script_opt = match signed_txn.payload() {
                    TransactionPayload::Script(script) => Some((signed_txn.sender(), script)),
                    TransactionPayload::Module(_) => {
                        // TODO: there is not much we can do as the module is written in IR, hence
                        // shortcut the test and call it successful
                        println!(
                            "Test case short-circuited due to module compilation: {}",
                            test_name
                        );
                        return Ok(());
                    }
                    TransactionPayload::WriteSet(WriteSetPayload::Direct(_)) => None,
                    TransactionPayload::WriteSet(WriteSetPayload::Script {
                        execute_as,
                        script,
                    }) => Some((*execute_as, script)),
                };

                if let Some((_sender, script)) = sender_script_opt {
                    let hval = HashValue::sha3_256_of(script.code());
                    // check whether this script is one of the standard diem scripts
                    let script_item = DIEM_SCRIPTS_HASHMAP.get(&hval);
                    if script_item.is_none() {
                        // TODO: there is not much we can do as the script is written in IR, hence
                        // shortcut the test and call it successful
                        println!(
                            "Test case partially skipped due to script compilation: {} - step {}",
                            test_name, seq
                        );
                        continue;
                    }

                    // compile the script
                    let script_name = script_item.unwrap();
                    let script_path = MOVE_DIEM_SCRIPTS
                        .join(script_name)
                        .with_extension(MOVE_EXTENSION);
                    controller.push(true, false, false)?;
                    controller.compile(&[&script_path], Some(Address::DIEM_CORE), true)?;

                    // symbolize it
                    controller.symbolize(script.ty_args())?;

                    // now pop the stack to remove the script
                    controller.pop(true, false, false)?;
                }
            }
        }
    }

    // clean up (if needed)
    if let Some(t) = tmp_wks {
        t.close()?;
    }
    Ok(())
}

// runs all the tests
harness!(run_one_test, *MOVE_E2E_TESTS_TRACE, r".*/name$");
