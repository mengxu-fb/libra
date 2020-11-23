// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use datatest_stable::{self, harness};
use log::error;
use once_cell::sync::Lazy;
use std::{
    fmt,
    path::{Path, PathBuf},
    process::Command,
    str,
};

use move_symexec::crate_path_string;

// Path to the directory of micro tests functional testsuites
crate_path_string!(MICRO_TESTS, "tests", "micro-tests");

/// Piggyback on the test-infra to run tests
#[derive(Debug)]
struct MicroTestError(String);

impl fmt::Display for MicroTestError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "\n\n{}", self.0)
    }
}

impl std::error::Error for MicroTestError {}

fn run_one_test(test_path: &Path) -> datatest_stable::Result<()> {
    let test_workdir = test_path.parent().unwrap();

    // execute the command
    let output = Command::new("bash")
        .current_dir(test_workdir)
        .arg(test_path.file_name().unwrap().to_str().unwrap())
        .output()?;

    // show errors and bail
    if !output.status.success() {
        error!("Failed to execute test: {}", test_path.to_str().unwrap());
        error!("{}", str::from_utf8(&output.stdout)?);
        error!("{}", str::from_utf8(&output.stderr)?);
        return Err(Box::new(MicroTestError(format!(
            "Test failed with exit code: {}",
            output
                .status
                .code()
                .map_or_else(|| String::from("<none>"), |v| v.to_string())
        ))));
    }

    // done
    Ok(())
}

// runs all the tests
harness!(run_one_test, *MICRO_TESTS, r"run.cmd$");
