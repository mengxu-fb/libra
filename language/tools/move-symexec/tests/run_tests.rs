// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

use log::error;
use std::{
    fs::File,
    io::{BufRead, BufReader},
    path::Path,
    process::Command,
    str,
};

use datatest_stable::{harness, Result};

const MOVE_SYMEXEC_BIN_NAME: &str = "move-symexec";

#[derive(Debug)]
struct TestFailure {
    args_line: String,
    exit_code: Option<i32>,
}

impl std::fmt::Display for TestFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Test {} failed with exit code {}",
            &self.args_line,
            self.exit_code
                .map_or(String::from("<none>"), |v| v.to_string())
        )
    }
}

impl std::error::Error for TestFailure {}

fn run_one_test(args_path: &Path) -> Result<()> {
    let workdir = args_path.parent().unwrap();

    for args_line in BufReader::new(File::open(args_path)?).lines() {
        let args_line = args_line?;
        if args_line.starts_with('#') {
            // ignore comments
            continue;
        }
        let args_iter: Vec<&str> = args_line.split_whitespace().collect();
        if args_iter.is_empty() {
            // ignore empty lines
            continue;
        }

        // execute the command
        let output = Command::new("Cargo")
            .current_dir(workdir)
            .arg("run")
            .arg("--bin")
            .arg(MOVE_SYMEXEC_BIN_NAME)
            .arg("--")
            .args(args_iter)
            .output()?;

        // show errors and bail
        if !output.status.success() {
            error!("Failed to execute test: {}", args_line);
            error!("{}", str::from_utf8(&output.stdout)?);
            error!("{}", str::from_utf8(&output.stderr)?);
            return Err(Box::new(TestFailure {
                args_line,
                exit_code: output.status.code(),
            }));
        }
    }

    // done
    Ok(())
}

// runs all the tests
harness!(run_one_test, "tests/testsuite", r"args.txt$");
