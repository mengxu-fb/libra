// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use once_cell::sync::Lazy;
use std::{fs, path::PathBuf, process::Command};
use structopt::StructOpt;
use tempfile::tempdir;

use move_symexec::{configs::PROJECT_ROOT, crate_path};

// Path to the directory of coverage reports in html
crate_path!(COV_REPORTS, "tests", "workspace", "cov");

#[derive(StructOpt)]
#[structopt()]
struct MainArgs {
    /// Serve the generated report only without generating it
    #[structopt(long = "serve-only", short = "s")]
    serve_only: bool,

    /// Choice of testsuite
    #[structopt(subcommand)]
    testsuite: TestSuite,
}

#[derive(StructOpt)]
enum TestSuite {
    /// The `micro_tests` testsuite
    #[structopt(name = "micro")]
    MicroTests,
}

impl TestSuite {
    fn name(&self) -> &'static str {
        match self {
            TestSuite::MicroTests => "micro_tests",
        }
    }
}

fn main() -> Result<()> {
    let MainArgs {
        serve_only,
        testsuite,
    } = MainArgs::from_args();

    let cov_dir = COV_REPORTS.join(testsuite.name());
    if !serve_only {
        if cov_dir.exists() {
            fs::remove_dir_all(&cov_dir)?;
        }
        fs::create_dir_all(&cov_dir)?;

        // create a tmp dir as workspace
        let wks_dir = tempdir()?;

        // run the test
        let mut cmd = Command::new("cargo");
        cmd.arg("test");
        match testsuite {
            TestSuite::MicroTests => {
                cmd.arg("--test").arg(testsuite.name());
            }
        };
        cmd.env("RUSTC_BOOTSTRAP", "1")
            .env(
                "RUSTFLAGS",
                [
                    "-Zprofile",
                    "-Ccodegen-units=1",
                    "-Copt-level=0",
                    "-Clink-dead-code",
                    "-Coverflow-checks=off",
                ]
                .join(" "),
            )
            .env("CARGO_INCREMENTAL", "0")
            .env("CARGO_TARGET_DIR", wks_dir.path())
            .current_dir(env!("CARGO_MANIFEST_DIR"));
        cmd.status()?;

        // run the conversion
        let debug_dir = wks_dir.path().join("debug/");
        let mut cmd = Command::new("grcov");
        cmd
            // output file from coverage: gcda files
            .arg(debug_dir.as_os_str())
            // source code location
            .arg("-s")
            .arg(".")
            // html output
            .arg("-t")
            .arg("html")
            .arg("--llvm")
            .arg("--branch")
            .arg("--ignore")
            .arg("/*")
            .arg("--ignore")
            .arg("x/*")
            .arg("--ignore")
            .arg("testsuite/*")
            .arg("--ignore-not-existing")
            .arg("-o")
            .arg(cov_dir.as_os_str())
            // run from root directory
            .current_dir(PROJECT_ROOT.as_os_str());
        cmd.status()?;

        // clean up the workspace
        wks_dir.close()?;
    }

    // serve the coverage report
    if !cov_dir.is_dir() {
        bail!(
            "Unable to find the coverage report in {}",
            cov_dir.to_str().unwrap()
        );
    }
    let mut cmd = Command::new("python3");
    cmd.arg("-m");
    cmd.arg("http.server");
    cmd.current_dir(cov_dir.as_os_str());
    cmd.status()?;
    Ok(())
}
