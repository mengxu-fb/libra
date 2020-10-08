// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use anyhow::Result;
use simplelog::{ConfigBuilder, LevelFilter, TermLogger, TerminalMode};
use structopt::StructOpt;

use move_symexec::symbolizer;

/// Default directory where Move modules live
pub const MOVE_SRC: &str = "move_src";

/// Default directory where dependencies (non-stdlib libraries) live
pub const MOVE_DEP: &str = "move_dep";

/// Default directory where saved Move resources live
pub const MOVE_DATA: &str = "move_data";

/// Default directory for build output
pub const MOVE_OUTPUT: &str = "move_build_output";

/// The intention of this symbolic executor is to generate new tests
/// that increase coverage on the module(s) being tested
#[derive(StructOpt)]
#[structopt(
    name = "Move symbolic executor",
    about = "Symbolically execute a Move script"
)]
struct SymExec {
    /// Directory storing source code for Move modules.
    /// Modules in these paths
    ///   1. will be loaded before `script_file`, and
    ///   2. will be symbolically executed to probe new execution paths.
    #[structopt(
        long = "move-src",
        default_value = MOVE_SRC,
        global = true,
    )]
    move_src: Vec<String>,

    /// Directory storing dependencies for `move_src` and `script_file`
    /// (i.e., Move libraries)
    /// Modules in this directory
    ///   1. will be loaded before `script_file`, but
    ///   2. will not be symbolically executed,
    ///      instead, they will be concretely executed.
    #[structopt(
        long = "move-dep",
        default_value = MOVE_DEP,
        global = true,
    )]
    move_dep: Vec<String>,

    /// Directory storing Move outputs (e.g., resources, events, traces)
    /// produced by script execution.
    #[structopt(
        long = "move-data",
        default_value = MOVE_DATA,
        global = true,
    )]
    move_data: String,

    /// Directory storing Move outputs (e.g., bytecode, source maps)
    /// produced by compilation.
    #[structopt(
        long = "move-output",
        default_value = MOVE_OUTPUT,
        global = true,
    )]
    move_output: String,

    /// Print additional diagnostics
    #[structopt(long = "verbose", short = "v", global = true)]
    verbose: bool,

    /// Subcommands
    #[structopt(subcommand)]
    cmd: Command,
}

#[derive(StructOpt)]
enum Command {
    /// Symbolically execute a Move script that reads/writes resources
    /// stored in `move_data`.
    ///
    /// This command finds and compiles each each module stored in
    /// `move_src` and `move_lib`, and loads them into the VM before
    /// symbolically executing the script.
    #[structopt(name = "run")]
    Run {
        /// Path to script to be compiled and symbolically executed.
        #[structopt()]
        script_file: String,

        /// Do not clean directories after execution
        #[structopt(long = "no-clean", short = "C")]
        no_clean: bool,
    },
}

fn main() -> Result<()> {
    let args = SymExec::from_args();

    // setup logging
    TermLogger::init(
        if args.verbose {
            LevelFilter::Debug
        } else {
            LevelFilter::Info
        },
        ConfigBuilder::new()
            .set_thread_level(LevelFilter::Off)
            .set_target_level(LevelFilter::Off)
            .set_location_level(LevelFilter::Off)
            .build(),
        TerminalMode::Stderr,
    )?;

    // match commands
    match &args.cmd {
        Command::Run {
            script_file,
            no_clean,
        } => symbolizer::run(
            script_file,
            args.move_src.as_slice(),
            args.move_dep.as_slice(),
            &args.move_data,
            &args.move_output,
            !no_clean,
        ),
    }
}
