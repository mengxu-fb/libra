// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use log::debug;
use simplelog::{ConfigBuilder, LevelFilter, SimpleLogger, TermLogger, TerminalMode};
use std::{
    fs::{self, File},
    io::{BufRead, BufReader},
    path::PathBuf,
};
use structopt::StructOpt;

use move_lang::{shared::Address, MOVE_EXTENSION};

use move_symexec::{
    configs::{MOVE_DIEM_SCRIPTS, MOVE_LIBNURSERY, MOVE_STDLIB_MODULES},
    controller::MoveController,
};

/// Default directory where the outputs live
const DEFAULT_OUTPUT: &str = "move_symexec_output";

/// The intention of this symbolic executor is to generate new tests
/// that increase coverage on the module(s) being tested
#[derive(StructOpt)]
#[structopt(
    name = "Move symbolic executor",
    about = "Symbolically execute a Move script"
)]
struct MainArgs {
    /// A list of files to take commands from, in which files are iterated in the input order
    #[structopt()]
    input: Vec<PathBuf>,

    /// A directory storing Move outputs produced by build, execution, and symbolization
    #[structopt(long = "output", short = "o", default_value = DEFAULT_OUTPUT)]
    output: PathBuf,

    /// Mark that the stdlib library will not be prepared
    #[structopt(long = "no-stdlib")]
    no_stdlib: bool,

    /// Mark that the libnursery library will not be prepared
    #[structopt(long = "no-libnursery", conflicts_with = "no-stdlib")]
    no_libnursery: bool,

    /// Mark that the diem script will be prepared
    #[structopt(long = "use-diem", conflicts_with = "no-stdlib")]
    use_diem: Option<String>,

    /// Do not clean the workspace after running the commands
    #[structopt(long = "no-clean", short = "C")]
    no_clean: bool,

    /// Print additional diagnostics
    #[structopt(long = "verbose", short = "v")]
    verbose: bool,

    /// Print pretty diagnostics information
    #[structopt(long = "verbose-pretty", short = "V", requires = "verbose")]
    verbose_pretty: bool,
}

fn main() -> Result<()> {
    let args = MainArgs::from_args();

    // setup logging
    let log_level = if args.verbose {
        LevelFilter::Debug
    } else {
        LevelFilter::Info
    };
    let log_config = ConfigBuilder::new()
        .set_time_level(if args.verbose_pretty {
            LevelFilter::Debug
        } else {
            LevelFilter::Off
        })
        .set_thread_level(LevelFilter::Off)
        .set_target_level(LevelFilter::Off)
        .set_location_level(LevelFilter::Off)
        .build();

    if args.verbose_pretty {
        TermLogger::init(log_level, log_config, TerminalMode::Stderr)?;
    } else {
        SimpleLogger::init(log_level, log_config)?;
    }

    // prepare the workspace
    let workdir = args.output;
    if workdir.exists() {
        fs::remove_dir_all(&workdir)?;
    }
    fs::create_dir_all(&workdir)?;

    // create controller
    let mut controller = MoveController::new(workdir.clone())?;

    // preprocessing
    if !args.no_stdlib {
        controller.compile(&[&*MOVE_STDLIB_MODULES], Some(Address::DIEM_CORE), true)?;
        if !args.no_libnursery {
            controller.compile(&[&*MOVE_LIBNURSERY], Some(Address::DIEM_CORE), true)?;
        }
    }

    if let Some(script_name) = args.use_diem {
        controller.compile(
            &[&(*MOVE_DIEM_SCRIPTS
                .join(script_name)
                .with_extension(MOVE_EXTENSION))],
            Some(Address::DIEM_CORE),
            true,
        )?;
    }

    // go through the inputs
    for input in args.input {
        for line in BufReader::new(File::open(input)?).lines() {
            let line = line?;

            // allow blank lines and comments
            if line.is_empty() || line.starts_with('#') {
                continue;
            }

            debug!("Command '{}'", line);
            controller.handle_command(&line)?;
        }
    }

    // clean the workspace if needed
    if !args.no_clean {
        fs::remove_dir_all(workdir)?;
    }

    // done
    Ok(())
}
