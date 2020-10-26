// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use anyhow::Result;
use log::debug;
use simplelog::{ConfigBuilder, LevelFilter, SimpleLogger, TermLogger, TerminalMode};
use std::{
    fs::File,
    io::{BufRead, BufReader},
};
use structopt::StructOpt;

use move_symexec::{
    configs::{MOVE_LIBNURSERY, MOVE_LIBSYMEXEC, MOVE_STDLIB_BIN_MODULES, MOVE_STDLIB_SRC_MODULES},
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
    /// A list of files to take commands from. Files will be executed
    /// according to the input order.
    #[structopt()]
    input: Vec<String>,

    /// A directory storing Move and symbolic execution outputs produced
    /// by script execution.
    #[structopt(long = "output", short = "o", default_value = DEFAULT_OUTPUT)]
    output: String,

    /// Mark that the stdlib library will not be prepared
    #[structopt(long = "no-stdlib")]
    no_stdlib: bool,

    /// Mark that the stdlib library needs to be built instead of using
    /// the compiled version.
    #[structopt(long = "build-stdlib", conflicts_with = "no-stdlib")]
    build_stdlib: bool,

    /// Mark that the stdlib library needs to be tracked for symbolic
    /// execution, regardless of whether stdlib is compiled or loaded.
    #[structopt(long = "track-stdlib", conflicts_with = "no-stdlib")]
    track_stdlib: bool,

    /// Mark that the libnursery library will not be prepared
    #[structopt(long = "no-libnursery", conflicts_with = "no-stdlib")]
    no_libnursery: bool,

    /// Mark that the libsymexec library will not be prepared
    #[structopt(long = "no-libsymexec")]
    no_libsymexec: bool,

    /// Print additional diagnostics
    #[structopt(long = "no-clean", short = "C")]
    no_clean: bool,

    /// Print additional diagnostics
    #[structopt(long = "verbose", short = "v")]
    verbose: bool,

    /// Print pretty diagnostics information
    #[structopt(long = "verbose-pretty", short = "V")]
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

    // create controller
    let mut controller = MoveController::new(args.output, !args.no_clean)?;

    // preprocessing
    debug!("setup");
    if !args.no_stdlib {
        if args.build_stdlib {
            controller.compile(
                &[MOVE_STDLIB_SRC_MODULES.to_owned()],
                None,
                args.track_stdlib,
                true,
            )?;
        } else {
            controller.load(
                &[MOVE_STDLIB_BIN_MODULES.to_owned()],
                false,
                args.track_stdlib,
                true,
            )?;
        }

        if !args.no_libnursery {
            controller.compile(&[MOVE_LIBNURSERY.to_owned()], None, false, true)?;
        }
    }

    if !args.no_libsymexec {
        controller.compile(&[MOVE_LIBSYMEXEC.to_owned()], None, false, true)?;
    }

    // go through the inputs
    for input in args.input {
        for line in BufReader::new(File::open(input)?).lines() {
            let line = line?;
            debug!("{}", line);
            controller.handle(&line)?;
        }
    }

    // done
    Ok(())
}
