// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use log::debug;
use regex::{Captures, Regex};
use simplelog::{ConfigBuilder, LevelFilter, SimpleLogger, TermLogger, TerminalMode};
use std::{
    fs::{self, File},
    io::{BufRead, BufReader},
    path::PathBuf,
};
use structopt::StructOpt;

use move_lang::{shared::Address, MOVE_EXTENSION};

use move_symexec::{
    configs::{is_in_pretty_mode, MOVE_DIEM_SCRIPTS, MOVE_LIBNURSERY, MOVE_STDLIB_MODULES},
    controller::MoveController,
};

/// Tag added to log messages
const LOG_TAG: &str = "[control]";

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
    inputs: Vec<PathBuf>,

    /// A directory storing Move outputs produced by build, execution, and symbolization
    #[structopt(long = "output", short = "o", default_value = DEFAULT_OUTPUT)]
    output: PathBuf,

    /// Mark that the stdlib library will not be prepared
    #[structopt(long = "no-stdlib")]
    no_stdlib: bool,

    /// Mark that the diem script will be prepared
    #[structopt(long = "use-diem", conflicts_with = "no-stdlib")]
    use_diem: Option<String>,

    /// Do not clean the workspace after running the commands
    #[structopt(long = "no-clean", short = "C")]
    no_clean: bool,

    /// Print additional diagnostics
    #[structopt(long = "verbose", short = "v")]
    verbose: bool,
}

fn work(
    output: PathBuf,
    no_stdlib: bool,
    use_diem: Option<String>,
    inputs: Vec<PathBuf>,
) -> Result<()> {
    // create controller
    let mut controller = MoveController::new(output)?;

    // preprocessing
    if !no_stdlib {
        debug!("{} Building stdlib modules", LOG_TAG);
        controller.compile(
            &[&*MOVE_STDLIB_MODULES, &*MOVE_LIBNURSERY],
            Some(Address::DIEM_CORE),
            true,
        )?;
    }

    if let Some(script_name) = use_diem {
        debug!("{} Building diem script '{}'", LOG_TAG, script_name);
        controller.compile(
            &[&(*MOVE_DIEM_SCRIPTS
                .join(script_name)
                .with_extension(MOVE_EXTENSION))],
            Some(Address::DIEM_CORE),
            true,
        )?;
    }

    // go through the inputs
    let subst = Regex::new(r"\{\{(.*?)\}\}").unwrap();
    for input in inputs {
        for line in BufReader::new(File::open(input)?).lines() {
            let line = line?;
            // allow blank lines and comments
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            debug!("{} {}", LOG_TAG, line);

            // replace diem framework sources
            let command = subst.replace_all(&line, |caps: &Captures| {
                let token = caps.get(1).unwrap().as_str();
                if token == "stdlib" {
                    format!(
                        "{} {}",
                        MOVE_STDLIB_MODULES.to_str().unwrap(),
                        MOVE_LIBNURSERY.to_str().unwrap(),
                    )
                } else {
                    let mut file = None;
                    for loc in &[
                        &*MOVE_STDLIB_MODULES,
                        &*MOVE_LIBNURSERY,
                        &*MOVE_DIEM_SCRIPTS,
                    ] {
                        let path = loc.join(token);
                        if path.exists() {
                            file = Some(path.to_str().unwrap().to_owned());
                            break;
                        }
                    }
                    file.unwrap_or_else(|| token.to_owned())
                }
            });

            // actually run the command
            controller.handle_command(&command)?;
        }
    }

    // everything is fine
    Ok(())
}

fn main() -> Result<()> {
    let MainArgs {
        inputs,
        output,
        no_stdlib,
        use_diem,
        no_clean,
        verbose,
    } = MainArgs::from_args();
    let pretty = is_in_pretty_mode();

    // setup logging
    let log_level = if verbose {
        LevelFilter::Debug
    } else {
        LevelFilter::Info
    };
    let log_config = ConfigBuilder::new()
        .set_time_level(if pretty {
            LevelFilter::Debug
        } else {
            LevelFilter::Off
        })
        .set_thread_level(LevelFilter::Off)
        .set_target_level(LevelFilter::Off)
        .set_location_level(LevelFilter::Off)
        .build();

    if pretty {
        TermLogger::init(log_level, log_config, TerminalMode::Stderr)?;
    } else {
        SimpleLogger::init(log_level, log_config)?;
    }

    // prepare the workspace
    if output.exists() {
        fs::remove_dir_all(&output)?;
    }
    fs::create_dir_all(&output)?;

    // do the actual work
    let result = work(output.clone(), no_stdlib, use_diem, inputs);

    // clean the workspace if needed
    if !no_clean {
        fs::remove_dir_all(output)?;
    }

    // return results from the actual work
    result
}
