// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use anyhow::{bail, Result};
use simplelog::{ConfigBuilder, LevelFilter, TermLogger, TerminalMode};
use std::path::PathBuf;
use structopt::StructOpt;

use move_core_types::{
    account_address::AccountAddress, language_storage::TypeTag, parser,
    transaction_argument::TransactionArgument,
};
use move_symexec::symbolizer;

/// Default directory where Move modules live
pub const MOVE_SRC: &str = "move_src";

/// Default directory where dependencies (non-stdlib libraries) live
pub const MOVE_DEP: &str = "move_dep";

/// Default directory where saved Move resources live
pub const MOVE_DATA: &str = "move_data";

/// Default directory for build output
pub const MOVE_OUTPUT: &str = "move_build_output";

/// Default path to directory containing libsymexec
pub const MOVE_LIBSYMEXEC: [&str; 2] = [env!("CARGO_MANIFEST_DIR"), "libsymexec"];

/// Default path to directory containing stdlib
pub const MOVE_STDLIB: [&str; 6] = [
    env!("CARGO_MANIFEST_DIR"),
    "..",
    "..",
    "stdlib",
    "compiled",
    "stdlib",
];

/// Default path to directory containing nursery
pub const MOVE_NURSERY: [&str; 5] = [env!("CARGO_MANIFEST_DIR"), "..", "..", "stdlib", "nursery"];

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

    /// Directory containing libsymexec
    #[structopt(long = "move-libsymexec", global = true)]
    move_libsymexec: Option<Vec<String>>,

    /// Directory containing other pre-built libs (e.g., stdlib)
    #[structopt(long = "move-systemlibs", global = true)]
    move_systemlibs: Option<Vec<String>>,

    /// Mark that no other system libraries are needed
    #[structopt(long = "no-systemlibs", short = "L", global = true)]
    no_systemlibs: bool,

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

        /// Possibly-empty list of signers for the current transaction
        /// (e.g., `account` in `main(&account: signer)`).
        /// Must match the number of signers expected by `script_file`.
        #[structopt(
            long = "signers",
            parse(try_from_str = AccountAddress::from_hex_literal),
        )]
        signers: Vec<AccountAddress>,

        /// Possibly-empty list of arguments passed to the transaction
        /// (e.g., `i` in `main(i: u64)`).
        /// Must match the arguments types expected by `script_file`.
        #[structopt(
            long = "val-args",
            parse(try_from_str = parser::parse_transaction_argument),
        )]
        val_args: Vec<TransactionArgument>,

        /// Possibly-empty list of type arguments passed to the
        /// transaction (e.g., `T` in `main<T>()`).
        /// Must match the type arguments expected by `script_file`.
        #[structopt(
            long = "type-args",
            parse(try_from_str = parser::parse_type_tag),
        )]
        type_args: Vec<TypeTag>,

        /// Do not clean directories after execution
        #[structopt(long = "no-clean", short = "C")]
        no_clean: bool,
    },
}

fn main() -> Result<()> {
    let args = SymExec::from_args();

    // default options
    let move_libsymexec = args.move_libsymexec.unwrap_or_else(|| {
        vec![MOVE_LIBSYMEXEC
            .iter()
            .collect::<PathBuf>()
            .into_os_string()
            .into_string()
            .unwrap()]
    });

    if args.no_systemlibs && args.move_systemlibs.is_some() {
        bail!("Error: conflicting option on systemlibs");
    }

    let move_systemlibs = match args.no_systemlibs {
        true => vec![],
        false => args.move_systemlibs.unwrap_or_else(|| {
            vec![MOVE_STDLIB
                .iter()
                .collect::<PathBuf>()
                .into_os_string()
                .into_string()
                .unwrap()]
        }),
    };

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
            signers,
            val_args,
            type_args,
            no_clean,
        } => symbolizer::run(
            script_file,
            signers.as_slice(),
            val_args.as_slice(),
            type_args.as_slice(),
            args.move_src.as_slice(),
            args.move_dep.as_slice(),
            move_libsymexec.as_slice(),
            move_systemlibs.as_slice(),
            &args.move_data,
            &args.move_output,
            !no_clean,
        ),
    }
}
