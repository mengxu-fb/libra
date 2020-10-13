// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use anyhow::Result;
use simplelog::{ConfigBuilder, LevelFilter, SimpleLogger, TermLogger, TerminalMode};
use std::path::PathBuf;
use structopt::StructOpt;

use move_core_types::{
    account_address::AccountAddress, language_storage::TypeTag, parser,
    transaction_argument::TransactionArgument,
};
use move_symexec::symbolizer;

/// Default directory where Move modules live
pub const MOVE_SRC: &str = "move_src";

/// Default directory where saved Move resources live
pub const MOVE_DATA: &str = "move_data";

/// Default directory for build output
pub const MOVE_OUTPUT: &str = "move_build_output";

/// Default path to directory containing libsymexec
pub const MOVE_LIBSYMEXEC: [&str; 2] = [env!("CARGO_MANIFEST_DIR"), "libsymexec"];

/// Default path to directory containing nursery (source)
pub const MOVE_LIBNURSERY: [&str; 5] =
    [env!("CARGO_MANIFEST_DIR"), "..", "..", "stdlib", "nursery"];

/// Default path to directory containing stdlib (pre-built)
pub const MOVE_STDLIB_BIN: [&str; 6] = [
    env!("CARGO_MANIFEST_DIR"),
    "..",
    "..",
    "stdlib",
    "compiled",
    "stdlib",
];

pub const MOVE_STDLIB_SRC: [&str; 5] =
    [env!("CARGO_MANIFEST_DIR"), "..", "..", "stdlib", "modules"];

/// The intention of this symbolic executor is to generate new tests
/// that increase coverage on the module(s) being tested
#[derive(StructOpt)]
#[structopt(
    name = "Move symbolic executor",
    about = "Symbolically execute a Move script"
)]
struct SymExec {
    /// Directories storing source code for Move modules.
    /// Modules in these paths
    ///   1. will be loaded before `script_file`, and
    ///   2. will be symbolically executed to probe new execution paths
    ///      unless excluded by markings in the `script_file`
    #[structopt(long = "move-src", short = "s", global = true)]
    move_src: Vec<String>,

    /// Mark that no default values will be added to `move_src`
    #[structopt(long = "no-default-move-src", short = "S", global = true)]
    no_default_move_src: bool,

    /// Directories storing libraries for `move_src` and `script_file`
    /// (i.e., Move libraries)
    /// Modules in this directory
    ///   1. will be loaded before `script_file`, but
    ///   2. will not be symbolically executed,
    ///      instead, they will be concretely executed.
    #[structopt(long = "move-lib", short = "l", global = true)]
    move_lib: Vec<String>,

    /// Mark that the libsymexec library will not be loaded
    #[structopt(long = "no-libsymexec", global = true)]
    no_libsymexec: bool,

    /// Mark that the libnursery library will not be loaded
    #[structopt(long = "no-libnursery", global = true)]
    no_libnursery: bool,

    /// Directories storing pre-builts for `move_src` and `script_file`
    /// (i.e., Move stdlib)
    /// Modules in this directory
    ///   1. will be loaded before `script_file`, but
    ///   2. will not be symbolically executed,
    ///      instead, they will be concretely executed.
    #[structopt(long = "move-sys", short = "d", global = true)]
    move_sys: Vec<String>,

    /// Mark that the stdlib library will not be loaded
    #[structopt(long = "no-stdlib", global = true)]
    no_stdlib: bool,

    /// Mark that the stdlib library needs to be built instead of using
    /// the pre-built library
    #[structopt(long = "build-stdlib", global = true)]
    build_stdlib: bool,

    /// A directory storing Move and symbolic execution outputs produced
    /// by script execution.
    #[structopt(
        long = "move-data",
        short = "o",
        default_value = MOVE_DATA,
        global = true,
    )]
    move_data: String,

    /// A directory storing Move outputs (e.g., bytecode, source maps)
    /// produced by compilation.
    #[structopt(
        long = "move-output",
        short = "b",
        default_value = MOVE_OUTPUT,
        global = true,
    )]
    move_output: String,

    /// Print additional diagnostics
    #[structopt(long = "verbose", short = "v", global = true)]
    verbose: bool,

    /// Print pretty diagnostics information
    #[structopt(long = "verbose-pretty", short = "V", global = true)]
    verbose_pretty: bool,

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

        /// Configuration file for the symbolic execution engine.
        /// Not setting the `config_file` means concreate execution.
        #[structopt(long = "config", short = "c")]
        config_file: Option<String>,

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

fn path_components_to_string(components: &[&str]) -> String {
    components
        .iter()
        .collect::<PathBuf>()
        .into_os_string()
        .into_string()
        .unwrap()
}

fn main() -> Result<()> {
    let args = SymExec::from_args();

    // setup options
    let mut default_move_src = Vec::new();
    if !args.no_default_move_src {
        default_move_src.push(MOVE_SRC.to_owned());
    }
    let move_src = [args.move_src, default_move_src].concat();

    let mut default_move_lib = Vec::new();
    if !args.no_libsymexec {
        default_move_lib.push(path_components_to_string(&MOVE_LIBSYMEXEC));
    }
    if !args.no_stdlib {
        if args.build_stdlib {
            default_move_lib.push(path_components_to_string(&MOVE_STDLIB_SRC));
        }
        if !args.no_libnursery {
            default_move_lib.push(path_components_to_string(&MOVE_LIBNURSERY));
        }
    }
    let move_lib = [args.move_lib, default_move_lib].concat();

    let mut default_move_sys = Vec::new();
    if !args.no_stdlib && !args.build_stdlib {
        default_move_sys.push(path_components_to_string(&MOVE_STDLIB_BIN));
    }
    let move_sys = [args.move_sys, default_move_sys].concat();

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

    // match commands
    match &args.cmd {
        Command::Run {
            script_file,
            config_file,
            signers,
            val_args,
            type_args,
            no_clean,
        } => symbolizer::run(
            script_file,
            config_file.as_ref(),
            &signers,
            &val_args,
            &type_args,
            &move_src,
            &move_lib,
            &move_sys,
            &args.move_data,
            &args.move_output,
            !no_clean,
        ),
    }
}
