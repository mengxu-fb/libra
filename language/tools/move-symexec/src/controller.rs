// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use log::debug;
use std::{
    fs,
    path::{Path, PathBuf},
};
use structopt::{clap::AppSettings, StructOpt};

use move_core_types::{
    account_address::AccountAddress,
    language_storage::TypeTag,
    parser::{parse_transaction_argument, parse_type_tag},
    transaction_argument::TransactionArgument,
};
use move_lang::shared::Address;
use vm::file_format::{CompiledModule, CompiledScript};

use crate::{
    builder::MoveStatefulBuilder,
    executor::MoveExecutor,
    sym_filter::{collect_tracked_functions, FuncIdMatcher},
    sym_vm_types::{parse_sym_transaction_argument, SymTransactionArgument},
    symbolizer::MoveSymbolizer,
};

/// Default directory containing builder workdirs
const MOVE_BUILDER_WORKDIR: &str = "builder";

/// Default directory containing executor workdirs
const MOVE_EXECUTOR_WORKDIR: &str = "execute";

/// Default directory containing symbolizer workdirs
const MOVE_SYMBOLIZER_WORKDIR: &str = "symexec";

/// Arguments available per each operation in the symbolic executor
#[derive(StructOpt)]
#[structopt(setting = AppSettings::NoBinaryName)]
struct OpArgs {
    /// Subcommands
    #[structopt(subcommand)]
    cmd: OpCommand,
}

#[derive(StructOpt)]
enum OpCommand {
    /// Load pre-compiled Move units (modules or scripts) from input paths given.
    #[structopt(name = "load")]
    Load {
        /// Directories storing compiled Move modules or scripts
        /// Modules in this directory
        ///  1. will be loaded before script execution, but
        ///  2. will not be symbolically executed unless `--track` is set, instead, they must be
        ///     statically modeled.
        /// Either modules (default) or scripts (with `--script` set) will be loaded, but not both.
        #[structopt()]
        input: Vec<PathBuf>,

        /// Mark that the scripts will be loaded instead of modules.
        #[structopt(long = "script", short = "s")]
        script_loading: bool,

        /// Mark that the loaded Move compiled units will be tracked for symbolication execution.
        #[structopt(long = "track", short = "t", conflicts_with = "dry-run")]
        track: bool,

        /// Mark that this operation should have no impact on future operations.
        #[structopt(long = "dry-run", short = "x")]
        dry_run: bool,
    },

    /// Compile Move source files from input paths given.
    #[structopt(name = "compile")]
    Compile {
        /// Directories storing Move source files
        /// Modules in this directory
        ///  1. will be loaded before script execution, but
        ///  2. will not be symbolically executed unless `--track` is set, instead, they must be
        ///     statically modeled.
        /// Scripts in this directory will be compiled and executed.
        #[structopt()]
        input: Vec<PathBuf>,

        /// Sender address, will be applied to all Move source files in this batch of compilation.
        #[structopt(long = "sender", short = "s", parse(try_from_str = Address::parse_str))]
        sender: Option<Address>,

        /// Mark that the compiled Move modules/scripts will be tracked for symbolic execution.
        #[structopt(long = "track", short = "t", conflicts_with = "dry-run")]
        track: bool,

        /// Mark that this operation should have no impact on future operations.
        #[structopt(long = "dry-run", short = "x")]
        dry_run: bool,
    },

    /// Execute the scripts, compiled or loaded, and committed state.
    /// All modules, compiled or loaded, and committed, will be preloaded before script execution.
    /// The runtime arguments, including type and value arguments, will be applied to all scripts.
    #[structopt(name = "execute")]
    Execute {
        /// Possibly-empty list of signers for the current transaction
        /// (e.g., `account` in `main(&account: signer)`).
        /// Must match the number of signers expected by every script.
        #[structopt(long = "signers", short = "s", parse(try_from_str = AccountAddress::from_hex_literal))]
        signers: Vec<AccountAddress>,

        /// Possibly-empty list of arguments passed to the transaction
        /// (e.g., `i` in `main(i: u64)`).
        /// Must match the arguments types expected by every script.
        #[structopt(long = "val-args", short = "v", parse(try_from_str = parse_transaction_argument))]
        val_args: Vec<TransactionArgument>,

        /// Possibly-empty list of type arguments passed to the
        /// transaction (e.g., `T` in `main<T>()`).
        /// Must match the type arguments expected by every script.
        #[structopt(long = "type-args", short = "t", parse(try_from_str = parse_type_tag))]
        type_args: Vec<TypeTag>,

        /// Execute only the scripts compiled in the most recent batch (i.e., the last build push)
        /// (by default, execute all scripts)
        #[structopt(long = "recent-only")]
        recent_only: bool,

        /// Execute only the scripts marked for symbolic tracking (by default, execute all scripts)
        #[structopt(long = "tracked-only")]
        tracked_only: bool,

        /// Mark that this operation is expected to be failed or aborted
        #[structopt(long = "expect-failure", short = "F")]
        expect_failure: bool,

        /// Mark that this operation should have no impact on future
        /// operations.
        #[structopt(long = "dry-run", short = "x")]
        dry_run: bool,
    },

    /// Symbolize the scripts and modules marked as tracking (with functions filtered by
    /// `--inclusions` and `--exclusions`).
    #[structopt(name = "symbolize")]
    Symbolize {
        /// Possibly-empty list of signers for the current transaction
        /// (e.g., `account` in `main(&account: signer)`).
        /// Must match the number of signers expected by every script.
        #[structopt(long = "signers", short = "s", parse(try_from_str = AccountAddress::from_hex_literal))]
        signers: Vec<AccountAddress>,

        /// Possibly-empty list of arguments passed to the transaction
        /// (e.g., `i` in `main(i: u64)`).
        /// - For concrete values, the format is C::<value>
        ///  - The <value> must match the arguments types expected by every script.
        /// - For symbolic values, the format is S::<var>
        ///  - The <var> is treated as a string and should be unique cross all <var> declarations.
        #[structopt(long = "sym-args", short = "v", parse(try_from_str = parse_sym_transaction_argument))]
        sym_args: Vec<SymTransactionArgument>,

        /// Possibly-empty list of type arguments passed to the transaction
        /// (e.g., `T` in `main<T>()`).
        /// Must match the type arguments expected by every script.
        #[structopt(long = "type-tags", short = "t", parse(try_from_str = parse_type_tag))]
        type_tags: Vec<TypeTag>,

        /// List of function identifiers to be included for tracking and symbolic execution.
        #[structopt(long = "inclusion", short = "i", parse(try_from_str = FuncIdMatcher::new))]
        inclusion: Option<Vec<FuncIdMatcher>>,

        /// List of function identifiers to be excluded for tracking and symbolic execution.
        #[structopt(long = "exclusion", short = "e", parse(try_from_str = FuncIdMatcher::new))]
        exclusion: Vec<FuncIdMatcher>,

        /// Symbolize only the scripts compiled in the most recent batch (i.e., the last build push)
        /// (by default, symbolize all scripts marked so far)
        #[structopt(long = "recent-only")]
        recent_only: bool,

        /// Output the composed execution graph in dot format
        #[structopt(long = "output-exec-graph")]
        output_exec_graph: bool,

        /// Output statistics  about the composed execution graph
        #[structopt(long = "output-exec-graph-stats")]
        output_exec_graph_stats: bool,
    },

    /// Push the state stack:
    /// - for build state: modules and scripts compiled will be saved in a separate layer
    /// - for exec state: the transaction effects will be saved in a separate layer
    /// The pushed information will be lost on pop.
    #[structopt(name = "push")]
    Push,

    /// Matches push, clean up all effects caused by operations since last push.
    /// The execution will have no effect if there are more pops than pushes.
    #[structopt(name = "pop")]
    Pop,
}

pub struct MoveController {
    builder: MoveStatefulBuilder,
    workdir_executor: PathBuf,
    counter_executor: usize,
    workdir_symbolizer: PathBuf,
    counter_symbolizer: usize,
}

impl MoveController {
    pub fn new(workdir: PathBuf) -> Result<Self> {
        fs::create_dir_all(&workdir)?;

        let workdir_builder = workdir.join(MOVE_BUILDER_WORKDIR);
        fs::create_dir(&workdir_builder)?;

        let workdir_executor = workdir.join(MOVE_EXECUTOR_WORKDIR);
        fs::create_dir(&workdir_executor)?;

        let workdir_symbolizer = workdir.join(MOVE_SYMBOLIZER_WORKDIR);
        fs::create_dir(&workdir_symbolizer)?;

        Ok(Self {
            builder: MoveStatefulBuilder::new(workdir_builder)?,
            workdir_executor,
            counter_executor: 0,
            workdir_symbolizer,
            counter_symbolizer: 0,
        })
    }

    pub fn load<P: AsRef<Path>, A: AsRef<[P]>>(
        &mut self,
        move_bin: A,
        script_loading: bool,
        track: bool,
        commit: bool,
    ) -> Result<()> {
        self.builder.load(move_bin, script_loading, track, commit)
    }

    pub fn compile<P: AsRef<Path>, A: AsRef<[P]>>(
        &mut self,
        move_src: A,
        sender: Option<Address>,
        track: bool,
        commit: bool,
    ) -> Result<()> {
        self.builder.compile(move_src, sender, track, commit)
    }

    pub fn execute(
        &mut self,
        signers: &[AccountAddress],
        val_args: &[TransactionArgument],
        type_args: &[TypeTag],
        recent_only: bool,
        tracked_only: bool,
        expect_failure: bool,
        commit: bool,
    ) -> Result<()> {
        // collect modules
        let modules = self.builder.get_compiled_modules_all(None);

        // collect scripts
        let track_opt = if tracked_only { Some(true) } else { None };
        let scripts = if recent_only {
            self.builder.get_compiled_scripts_recent(track_opt)
        } else {
            self.builder.get_compiled_scripts_all(track_opt)
        };

        // run each script with a new executor
        for script in scripts {
            let workdir = self
                .workdir_executor
                .join(self.counter_executor.to_string());
            fs::create_dir(&workdir)?;
            self.counter_executor += 1;

            let mut executor = MoveExecutor::new(workdir);
            executor.preload_modules(&modules);

            executor.execute_script(
                &script,
                &signers,
                &val_args,
                &type_args,
                expect_failure,
                commit,
            )?;
        }

        // done
        Ok(())
    }

    pub fn symbolize(
        &mut self,
        signers: &[AccountAddress],
        sym_args: &[SymTransactionArgument],
        type_tags: &[TypeTag],
        inclusion: Option<&[FuncIdMatcher]>,
        exclusion: &[FuncIdMatcher],
        recent_only: bool,
        output_exec_graph: bool,
        output_exec_graph_stats: bool,
    ) -> Result<()> {
        // collect modules
        let modules = self.builder.get_compiled_modules_all(None);

        // collect scripts
        let scripts = if recent_only {
            self.builder.get_compiled_scripts_recent(Some(true))
        } else {
            self.builder.get_compiled_scripts_all(Some(true))
        };

        // collect information
        let tracked_modules = self.builder.get_compiled_modules_all(Some(true));
        let tracked_functions =
            collect_tracked_functions(&tracked_modules, inclusion, Some(&exclusion));
        debug!(
            "{} functions to be tracked symbolically",
            tracked_functions.values().flatten().count()
        );

        // run each script with a new symbolizer
        for script in scripts {
            let workdir = self
                .workdir_symbolizer
                .join(self.counter_symbolizer.to_string());
            fs::create_dir(&workdir)?;
            self.counter_symbolizer += 1;

            let mut symbolizer = MoveSymbolizer::new(workdir);
            symbolizer.symbolize(
                &script,
                &modules,
                &tracked_functions,
                &signers,
                &sym_args,
                &type_tags,
                output_exec_graph,
                output_exec_graph_stats,
            )?;
        }

        // done
        Ok(())
    }

    pub fn push(&mut self) -> Result<()> {
        self.builder.push()
    }

    pub fn pop(&mut self) -> Result<()> {
        self.builder.pop()
    }

    pub fn get_compiled_units_recent(
        &self,
        track_opt: Option<bool>,
    ) -> (Vec<&CompiledModule>, Vec<&CompiledScript>) {
        self.builder.get_compiled_units_recent(track_opt)
    }

    pub fn handle_command(&mut self, cmdl: &str) -> Result<()> {
        let args = OpArgs::from_iter(&shell_words::split(cmdl)?);

        // handle commands
        match args.cmd {
            OpCommand::Load {
                input,
                script_loading,
                track,
                dry_run,
            } => self.load(&input, script_loading, track, !dry_run),
            OpCommand::Compile {
                input,
                sender,
                track,
                dry_run,
            } => self.compile(&input, sender, track, !dry_run),
            OpCommand::Execute {
                signers,
                val_args,
                type_args,
                recent_only,
                tracked_only,
                expect_failure,
                dry_run,
            } => self.execute(
                &signers,
                &val_args,
                &type_args,
                recent_only,
                tracked_only,
                expect_failure,
                !dry_run,
            ),
            OpCommand::Symbolize {
                signers,
                sym_args,
                type_tags,
                inclusion,
                exclusion,
                recent_only,
                output_exec_graph,
                output_exec_graph_stats,
            } => self.symbolize(
                &signers,
                &sym_args,
                &type_tags,
                inclusion.as_deref(),
                &exclusion,
                recent_only,
                output_exec_graph,
                output_exec_graph_stats,
            ),
            OpCommand::Push => self.push(),
            OpCommand::Pop => self.pop(),
        }
    }
}
