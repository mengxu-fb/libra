// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
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
use spec_lang::run_spec_lang_compiler;
use vm::file_format::{CompiledModule, CompiledScript};

use crate::{
    builder::MoveStatefulBuilder,
    executor::MoveExecutor,
    sym_filter::FuncIdMatcher,
    sym_oracle::SymOracle,
    sym_vm_types::{parse_sym_transaction_argument, SymTransactionArgument},
    symbolizer::MoveSymbolizer,
    utils::PathsToStrings,
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
    /// Compile Move source files (may contain both modules and scripts) from input paths given
    #[structopt(name = "compile")]
    Compile {
        /// Directories storing Move source files
        #[structopt()]
        input: Vec<PathBuf>,

        /// Sender address, will be applied to all Move source files in this batch of compilation
        #[structopt(long = "sender", short = "s", parse(try_from_str = Address::parse_str))]
        sender: Option<Address>,

        /// Mark that the modules and scripts compiled should have no impact on future operations
        #[structopt(long = "dry-run", short = "x")]
        dry_run: bool,
    },

    /// Execute the script compiled and committed to state. There should be **one and only one**
    /// script compiled and committed. All modules compiled and committed will be preloaded before
    /// the script is executed
    #[structopt(name = "execute")]
    Execute {
        /// Possibly-empty list of signers for the current transaction
        /// (e.g., `account` in `main(&account: signer)`).
        /// Must match the number of signers expected by every script
        #[structopt(long = "signers", short = "s", parse(try_from_str = AccountAddress::from_hex_literal))]
        signers: Vec<AccountAddress>,

        /// Possibly-empty list of arguments passed to the transaction
        /// (e.g., `i` in `main(i: u64)`).
        /// Must match the arguments types expected by every script
        #[structopt(long = "val-args", short = "v", parse(try_from_str = parse_transaction_argument))]
        val_args: Vec<TransactionArgument>,

        /// Possibly-empty list of type arguments passed to the
        /// transaction (e.g., `T` in `main<T>()`).
        /// Must match the type arguments expected by every script
        #[structopt(long = "type-args", short = "t", parse(try_from_str = parse_type_tag))]
        type_args: Vec<TypeTag>,

        /// Mark that this operation is expected to be failed or aborted
        #[structopt(long = "expect-failure", short = "F")]
        expect_failure: bool,

        /// Mark that the results from script execution should have no impact on future operations
        #[structopt(long = "dry-run", short = "x")]
        dry_run: bool,
    },

    /// Symbolize the **one and only one** script and its dependency modules (with functions
    /// filtered by `--inclusions` and `--exclusions`)
    #[structopt(name = "symbolize")]
    Symbolize {
        /// Possibly-empty list of signers for the current transaction
        /// (e.g., `account` in `main(&account: signer)`).
        /// Must match the number of signers expected by every script
        #[structopt(long = "signers", short = "s", parse(try_from_str = AccountAddress::from_hex_literal))]
        signers: Vec<AccountAddress>,

        /// Possibly-empty list of arguments passed to the transaction
        /// (e.g., `i` in `main(i: u64)`).
        /// - For concrete values, the format is C::<value>
        ///  - The <value> must match the arguments types expected by every script
        /// - For symbolic values, the format is S::<var>
        ///  - The <var> is treated as a string and should be unique cross all <var> declarations
        #[structopt(long = "sym-args", short = "v", parse(try_from_str = parse_sym_transaction_argument))]
        sym_args: Vec<SymTransactionArgument>,

        /// Possibly-empty list of type arguments passed to the transaction
        /// (e.g., `T` in `main<T>()`).
        /// Must match the type arguments expected by every script
        #[structopt(long = "type-tags", short = "t", parse(try_from_str = parse_type_tag))]
        type_tags: Vec<TypeTag>,

        /// List of function identifiers to be included for tracking and symbolic execution
        #[structopt(long = "inclusion", short = "i", parse(try_from_str = FuncIdMatcher::new))]
        inclusion: Option<Vec<FuncIdMatcher>>,

        /// List of function identifiers to be excluded for tracking and symbolic execution
        #[structopt(long = "exclusion", short = "e", parse(try_from_str = FuncIdMatcher::new))]
        exclusion: Vec<FuncIdMatcher>,

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
    /// The pushed information will be lost on pop
    #[structopt(name = "push")]
    Push,

    /// Matches push, clean up all effects caused by operations since last push.
    /// The execution will have no effect if there are more pops than pushes
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

    pub fn compile<P: AsRef<Path>, A: AsRef<[P]>>(
        &mut self,
        move_src: A,
        sender: Option<Address>,
        commit: bool,
    ) -> Result<()> {
        self.builder.compile(move_src, sender, commit)
    }

    pub fn execute(
        &mut self,
        signers: &[AccountAddress],
        val_args: &[TransactionArgument],
        type_args: &[TypeTag],
        expect_failure: bool,
        commit: bool,
    ) -> Result<()> {
        // get the script
        let mut scripts = self.builder.get_compiled_scripts_all();
        if scripts.len() != 1 {
            bail!("Expecting only one script, found {}", scripts.len());
        }
        let script = scripts.pop().unwrap();

        // prepare a new executor
        let workdir = self
            .workdir_executor
            .join(self.counter_executor.to_string());
        fs::create_dir(&workdir)?;
        self.counter_executor += 1;
        let mut executor = MoveExecutor::new(workdir);

        // preload modules
        let modules = self.builder.get_compiled_modules_all();
        executor.preload_modules(&modules);

        // execute it
        executor.execute_script(
            script,
            &signers,
            &val_args,
            &type_args,
            expect_failure,
            commit,
        )
    }

    pub fn symbolize(
        &mut self,
        signers: &[AccountAddress],
        sym_args: &[SymTransactionArgument],
        type_tags: &[TypeTag],
        inclusion: Option<&[FuncIdMatcher]>,
        exclusion: &[FuncIdMatcher],
        output_exec_graph: bool,
        output_exec_graph_stats: bool,
    ) -> Result<()> {
        // get the script
        let mut scripts = self.builder.get_compiled_scripts_all();
        if scripts.len() != 1 {
            bail!(
                "Expecting one and only one compiled script, found {}",
                scripts.len()
            );
        }
        let script = scripts.pop().unwrap();

        // get the address
        let addresses = self.builder.get_sender_addresses_all();
        if addresses.len() > 1 {
            bail!(
                "Expecting at most one sender address, found {}",
                addresses.len()
            );
        }
        // NOTE: this address is the sender address for the one and only script, and this value is
        // needed by `run_spec_lang_compiler`
        let address = addresses.into_iter().next().map(|addr| addr.to_string());

        // build the global env
        let sources = self.builder.get_source_locations_all();
        let global_env =
            run_spec_lang_compiler(sources.paths_to_strings()?, vec![], address.as_deref())?;

        // build the oracle
        let oracle = SymOracle::new(&global_env, inclusion, exclusion);
        debug!(
            "{} functions tracked symbolically",
            oracle.num_tracked_functions()
        );

        // prepare a new symbolizer
        let workdir = self
            .workdir_symbolizer
            .join(self.counter_symbolizer.to_string());
        fs::create_dir(&workdir)?;
        self.counter_symbolizer += 1;
        let symbolizer = MoveSymbolizer::new(workdir, script, &oracle, type_tags)?;

        // output information if requested
        if output_exec_graph {
            symbolizer.save_exec_graph()?;
        }
        if output_exec_graph_stats {
            symbolizer.save_exec_graph_stats()?;
        }

        // symbolize it
        symbolizer.symbolize(signers, sym_args)
    }

    pub fn push(&mut self) -> Result<()> {
        self.builder.push()
    }

    pub fn pop(&mut self) -> Result<()> {
        self.builder.pop()
    }

    pub fn get_compiled_units_recent(&self) -> (Vec<&CompiledModule>, Vec<&CompiledScript>) {
        (
            self.builder.get_compiled_modules_recent(),
            self.builder.get_compiled_scripts_recent(),
        )
    }

    pub fn get_compilation_interfaces(&self) -> Vec<&Path> {
        self.builder.get_compilation_interfaces()
    }

    pub fn handle_command(&mut self, cmdl: &str) -> Result<()> {
        let args = OpArgs::from_iter(&shell_words::split(cmdl)?);

        // handle commands
        match args.cmd {
            OpCommand::Compile {
                input,
                sender,
                dry_run,
            } => self.compile(&input, sender, !dry_run),
            OpCommand::Execute {
                signers,
                val_args,
                type_args,
                expect_failure,
                dry_run,
            } => self.execute(&signers, &val_args, &type_args, expect_failure, !dry_run),
            OpCommand::Symbolize {
                signers,
                sym_args,
                type_tags,
                inclusion,
                exclusion,
                output_exec_graph,
                output_exec_graph_stats,
            } => self.symbolize(
                &signers,
                &sym_args,
                &type_tags,
                inclusion.as_deref(),
                &exclusion,
                output_exec_graph,
                output_exec_graph_stats,
            ),
            OpCommand::Push => self.push(),
            OpCommand::Pop => self.pop(),
        }
    }
}
