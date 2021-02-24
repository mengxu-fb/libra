// Copyright (c) The Diem Core Contributors
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
use move_model::run_model_builder;
use vm::file_format::{CompiledModule, CompiledScript};

use crate::{
    builder::MoveStatefulBuilder, executor::MoveStatefulExecutor,
    symbolizer::MoveStatefulSymbolizer, utils::PathsToStrings,
};

/// Tag added to log messages
const LOG_TAG: &str = "[control]";

// directory layouts
//
// |-- output/
// |   |-- sessions/
// |   |   |-- 0/
// |   |   |   |-- workdir/
// |   |   |   |   |-- mv_interfaces/
// |   |   |   |-- playdir/
// |   |   |   |   |-- executions/
// |   |   |   |   |   |-- 0/
// |   |   |   |   |   |   |-- workdir/
// |   |   |   |   |   |   |   |-- resources/
// |   |   |   |   |   |   |   |-- events/
// |   |   |   |   |   |   |   |-- modules/
// |   |   |   |   |   |   |-- playdir/

/// Default directory under `output/` containing sessions
const OUTPUT_SESSIONS: &str = "sessions";

/// Default directory under `output/<session>/playdir` containing the storage dirs of executors
const OUTPUT_EXECUTIONS: &str = "executions";

/// Default directory under `output/<session>/playdir` containing the storage dirs of symbolizers
const OUTPUT_SYMBOLIZATIONS: &str = "symbolizations";

/// Arguments available per each operation in the symbolic executor
#[derive(StructOpt)]
#[structopt(setting = AppSettings::NoBinaryName)]
struct OpArgs {
    /// Mark that this operation is expected to be failed or aborted
    #[structopt(long = "expect-failure", short = "F")]
    expect_failure: bool,

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

        /// Mark that the results from script execution should have no impact on future operations
        #[structopt(long = "dry-run", short = "x")]
        dry_run: bool,
    },

    /// Symbolize the **one and only one** script and its dependency modules
    #[structopt(name = "symbolize")]
    Symbolize {
        /// Possibly-empty list of type arguments passed to the
        /// transaction (e.g., `T` in `main<T>()`).
        /// Must match the type arguments expected by every script
        #[structopt(long = "type-args", short = "t", parse(try_from_str = parse_type_tag))]
        type_args: Vec<TypeTag>,
    },

    /// Push the state stack:
    /// - for build state: modules and scripts compiled will be saved in a separate layer
    /// - for exec state: the transaction effects will be saved in a separate layer
    /// The pushed information will be lost on pop
    #[structopt(name = "push")]
    Push {
        /// Target the builder
        #[structopt(long = "builder", short = "b")]
        builder: bool,

        /// Target the executor
        #[structopt(long = "executor", short = "e", conflicts_with = "builder")]
        executor: bool,

        /// Target the symbolizer
        #[structopt(long = "symbolizer", short = "s", conflicts_with = "builder")]
        symbolizer: bool,
    },

    /// Matches push, clean up all effects caused by operations since last push.
    /// The execution will have no effect if there are more pops than pushes
    #[structopt(name = "pop")]
    Pop {
        /// Target the builder
        #[structopt(long = "builder", short = "b")]
        builder: bool,

        /// Target the executor
        #[structopt(long = "executor", short = "e", conflicts_with = "builder")]
        executor: bool,

        /// Target the symbolizer
        #[structopt(long = "symbolizer", short = "s", conflicts_with = "builder")]
        symbolizer: bool,
    },
}

pub struct MoveController {
    builder: MoveStatefulBuilder,
    executors: Vec<Option<MoveStatefulExecutor>>,
    symbolizers: Vec<Option<MoveStatefulSymbolizer>>,
}

impl MoveController {
    pub fn new(output: PathBuf) -> Result<Self> {
        fs::create_dir_all(&output)?;

        let output_sessions = output.join(OUTPUT_SESSIONS);
        fs::create_dir(&output_sessions)?;

        Ok(Self {
            builder: MoveStatefulBuilder::new(output_sessions, ())?,
            executors: vec![None],
            symbolizers: vec![None],
        })
    }

    //
    // core operations
    //

    pub fn compile<P: AsRef<Path>, A: AsRef<[P]>>(
        &mut self,
        move_src: A,
        sender: Option<Address>,
        commit: bool,
    ) -> Result<()> {
        if self.executors.last().unwrap().is_some() {
            bail!("Compilation disabled due to existence of the executor");
        }
        if self.symbolizers.last().unwrap().is_some() {
            bail!("Compilation disabled due to existence of the symbolizer");
        }
        self.builder.compile(move_src, sender, commit)
    }

    pub fn execute(
        &mut self,
        signers: &[AccountAddress],
        val_args: &[TransactionArgument],
        type_args: &[TypeTag],
        commit: bool,
    ) -> Result<()> {
        // get the script
        let mut scripts = self.builder.get_compiled_scripts_all();
        if scripts.len() != 1 {
            bail!("Expecting only one script, found {}", scripts.len());
        }
        let script = scripts.pop().unwrap();

        // execute it
        let executor = Self::get_or_create_executor(&self.builder, &mut self.executors)?;
        executor.execute_script(script, signers, val_args, type_args, commit)
    }

    pub fn symbolize(&mut self, type_args: &[TypeTag]) -> Result<()> {
        // symbolize it
        let symbolizer = Self::get_or_create_symbolizer(&self.builder, &mut self.symbolizers)?;
        symbolizer.symbolize(type_args)
    }

    pub fn push(
        &mut self,
        target_builder: bool,
        target_executor: bool,
        target_symbolizer: bool,
    ) -> Result<()> {
        if target_builder {
            self.builder.push()?;
            self.executors.push(None);
            self.symbolizers.push(None);
        }
        if target_executor {
            debug_assert!(!target_builder);
            Self::get_or_create_executor(&self.builder, &mut self.executors)?.push()?;
        }
        if target_symbolizer {
            debug_assert!(!target_builder);
            Self::get_or_create_symbolizer(&self.builder, &mut self.symbolizers)?.push()?;
        }
        Ok(())
    }

    pub fn pop(
        &mut self,
        target_builder: bool,
        target_executor: bool,
        target_symbolizer: bool,
    ) -> Result<()> {
        if target_builder {
            let executor = self.executors.pop().unwrap();
            if let Some(worker) = &executor {
                if !worker.balanced() {
                    self.executors.push(executor);
                    bail!("Cannot pop the builder because the associated executor is unbalanced");
                }
            }
            let symbolizer = self.symbolizers.pop().unwrap();
            if let Some(worker) = &symbolizer {
                if !worker.balanced() {
                    self.symbolizers.push(symbolizer);
                    bail!("Cannot pop the builder because the associated symbolizer is unbalanced");
                }
            }
            if let Err(err) = self.builder.pop() {
                self.executors.push(executor);
                self.symbolizers.push(symbolizer);
                return Err(err);
            }
        }
        if target_executor {
            debug_assert!(!target_builder);
            Self::get_or_create_executor(&self.builder, &mut self.executors)?.pop()?;
        }
        if target_symbolizer {
            debug_assert!(!target_builder);
            Self::get_or_create_symbolizer(&self.builder, &mut self.symbolizers)?.pop()?;
        }
        Ok(())
    }

    //
    // info provider
    //

    pub fn get_compilation_dependencies(&self) -> Result<Vec<String>> {
        self.builder.get_compilation_dependencies()
    }

    pub fn get_compiled_units_recent(&self) -> (Vec<&CompiledModule>, Vec<&CompiledScript>) {
        (
            self.builder.get_compiled_modules_recent(),
            self.builder.get_compiled_scripts_recent(),
        )
    }

    //
    // helpers
    //

    // this function is purposely designed not to take a &mut self to make the borrow checker happy
    fn get_or_create_executor<'a>(
        builder: &MoveStatefulBuilder,
        executors: &'a mut Vec<Option<MoveStatefulExecutor>>,
    ) -> Result<&'a mut MoveStatefulExecutor> {
        if executors.last().unwrap().is_none() {
            let worker = builder.top_worker();
            let dependent_dir = worker.playdir().join(OUTPUT_EXECUTIONS);
            fs::create_dir(&dependent_dir)?;
            let mut executor = MoveStatefulExecutor::new(dependent_dir, ())?;

            // preload the modules to the executor
            let modules = builder.get_compiled_modules_all();
            executor.preload_modules(modules.into_iter())?;
            executors.push(Some(executor));
        }
        Ok(executors.last_mut().unwrap().as_mut().unwrap())
    }

    fn get_or_create_symbolizer<'a>(
        builder: &MoveStatefulBuilder,
        symbolizers: &'a mut Vec<Option<MoveStatefulSymbolizer>>,
    ) -> Result<&'a mut MoveStatefulSymbolizer> {
        if symbolizers.last().unwrap().is_none() {
            let worker = builder.top_worker();
            let dependent_dir = worker.playdir().join(OUTPUT_SYMBOLIZATIONS);
            fs::create_dir(&dependent_dir)?;

            //
            // create the global env
            //

            // get the address
            let addresses = builder.get_sender_addresses_all();
            if addresses.len() > 1 {
                bail!(
                    "Expecting at most one sender address, found {}",
                    addresses.len()
                );
            }
            // NOTE: this address is the signer's address for the one and only script, and this
            // address is needed by `run_model_builder`
            let address = addresses.into_iter().next().map(|addr| addr.to_string());

            // build the global env
            let sources = builder.get_source_locations_all();
            let global_env =
                run_model_builder(sources.paths_to_strings()?, vec![], address.as_deref())?;

            let symbolizer = MoveStatefulSymbolizer::new(dependent_dir, global_env)?;
            symbolizers.push(Some(symbolizer));
        }
        Ok(symbolizers.last_mut().unwrap().as_mut().unwrap())
    }

    //
    // command handler
    //

    pub fn handle_command(&mut self, cmdl: &str) -> Result<()> {
        let OpArgs {
            expect_failure,
            cmd,
        } = OpArgs::from_iter(&shell_words::split(cmdl)?);

        // handle commands
        let result = match cmd {
            OpCommand::Compile {
                input,
                sender,
                dry_run,
            } => self.compile(&input, sender, !dry_run),
            OpCommand::Execute {
                signers,
                val_args,
                type_args,
                dry_run,
            } => self.execute(&signers, &val_args, &type_args, !dry_run),
            OpCommand::Symbolize { type_args } => self.symbolize(&type_args),
            OpCommand::Push {
                builder,
                executor,
                symbolizer,
            } => self.push(builder, executor, symbolizer),
            OpCommand::Pop {
                builder,
                executor,
                symbolizer,
            } => self.pop(builder, executor, symbolizer),
        };

        // check result
        if let Err(err) = result {
            if expect_failure {
                debug!("{} [x] {}", LOG_TAG, err);
                Ok(())
            } else {
                Err(err)
            }
        } else {
            if expect_failure {
                bail!("Expected failure but none reported");
            }
            Ok(())
        }
    }
}
