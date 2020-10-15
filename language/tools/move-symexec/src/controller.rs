// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use anyhow::{bail, Result};
use log::{debug, warn};
use regex::Regex;
use std::{
    collections::{HashMap, HashSet},
    fs,
};
use structopt::{clap::AppSettings, StructOpt};

use move_core_types::{
    account_address::AccountAddress,
    identifier::{IdentStr, Identifier},
    language_storage::{ModuleId, TypeTag},
    parser::{parse_transaction_argument, parse_type_tag},
    transaction_argument::TransactionArgument,
};
use move_lang::shared::Address;
use vm::{
    access::ModuleAccess,
    file_format::{CompiledModule, CompiledScript},
};

use crate::{
    builder::MoveBuilder, executor::MoveExecutor, sym_setup::SymSetup, symbolizer::MoveSymbolizer,
    utils,
};

/// Default directory containing builder workdirs
const MOVE_BUILDER_WORKDIR: &str = "builder";

/// Filters for identifiers in Move compiled units
pub struct FuncIdMatcher {
    module_addr_regex: Regex,
    module_name_regex: Regex,
    func_name_regex: Regex,
}

impl FuncIdMatcher {
    fn new(expr: &str) -> Result<Self> {
        let tokens: Vec<&str> = expr.split("::").collect();
        if tokens.len() != 3 {
            bail!("Error: invalid match expression - {}", expr);
        }
        Ok(Self {
            module_addr_regex: Regex::new(tokens[0])?,
            module_name_regex: Regex::new(tokens[1])?,
            func_name_regex: Regex::new(tokens[2])?,
        })
    }

    fn is_match(&self, module_id: &ModuleId, func_id: &IdentStr) -> bool {
        self.module_addr_regex
            .is_match(&module_id.address().to_string())
            && self.module_name_regex.is_match(&module_id.name().as_str())
            && self.func_name_regex.is_match(func_id.as_str())
    }
}

struct FuncIdMatcherList<'a> {
    matchers_opt: Option<&'a [FuncIdMatcher]>,
}

impl FuncIdMatcherList<'_> {
    fn is_match(&self, module_id: &ModuleId, func_id: &IdentStr) -> bool {
        match &self.matchers_opt {
            None => true,
            Some(matchers) => matchers.iter().any(|m| m.is_match(module_id, func_id)),
        }
    }
}

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
    /// Load pre-compiled Move modules from input paths given.
    #[structopt(name = "load")]
    Load {
        /// Directories storing compiled Move modules
        /// Modules in this directory
        ///   1. will be loaded before script execution, but
        ///   2. will not be symbolically executed,
        ///      instead, they must be statically modeled,
        ///      unless the --track option is set.
        /// Scripts are not allowed in these directories.
        #[structopt()]
        input: Vec<String>,

        /// Mark that the loaded Move modules will be tracked.
        #[structopt(long = "track", short = "t", conflicts_with = "dry-run")]
        track: bool,

        /// Mark that this operation should have no impact on future
        /// operations.
        #[structopt(long = "dry-run", short = "x")]
        dry_run: bool,
    },

    /// Compile Move source files from input paths given.
    #[structopt(name = "compile")]
    Compile {
        /// Directories storing Move source files
        /// Modules in this directory
        ///   1. will be loaded before script execution, but
        ///   2. will not be symbolically executed,
        ///      instead, they must be statically modeled,
        ///      unless the --track option is set.
        /// Scripts in this directory will be compiled and executed.
        #[structopt()]
        input: Vec<String>,

        /// Sender address, will be applied to all Move source files
        /// in this batch in compilation.
        #[structopt(long = "sender", short = "s", parse(try_from_str = Address::parse_str))]
        sender: Option<Address>,

        /// Mark that the compiled Move modules/scripts will be tracked.
        #[structopt(long = "track", short = "t", conflicts_with = "dry-run")]
        track: bool,

        /// Mark that this operation should have no impact on future
        /// operations.
        #[structopt(long = "dry-run", short = "x")]
        dry_run: bool,
    },

    /// Execute the scripts compiled and ready in state. All modules
    /// compiled will be pre-loaded before script execution. The runtime
    /// arguments will be applied to all scripts.
    #[structopt(name = "execute")]
    Execute {
        /// Possibly-empty list of signers for the current transaction
        /// (e.g., `account` in `main(&account: signer)`).
        /// Must match the number of signers expected by `script_file`.
        #[structopt(long = "signers", short = "s", parse(try_from_str = AccountAddress::from_hex_literal))]
        signers: Vec<AccountAddress>,

        /// Possibly-empty list of arguments passed to the transaction
        /// (e.g., `i` in `main(i: u64)`).
        /// Must match the arguments types expected by `script_file`.
        #[structopt(long = "val-args", short = "v", parse(try_from_str = parse_transaction_argument))]
        val_args: Vec<TransactionArgument>,

        /// Possibly-empty list of type arguments passed to the
        /// transaction (e.g., `T` in `main<T>()`).
        /// Must match the type arguments expected by `script_file`.
        #[structopt(long = "type-args", short = "t", parse(try_from_str = parse_type_tag))]
        type_args: Vec<TypeTag>,

        /// Mark that this operation should have no impact on future
        /// operations.
        #[structopt(long = "dry-run", short = "x")]
        dry_run: bool,
    },

    /// Symbolize the scripts and modules marked as tracking (filtered
    /// by inclusions and exclusions).
    #[structopt(name = "symbolize")]
    Symbolize {
        /// List of function identifiers to be included for tracking
        /// and symbolic execution.
        #[structopt(long = "inclusion", short = "i", parse(try_from_str = FuncIdMatcher::new))]
        inclusion: Option<Vec<FuncIdMatcher>>,

        /// List of function identifiers to be excluded for tracking
        /// and symbolic execution.
        #[structopt(long = "exclusion", short = "e", parse(try_from_str = FuncIdMatcher::new))]
        exclusion: Vec<FuncIdMatcher>,
    },

    /// Push the execution stack, modules and scripts compiled will be
    /// saved in a separate layer of variables and their information
    /// will be lost on pop.
    #[structopt(name = "push")]
    Push,

    /// Matches push, clean up all effects caused by operations since
    /// last push. The execution will have no effect if there are more
    /// pops than pushes.
    #[structopt(name = "pop")]
    Pop,
}

/// Compilation units with additional marking and information
#[derive(Clone, Debug, Eq, PartialEq)]
struct MarkedModule {
    module: CompiledModule,
    track: bool,
}

impl MarkedModule {
    fn filter(&self, track_opt: Option<bool>) -> Option<&CompiledModule> {
        match track_opt {
            None => Some(&self.module),
            Some(v) => {
                if self.track == v {
                    Some(&self.module)
                } else {
                    None
                }
            }
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct MarkedScript {
    script: CompiledScript,
    track: bool,
}

impl MarkedScript {
    fn filter(&self, track_opt: Option<bool>) -> Option<&CompiledScript> {
        match track_opt {
            None => Some(&self.script),
            Some(v) => {
                if self.track == v {
                    Some(&self.script)
                } else {
                    None
                }
            }
        }
    }
}

/// Holds the current state
struct OpState {
    builder: MoveBuilder,
    executor: MoveExecutor,
    compiled_modules: Vec<MarkedModule>,
    compiled_scripts: Vec<MarkedScript>,
}

/// A stateful controller to run multiple operations on Move programs
pub struct MoveController {
    workdir: String,
    workdir_builder: String,
    op_stack: Vec<OpState>,
    num_contexts: usize,
    clean_on_destroy: bool,
}

impl MoveController {
    pub fn new(workdir: String, clean_on_destroy: bool) -> Result<Self> {
        // prepare the directory
        let workdir_builder = join_path_items!(&workdir, MOVE_BUILDER_WORKDIR);
        utils::maybe_recreate_dir(&workdir)?;
        fs::create_dir_all(&workdir_builder)?;

        // create the initial state
        let state = OpState {
            builder: MoveBuilder::new(
                join_path_items!(&workdir_builder, "0"),
                None,
                clean_on_destroy,
            )?,
            executor: MoveExecutor::new(&[]),
            compiled_modules: vec![],
            compiled_scripts: vec![],
        };

        // done
        Ok(Self {
            workdir,
            workdir_builder,
            op_stack: vec![state],
            num_contexts: 1,
            clean_on_destroy,
        })
    }

    // helper functions
    fn get_state(&self) -> &OpState {
        self.op_stack.last().unwrap()
    }

    fn get_state_mut(&mut self) -> &mut OpState {
        self.op_stack.last_mut().unwrap()
    }

    // core operations
    pub fn load(&mut self, move_bin: &[String], track: bool, commit: bool) -> Result<()> {
        let state = self.get_state_mut();

        let modules = state.builder.load_modules(move_bin, commit)?;
        debug!("{} module(s) loaded", modules.len());

        if commit {
            state.executor.preload_modules(&modules);
            state.compiled_modules.extend(
                modules
                    .into_iter()
                    .map(|module| MarkedModule { module, track }),
            );
        }

        Ok(())
    }

    pub fn compile(
        &mut self,
        move_src: &[String],
        sender: Option<Address>,
        track: bool,
        commit: bool,
    ) -> Result<()> {
        let state = self.get_state_mut();

        let (modules, scripts) = state.builder.compile(move_src, sender, commit)?;
        debug!(
            "{} module(s) + {} script(s) compiled",
            modules.len(),
            scripts.len()
        );

        if commit {
            state.executor.preload_modules(&modules);
            state.compiled_modules.extend(
                modules
                    .into_iter()
                    .map(|module| MarkedModule { module, track }),
            );
            state.compiled_scripts.extend(
                scripts
                    .into_iter()
                    .map(|script| MarkedScript { script, track }),
            );
        }

        Ok(())
    }

    pub fn execute(
        &mut self,
        signers: &[AccountAddress],
        val_args: &[TransactionArgument],
        type_args: &[TypeTag],
        commit: bool,
    ) -> Result<()> {
        let compiled_scripts = self.get_compiled_scripts_all(None);

        let state = self.get_state_mut();
        for script in compiled_scripts.iter() {
            state
                .executor
                .execute_script(script, signers, val_args, type_args, commit)?;
        }

        Ok(())
    }

    pub fn symbolize(
        &self,
        inclusion: Option<&[FuncIdMatcher]>,
        exclusion: Option<&[FuncIdMatcher]>,
    ) -> Result<()> {
        // build the setup
        let tracked_scripts = self.get_compiled_scripts_all(Some(true));
        let tracked_modules = self.get_compiled_modules_all(Some(true));
        let sym_setup =
            SymSetup::new(self.collect_tracked_functions(&tracked_modules, inclusion, exclusion));
        debug!(
            "{} functions to be tracked symbolically",
            sym_setup.num_tracked_functions()
        );

        // symbolize each script one by one
        for script in tracked_scripts.iter() {
            let _symbolizer = MoveSymbolizer::new(script, &tracked_modules, &sym_setup);
        }

        // done
        Ok(())
    }

    // stack operations
    pub fn push(&mut self) -> Result<()> {
        let old_state = self.get_state();
        let new_state = OpState {
            builder: MoveBuilder::new(
                join_path_items!(&self.workdir_builder, self.num_contexts.to_string()),
                Some(&old_state.builder),
                self.clean_on_destroy,
            )?,
            executor: old_state.executor.clone(),
            compiled_modules: vec![],
            compiled_scripts: vec![],
        };
        self.op_stack.push(new_state);
        self.num_contexts += 1;
        Ok(())
    }

    pub fn pop(&mut self) -> Result<()> {
        if self.op_stack.len() == 1 {
            bail!("More pops than push?");
        } else {
            self.op_stack.pop();
        }
        Ok(())
    }

    // get results (maybe across stack)
    pub fn get_compiled_units_recent(
        &self,
        track_opt: Option<bool>,
    ) -> (Vec<CompiledModule>, Vec<CompiledScript>) {
        let state = self.get_state();
        (
            state
                .compiled_modules
                .iter()
                .filter_map(|m| m.filter(track_opt))
                .cloned()
                .collect(),
            state
                .compiled_scripts
                .iter()
                .filter_map(|s| s.filter(track_opt))
                .cloned()
                .collect(),
        )
    }

    fn get_compiled_modules_all(&self, track_opt: Option<bool>) -> Vec<CompiledModule> {
        self.op_stack
            .iter()
            .map(|state| state.compiled_modules.iter())
            .flatten()
            .filter_map(|m| m.filter(track_opt))
            .cloned()
            .collect()
    }

    fn get_compiled_scripts_all(&self, track_opt: Option<bool>) -> Vec<CompiledScript> {
        self.op_stack
            .iter()
            .map(|state| state.compiled_scripts.iter())
            .flatten()
            .filter_map(|s| s.filter(track_opt))
            .cloned()
            .collect()
    }

    // identifier filtering
    fn collect_tracked_functions(
        &self,
        tracked_modules: &[CompiledModule],
        inclusion: Option<&[FuncIdMatcher]>,
        exclusion: Option<&[FuncIdMatcher]>,
    ) -> HashMap<ModuleId, HashSet<Identifier>> {
        // build filters
        let inc_matcher = FuncIdMatcherList {
            matchers_opt: inclusion,
        };
        let exc_matcher = FuncIdMatcherList {
            matchers_opt: exclusion,
        };

        // filter through the inclusion matchers
        let mut included_functions: HashMap<ModuleId, HashSet<Identifier>> = HashMap::new();
        for module in tracked_modules {
            let module_id = module.self_id();
            let func_set = module
                .function_defs()
                .iter()
                .filter_map(|func_def| {
                    let handle = module.function_handle_at(func_def.function);
                    let func_id = module.identifier_at(handle.name);
                    if inc_matcher.is_match(&module_id, func_id) {
                        Some(func_id.to_owned())
                    } else {
                        None
                    }
                })
                .collect();

            if included_functions
                .insert(module.self_id(), func_set)
                .is_some()
            {
                warn!("Duplication of compiled modules: {}", module.self_id());
            }
        }

        // filter through the exclusion matchers
        let mut tracked_functions = HashMap::new();
        for (module_id, func_set) in included_functions.into_iter() {
            let filtered_set: HashSet<Identifier> = func_set
                .into_iter()
                .filter(|func_id| !exc_matcher.is_match(&module_id, &func_id))
                .collect();

            if !filtered_set.is_empty() {
                tracked_functions.insert(module_id, filtered_set);
            }
        }

        // done
        tracked_functions
    }

    // command handling
    pub fn handle(&mut self, cmdl: &str) -> Result<()> {
        let args = OpArgs::from_iter(&shell_words::split(cmdl)?);

        // handle commands
        match args.cmd {
            OpCommand::Load {
                input,
                track,
                dry_run,
            } => self.load(&input, track, !dry_run),
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
                dry_run,
            } => self.execute(&signers, &val_args, &type_args, !dry_run),
            OpCommand::Symbolize {
                inclusion,
                exclusion,
            } => self.symbolize(inclusion.as_deref(), Some(&exclusion)),
            OpCommand::Push => self.push(),
            OpCommand::Pop => self.pop(),
        }
    }
}

impl Drop for MoveController {
    fn drop(&mut self) {
        if self.clean_on_destroy {
            utils::maybe_remove_dir(&self.workdir).unwrap_or_else(|_| {
                panic!(
                    "Unable to remove workdir for Move controller: {}",
                    &self.workdir
                )
            });
        }
    }
}
