// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use anyhow::{bail, Result};
use log::{debug, error, warn};
use std::{
    fs,
    path::{Path, PathBuf},
};
use tempfile::tempdir;

use move_core_types::{
    account_address::AccountAddress,
    gas_schedule::{GasAlgebra, GasUnits},
    language_storage::TypeTag,
    transaction_argument::TransactionArgument,
};
use move_lang::{self, compiled_unit::CompiledUnit, MOVE_COMPILED_EXTENSION};
use move_vm_runtime::{logging::NoContextLog, move_vm::MoveVM};
use move_vm_types::{gas_schedule::CostStrategy, values::Value};
use vm::{file_format::CompiledScript, CompiledModule};
use vm_genesis::genesis_gas_schedule::INITIAL_GAS_SCHEDULE;

use crate::{exec_graph::ExecGraph, state_view::InMemoryStateView, sym_config::SymConfig, utils};

fn load_modules(module_bin: &[String], move_output: &str) -> Result<Vec<CompiledModule>> {
    // generate interfaces
    move_lang::generate_interface_files(module_bin, Some(move_output.to_owned()), false)?;

    // load
    let compiled_modules = move_lang::find_filenames(module_bin, |fpath| {
        match fpath.extension().and_then(|s| s.to_str()) {
            None => false,
            Some(ext) => ext == MOVE_COMPILED_EXTENSION,
        }
    })?
    .iter()
    .map(|entry| {
        CompiledModule::deserialize(
            &fs::read(Path::new(entry)).expect("Error: unable to compiled module file"),
        )
        .expect("Error: unable to deserialize compiled module")
    })
    .collect();

    // done
    Ok(compiled_modules)
}

fn compile(
    move_src: &[String],
    move_output: &str,
) -> Result<(Vec<CompiledModule>, Vec<CompiledScript>)> {
    let deps = utils::path_interface_dir(move_output)?;

    // compile
    let (files, compiled_units) = move_lang::move_compile(move_src, &deps, None, None)?;

    // collect modules and scripts
    let mut compiled_modules = vec![];
    let mut compiled_scripts = vec![];
    for unit in compiled_units.iter() {
        match unit {
            CompiledUnit::Script { script, .. } => {
                compiled_scripts.push(script.clone());
            }
            CompiledUnit::Module { module, .. } => {
                compiled_modules.push(module.clone());
            }
        }
    }

    // filter out scripts from compiled units
    let compiled_units_modules = compiled_units
        .into_iter()
        .filter(|unit| match unit {
            CompiledUnit::Script { .. } => false,
            CompiledUnit::Module { .. } => true,
        })
        .collect();

    // generate interfaces
    let mv_dir = tempdir()?;
    let mv_dir_path = mv_dir.path().to_str().unwrap();
    move_lang::output_compiled_units(false, files, compiled_units_modules, mv_dir_path)?;
    move_lang::generate_interface_files(
        &[mv_dir_path.to_owned()],
        Some(move_output.to_owned()),
        false,
    )?;

    // done
    Ok((compiled_modules, compiled_scripts))
}

fn execute_script(
    script: &CompiledScript,
    modules: &[CompiledModule],
    signers: &[AccountAddress],
    val_args: &[TransactionArgument],
    type_args: &[TypeTag],
) -> Result<()> {
    // serialize script
    let mut script_bytes = vec![];
    script.serialize(&mut script_bytes)?;

    // load modules
    let state = InMemoryStateView::new(modules)?;

    // convert args to values
    let exec_args: Vec<Value> = val_args
        .iter()
        .map(|arg| match arg {
            TransactionArgument::U8(i) => Value::u8(*i),
            TransactionArgument::U64(i) => Value::u64(*i),
            TransactionArgument::U128(i) => Value::u128(*i),
            TransactionArgument::Address(a) => Value::address(*a),
            TransactionArgument::Bool(b) => Value::bool(*b),
            TransactionArgument::U8Vector(v) => Value::vector_u8(v.clone()),
        })
        .collect();

    // init setup
    let log_context = NoContextLog::new();
    let mut cost_strategy = CostStrategy::system(&INITIAL_GAS_SCHEDULE, GasUnits::new(0));

    // execution
    let vm = MoveVM::new();

    let mut session = vm.new_session(&state);
    let result = session.execute_script(
        script_bytes,
        type_args.to_owned(),
        exec_args,
        signers.to_owned(),
        &mut cost_strategy,
        &log_context,
    );

    // handle errors
    if let Err(err) = result {
        error!("{}", err);
        bail!("Error: failed to execute the script!");
    };

    // collect effects
    match session.finish() {
        Ok(effects) => {
            debug!(
                "Script executed - modules: {}, resources: {}, events: {}",
                effects.modules.len(),
                effects.resources.len(),
                effects.events.len(),
            );
            // effects are discarded and not commited to states
            Ok(())
        }
        Err(err) => {
            error!("{}", err);
            bail!("Error: failed to collect effects from script execution")
        }
    }
}

pub fn run(
    config_file_opt: Option<&String>,
    signers: &[AccountAddress],
    val_args: &[TransactionArgument],
    type_args: &[TypeTag],
    move_src: &[String],
    move_lib: &[String],
    move_sys: &[String],
    build_stdlib: bool,
    track_stdlib: bool,
    move_data: &str,
    move_output: &str,
    post_run_cleaning: bool,
) -> Result<()> {
    // directory preparation
    let path_move_data = PathBuf::from(move_data);
    let path_move_output = PathBuf::from(move_output);
    utils::maybe_recreate_dir(&path_move_data)?;
    utils::maybe_recreate_dir(&path_move_output)?;

    // load/compile modules and expose interfaces
    let sys_modules = if build_stdlib {
        let (modules, scripts) = compile(move_sys, move_output)?;
        if !scripts.is_empty() {
            warn!(
                "{} scripts ignored when compiling sys modules",
                scripts.len()
            );
        }
        debug!("{} sys module(s) compiled", modules.len());
        modules
    } else {
        let modules = load_modules(move_sys, move_output)?;
        debug!("{} sys module(s) loaded", modules.len());
        modules
    };

    // compile libraries
    let (lib_modules, lib_scripts) = compile(move_lib, move_output)?;
    if !lib_scripts.is_empty() {
        warn!(
            "{} scripts ignored when compiling lib modules",
            lib_scripts.len()
        );
    }
    debug!("{} lib module(s) compiled", lib_modules.len());

    // compile sources
    let (src_modules, src_scripts) = compile(move_src, move_output)?;
    debug!("{} src module(s) compiled", src_modules.len());
    debug!("{} src script(s) compiled", src_scripts.len());

    if let Some(config_file) = config_file_opt {
        // collect modules to track
        let sym_modules = if track_stdlib {
            [sys_modules, src_modules].concat()
        } else {
            src_modules
        };

        // parse config file
        let config = SymConfig::new(&config_file, &sym_modules)?;
        debug!(
            "Config parsed: {} function(s) to be tracked",
            config.num_tracked_functions()
        );

        // execute each script symbolically
        for script in src_scripts {
            // build an execution graph that encloses both script and
            // module CFGs, i.e., a super graph that has CFGs connected
            // by the call graph
            ExecGraph::new(&config, &script, &sym_modules);
        }
    } else {
        // if no config file specified, execute each script concretely
        let modules = [sys_modules, lib_modules, src_modules].concat();
        for script in src_scripts {
            execute_script(&script, &modules, signers, val_args, type_args)?;
        }
    }

    // cleaning
    if post_run_cleaning {
        utils::maybe_remove_dir(&path_move_data)?;
        utils::maybe_remove_dir(&path_move_output)?;
    }

    // done
    Ok(())
}
