// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use anyhow::{bail, Result};
use log::{debug, error, warn};
use std::{
    fs,
    path::{Path, PathBuf},
};

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

use crate::{state_view::InMemoryStateView, utils};

fn load_modules(path: &[String]) -> Result<Vec<CompiledModule>> {
    Ok(move_lang::find_filenames(path, |fpath| {
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
    .collect())
}

fn compile_modules(
    module_src: &[String],
    module_lib: &[String],
    systemlibs: &[String],
    move_output: &str,
) -> Result<Vec<CompiledModule>> {
    let path_interface_dir = utils::path_interface_dir(move_output)?;
    let (_, compiled_units) = move_lang::move_compile(
        module_src,
        &[module_lib, systemlibs].concat(),
        None,
        Some(path_interface_dir.into_os_string().into_string().unwrap()),
    )?;

    let mut compiled_modules = vec![];
    for unit in compiled_units {
        match unit {
            CompiledUnit::Script { loc, .. } => warn!(
                "Warning: found a script during module compilation: {}. \
                The script will not be involved in symbolic execution.",
                loc.file(),
            ),
            CompiledUnit::Module { module, .. } => {
                compiled_modules.push(module);
            }
        }
    }
    Ok(compiled_modules)
}

fn compile_script(
    script_file: &str,
    module_src: &[String],
    module_lib: &[String],
    libsymexec: &[String],
    systemlibs: &[String],
    move_output: &str,
) -> Result<CompiledScript> {
    let path_interface_dir = utils::path_interface_dir(move_output)?;
    let (_, compiled_units) = move_lang::move_compile(
        &[script_file.to_owned()],
        &[module_src, module_lib, libsymexec, systemlibs].concat(),
        None,
        Some(path_interface_dir.into_os_string().into_string().unwrap()),
    )?;

    let mut compiled_script = None;
    for unit in compiled_units {
        match unit {
            CompiledUnit::Script { script, .. } => {
                if compiled_script.is_some() {
                    bail!("Error: found more than one script!");
                }
                compiled_script = Some(script);
            }
            CompiledUnit::Module { ident, .. } => warn!(
                "Warning: found a module during script compilation: {}. \
                The module will not be involved in symbolic execution.",
                ident,
            ),
        }
    }

    match compiled_script {
        None => bail!("Error: no scripts found!"),
        Some(script) => Ok(script),
    }
}

fn execute_script(
    script: &CompiledScript,
    src_modules: &[CompiledModule],
    lib_modules: &[CompiledModule],
    libsymexec_modules: &[CompiledModule],
    systemlibs_modules: &[CompiledModule],
    signers: &[AccountAddress],
    val_args: &[TransactionArgument],
    type_args: &[TypeTag],
) -> Result<()> {
    // serialize script
    let mut script_bytes = vec![];
    script.serialize(&mut script_bytes)?;

    // load modules
    let state = InMemoryStateView::new(
        &[
            src_modules,
            lib_modules,
            libsymexec_modules,
            systemlibs_modules,
        ]
        .concat(),
    )?;

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

    // collect effects;
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
    script_file: &str,
    signers: &[AccountAddress],
    val_args: &[TransactionArgument],
    type_args: &[TypeTag],
    move_src: &[String],
    move_lib: &[String],
    move_libsymexec: &[String],
    move_sysdeps_src: &[String],
    move_sysdeps_bin: &[String],
    move_data: &str,
    move_output: &str,
    post_run_cleaning: bool,
) -> Result<()> {
    // directory preparation
    let path_move_data = PathBuf::from(move_data);
    let path_move_output = PathBuf::from(move_output);
    utils::maybe_recreate_dir(&path_move_data)?;
    utils::maybe_recreate_dir(&path_move_output)?;

    // prepare system modules
    let pre_built_modules = load_modules(move_sysdeps_bin)?;
    debug!("{} systemlibs module(s) loaded", pre_built_modules.len());

    let on_demand_modules = compile_modules(move_sysdeps_src, &[], move_sysdeps_bin, move_output)?;
    debug!("{} systemlibs module(s) compiled", on_demand_modules.len());

    let move_systemlibs = &[move_sysdeps_src, move_sysdeps_bin].concat();
    let systemlibs_modules = [pre_built_modules, on_demand_modules].concat();

    // prepare symexec-related modules
    let libsymexec_modules = compile_modules(move_libsymexec, &[], &[], move_output)?;
    debug!("{} libsymexec module(s) compiled", libsymexec_modules.len());

    // prepare local modules and scripts
    let lib_modules = compile_modules(move_lib, &[], move_systemlibs, move_output)?;
    debug!("{} lib module(s) compiled", lib_modules.len());

    let src_modules = compile_modules(move_src, move_lib, move_systemlibs, move_output)?;
    debug!("{} src module(s) compiled", src_modules.len());

    let script = compile_script(
        script_file,
        move_src,
        move_lib,
        move_libsymexec,
        move_systemlibs,
        move_output,
    )?;
    debug!("Script compiled");

    // execute script
    execute_script(
        &script,
        &src_modules,
        &lib_modules,
        &libsymexec_modules,
        &systemlibs_modules,
        signers,
        val_args,
        type_args,
    )?;

    // cleaning
    if post_run_cleaning {
        utils::maybe_remove_dir(&path_move_data)?;
        utils::maybe_remove_dir(&path_move_output)?;
    }

    // done
    Ok(())
}
