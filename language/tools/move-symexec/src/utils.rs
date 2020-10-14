// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use anyhow::Result;
use std::{
    fs,
    path::{Path, PathBuf},
};

pub const MOVE_COMPILED_INTERFACES_DIR: &str = "mv_interfaces";

// helpers
pub fn path_components_to_string(components: &[&str]) -> String {
    components
        .iter()
        .collect::<PathBuf>()
        .into_os_string()
        .into_string()
        .unwrap()
}

// paths
pub fn maybe_create_dir(dir_name: &PathBuf) -> Result<()> {
    let dir = Path::new(dir_name);
    if !dir.exists() {
        fs::create_dir_all(dir)?;
    }
    Ok(())
}

pub fn maybe_remove_dir(dir_name: &PathBuf) -> Result<()> {
    let dir = Path::new(dir_name);
    if dir.exists() {
        fs::remove_dir_all(dir)?;
    }
    Ok(())
}

pub fn maybe_recreate_dir(dir_name: &PathBuf) -> Result<()> {
    let dir = Path::new(dir_name);
    if dir.exists() {
        fs::remove_dir_all(dir)?;
    }
    fs::create_dir_all(dir)?;
    Ok(())
}

pub fn path_interface_dir(move_output: &str) -> Result<Vec<String>> {
    let mut path = PathBuf::from(move_output);
    path.push(MOVE_COMPILED_INTERFACES_DIR);
    maybe_create_dir(&path)?;
    Ok(vec![path.into_os_string().into_string().unwrap()])
}
