// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]
#![macro_use]

use anyhow::Result;
use std::{fs, path::Path};

// path
#[macro_export]
macro_rules! join_path_items {
    ($base:expr, $($item:expr),+) => {{
        let mut base: ::std::path::PathBuf = $base.into();
        $(
            base.push($item);
        )*
        base.into_os_string().into_string().unwrap()
    }}
}

// filesystem
pub fn maybe_create_dir<P: AsRef<Path>>(dir_path: P) -> Result<()> {
    if !dir_path.as_ref().exists() {
        fs::create_dir_all(&dir_path)?;
    }
    Ok(())
}

pub fn maybe_remove_dir<P: AsRef<Path>>(dir_path: P) -> Result<()> {
    if dir_path.as_ref().exists() {
        fs::remove_dir_all(&dir_path)?;
    }
    Ok(())
}

pub fn maybe_recreate_dir<P: AsRef<Path>>(dir_path: P) -> Result<()> {
    if dir_path.as_ref().exists() {
        fs::remove_dir_all(&dir_path)?;
    }
    fs::create_dir_all(&dir_path)?;
    Ok(())
}
