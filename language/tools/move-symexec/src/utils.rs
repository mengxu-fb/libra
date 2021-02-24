// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, Result};
use std::path::Path;

//
// path to string conversion
//

pub trait PathToString {
    fn path_to_string(&self) -> Result<String>;
}

impl<P: AsRef<Path>> PathToString for P {
    fn path_to_string(&self) -> Result<String> {
        self.as_ref()
            .to_path_buf()
            .into_os_string()
            .into_string()
            .map_err(|s| anyhow!("Unicode string conversion failed: '{:?}'", s))
    }
}

pub trait PathsToStrings<P> {
    fn paths_to_strings(&self) -> Result<Vec<String>>;
}

impl<P: PathToString, A: AsRef<[P]>> PathsToStrings<P> for A {
    fn paths_to_strings(&self) -> Result<Vec<String>> {
        self.as_ref()
            .iter()
            .map(|path| path.path_to_string())
            .collect()
    }
}
