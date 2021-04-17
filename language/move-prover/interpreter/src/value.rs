// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use move_core_types::{
    account_address::AccountAddress,
    value::{MoveStruct, MoveValue},
};

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum SpecValue {
    Obj(MoveValue),
    Ref(MoveValue),
}

impl SpecValue {
    pub fn into_bool(self) -> Result<bool, Self> {
        match self {
            SpecValue::Obj(MoveValue::Bool(v)) => Ok(v),
            e => Err(e),
        }
    }

    pub fn into_u8(self) -> Result<u8, Self> {
        match self {
            SpecValue::Obj(MoveValue::U8(v)) => Ok(v),
            e => Err(e),
        }
    }

    pub fn into_u64(self) -> Result<u64, Self> {
        match self {
            SpecValue::Obj(MoveValue::U64(v)) => Ok(v),
            e => Err(e),
        }
    }

    pub fn into_u128(self) -> Result<u128, Self> {
        match self {
            SpecValue::Obj(MoveValue::U128(v)) => Ok(v),
            e => Err(e),
        }
    }

    pub fn into_address(self) -> Result<AccountAddress, Self> {
        match self {
            SpecValue::Obj(MoveValue::Address(v)) => Ok(v),
            e => Err(e),
        }
    }

    pub fn into_signer(self) -> Result<AccountAddress, Self> {
        match self {
            SpecValue::Obj(MoveValue::Signer(v)) => Ok(v),
            e => Err(e),
        }
    }

    pub fn into_struct(self) -> Result<MoveStruct, Self> {
        match self {
            SpecValue::Obj(MoveValue::Struct(v)) => Ok(v),
            e => Err(e),
        }
    }
}
