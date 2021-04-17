// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use bytecode::{
    function_target::FunctionTarget,
    function_target_pipeline::FunctionVariant,
    stackless_bytecode::{Bytecode, Label},
};
use move_core_types::vm_status::StatusCode;
use move_model::{
    ast::TempIndex,
    model::{
        AbilitySet, FunId, FunctionEnv, GetNameString, GlobalEnv, QualifiedId, StructEnv, StructId,
    },
    ty::{Type, TypeDisplayContext},
};
use vm::errors::PartialVMError;

use crate::value::SpecValue;

const INVARIANT_ERROR: StatusCode = StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR;

#[repr(u64)]
#[allow(non_camel_case_types)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub enum ErrorSubCode {
    // We don't want the default value to be valid
    UNKNOWN_ERROR_SUB_CODE = 0,

    // Function not found in the environment
    ENV_FUNCTION_LOOKUP_FAILURE,
    // Struct not found in the environment
    ENV_STRUCT_LOOKUP_FAILURE,

    // Unable to find the baseline version of function target
    NO_BASELINE_VARIANT,
    // Discrepancy between execution results
    DISCREPANCIES_BETWEEN_VARIANTS,

    // Number of locals is less than the number of arguments
    LOCAL_COUNT_LESS_THAN_ARGUMENT_COUNT,
    // Accessing a local slot beyond the total count
    LOCAL_ACCESS_OUT_OF_BOUND,
    // Using a local slot after removal
    LOCAL_USE_AFTER_MOVE,
    // The local type does not match with the value in the slot
    LOCAL_TYPE_MISMATCH,

    // Argument count mismatch
    ARGUMENT_COUNT_MISMATCH,

    // Type argument count mismatch
    TYPE_ARGUMENT_COUNT_MISMATCH_FOR_FUNCTION,
    TYPE_ARGUMENT_COUNT_MISMATCH_FOR_STRUCT,
    // Type argument is invalid (in the context of function type param)
    TYPE_ARGUMENT_INVALID_FOR_FUNCTION,
    TYPE_ARGUMENT_INVALID_FOR_STRUCT,
    // Type argument constraints are not satisfied
    TYPE_ARGUMENT_CONSTRAINTS_NOT_SATISFIED_FOR_FUNCTION,
    TYPE_ARGUMENT_CONSTRAINTS_NOT_SATISFIED_FOR_STRUCT,
    // Accessing a type argument beyond the total count
    TYPE_ARGUMENT_ACCESS_OUT_OF_BOUND_FOR_FUNCTION,
    TYPE_ARGUMENT_ACCESS_OUT_OF_BOUND_FOR_STRUCT,

    // The number of srcs does not match the semantics of the bytecode
    BYTECODE_OPERAND_SRC_COUNT_MISMATCH,
    // The number of dsts does not match the semantics of the bytecode
    BYTECODE_OPERAND_DST_COUNT_MISMATCH,
    // The src operand type does not match with the semantics of the bytecode
    BYTECODE_OPERAND_SRC_TYPE_MISMATCH,
    // The dst operand type does not match with the semantics of the bytecode
    BYTECODE_OPERAND_DST_TYPE_MISMATCH,
    // The label to offset mapping is corrupted
    BYTECODE_LABEL_INVALID,

    // Function already terminated
    FUNCTION_ALREADY_TERMINATED,
    // Function not terminated but control transfer goes back
    FUNCTION_NOT_TERMINATED,

    // Return value count mismatch
    RETURN_VALUE_COUNT_MISMATCH,

    // Aborted with invalid type for the status code
    ABORT_VALUE_TYPE_MISMATCH,
    // Abort action specified at a instruction that cannot be aborted
    ABORT_ACTION_UNEXPECTED,
}

impl ErrorSubCode {
    //
    // Errors related to the environment in general
    //

    pub fn env_function_lookup_failure(env: &GlobalEnv, qid: QualifiedId<FunId>) -> PartialVMError {
        PartialVMError::new(INVARIANT_ERROR)
            .with_sub_status(ErrorSubCode::ENV_FUNCTION_LOOKUP_FAILURE as u64)
            .with_message(format!(
                "Failed to lookup function with id `{}` in the environment",
                qid.get_name_for_display(env)
            ))
    }

    pub fn env_struct_lookup_failure(
        env: &GlobalEnv,
        qid: QualifiedId<StructId>,
    ) -> PartialVMError {
        PartialVMError::new(INVARIANT_ERROR)
            .with_sub_status(ErrorSubCode::ENV_STRUCT_LOOKUP_FAILURE as u64)
            .with_message(format!(
                "Failed to lookup struct with id `{}` in the environment",
                qid.get_name_for_display(env)
            ))
    }

    //
    // Errors related to function variants
    //

    pub fn no_baseline_variant(fun_env: &FunctionEnv<'_>) -> PartialVMError {
        PartialVMError::new(INVARIANT_ERROR)
            .with_sub_status(ErrorSubCode::NO_BASELINE_VARIANT as u64)
            .with_message(format!(
                "[{}] unable to find the baseline variant for the function target`",
                fun_env.get_full_name_str()
            ))
    }

    pub fn discrepancies_between_variants(
        fun_env: &FunctionEnv<'_>,
        variant: &FunctionVariant,
    ) -> PartialVMError {
        PartialVMError::new(INVARIANT_ERROR)
            .with_sub_status(ErrorSubCode::DISCREPANCIES_BETWEEN_VARIANTS as u64)
            .with_message(format!(
                "[{}] discrepancies in execution results for the function target \
                between variants `{}` and `{}`",
                fun_env.get_full_name_str(),
                &FunctionVariant::Baseline,
                variant
            ))
    }

    //
    // Errors related to local slots
    //

    pub fn local_count_less_than_argument_count(
        fun_target: &FunctionTarget,
        arg_count: usize,
    ) -> PartialVMError {
        PartialVMError::new(INVARIANT_ERROR)
            .with_sub_status(ErrorSubCode::LOCAL_COUNT_LESS_THAN_ARGUMENT_COUNT as u64)
            .with_message(format!(
                "[{}] expect at least {} slots in local state, got {}",
                fun_target.func_env.get_full_name_str(),
                arg_count,
                fun_target.get_local_count(),
            ))
    }

    pub fn local_access_out_of_bound(
        fun_target: &FunctionTarget,
        index: TempIndex,
    ) -> PartialVMError {
        PartialVMError::new(INVARIANT_ERROR)
            .with_sub_status(ErrorSubCode::LOCAL_ACCESS_OUT_OF_BOUND as u64)
            .with_message(format!(
                "[{}] local slot access out of bound (index {}, total {})",
                fun_target.func_env.get_full_name_str(),
                index,
                fun_target.get_local_count()
            ))
    }

    pub fn local_use_after_move(fun_target: &FunctionTarget, index: TempIndex) -> PartialVMError {
        PartialVMError::new(INVARIANT_ERROR)
            .with_sub_status(ErrorSubCode::LOCAL_USE_AFTER_MOVE as u64)
            .with_message(format!(
                "[{}] using local slot after it is moved or before it is initialized (index {})",
                fun_target.func_env.get_full_name_str(),
                index
            ))
    }

    pub fn local_type_mismatch(
        fun_target: &FunctionTarget,
        index: TempIndex,
        val: &SpecValue,
        ty: &Type,
    ) -> PartialVMError {
        PartialVMError::new(INVARIANT_ERROR)
            .with_sub_status(ErrorSubCode::LOCAL_TYPE_MISMATCH as u64)
            .with_message(format!(
                "[{}] expect a value of type {} for local slot {}, got {:?}",
                fun_target.func_env.get_full_name_str(),
                ty.display(&Self::get_type_display_context(fun_target)),
                index,
                val
            ))
    }

    //
    // Errors related to arguments
    //

    pub fn argument_count_mismatch(
        fun_target: &FunctionTarget,
        arg_count: usize,
    ) -> PartialVMError {
        PartialVMError::new(INVARIANT_ERROR)
            .with_sub_status(ErrorSubCode::ARGUMENT_COUNT_MISMATCH as u64)
            .with_message(format!(
                "[{}] expect {} arguments, got {}",
                fun_target.func_env.get_full_name_str(),
                fun_target.get_parameter_count(),
                arg_count
            ))
    }

    //
    // Errors related to type arguments
    //

    pub fn type_argument_count_mismatch_for_function(
        fun_target: &FunctionTarget,
        arg_count: usize,
    ) -> PartialVMError {
        PartialVMError::new(INVARIANT_ERROR)
            .with_sub_status(ErrorSubCode::TYPE_ARGUMENT_COUNT_MISMATCH_FOR_FUNCTION as u64)
            .with_message(format!(
                "[{}] expect {} type arguments, got {}",
                fun_target.func_env.get_full_name_str(),
                fun_target.get_type_parameters().len(),
                arg_count
            ))
    }

    pub fn type_argument_count_mismatch_for_struct(
        fun_target: &FunctionTarget,
        struct_env: &StructEnv,
        arg_count: usize,
    ) -> PartialVMError {
        PartialVMError::new(INVARIANT_ERROR)
            .with_sub_status(ErrorSubCode::TYPE_ARGUMENT_COUNT_MISMATCH_FOR_STRUCT as u64)
            .with_message(format!(
                "[{}] struct `{}` instantiation expects {} type arguments, got {}",
                fun_target.func_env.get_full_name_str(),
                struct_env.get_full_name_str(),
                fun_target.get_type_parameters().len(),
                arg_count
            ))
    }

    pub fn type_argument_invalid_for_function(
        fun_target: &FunctionTarget,
        index: usize,
        ty_arg: &Type,
    ) -> PartialVMError {
        let ty_params = fun_target.get_type_parameters();
        let ty_param = ty_params.get(index).unwrap();
        PartialVMError::new(INVARIANT_ERROR)
            .with_sub_status(ErrorSubCode::TYPE_ARGUMENT_INVALID_FOR_FUNCTION as u64)
            .with_message(format!(
                "[{}] type argument `{}` is invalid: {}",
                fun_target.func_env.get_full_name_str(),
                fun_target.global_env().symbol_pool().string(ty_param.0),
                ty_arg.display(&Self::get_type_display_context(fun_target))
            ))
    }

    pub fn type_argument_invalid_for_struct(
        fun_target: &FunctionTarget,
        struct_env: &StructEnv,
        index: usize,
        ty_arg: &Type,
    ) -> PartialVMError {
        let ty_params = fun_target.get_type_parameters();
        let ty_param = ty_params.get(index).unwrap();
        PartialVMError::new(INVARIANT_ERROR)
            .with_sub_status(ErrorSubCode::TYPE_ARGUMENT_INVALID_FOR_STRUCT as u64)
            .with_message(format!(
                "[{}] in instantiation of struct `{}`, type argument `{}` is invalid: {}",
                fun_target.func_env.get_full_name_str(),
                struct_env.get_full_name_str(),
                fun_target.global_env().symbol_pool().string(ty_param.0),
                ty_arg.display(&Self::get_type_display_context(fun_target))
            ))
    }

    pub fn type_argument_constraints_not_satisfied_for_function(
        fun_target: &FunctionTarget,
        index: usize,
        ty_arg: &Type,
    ) -> PartialVMError {
        let ty_params = fun_target.get_type_parameters();
        let ty_param = ty_params.get(index).unwrap();
        let ability_tokens = Self::get_ability_tokens(ty_param.1 .0);
        let ability_suffix = if ability_tokens.is_empty() {
            "".to_owned()
        } else {
            ability_tokens.join(", ")
        };
        PartialVMError::new(INVARIANT_ERROR)
            .with_sub_status(
                ErrorSubCode::TYPE_ARGUMENT_CONSTRAINTS_NOT_SATISFIED_FOR_FUNCTION as u64,
            )
            .with_message(format!(
                "[{}] constraints on type argument `{}{}` is not satisfied: {}",
                fun_target.func_env.get_full_name_str(),
                fun_target.global_env().symbol_pool().string(ty_param.0),
                ability_suffix,
                ty_arg.display(&Self::get_type_display_context(fun_target))
            ))
    }

    pub fn type_argument_constraints_not_satisfied_for_struct(
        fun_target: &FunctionTarget,
        struct_env: &StructEnv,
        index: usize,
        ty_arg: &Type,
    ) -> PartialVMError {
        let ty_params = fun_target.get_type_parameters();
        let ty_param = ty_params.get(index).unwrap();
        let ability_tokens = Self::get_ability_tokens(ty_param.1 .0);
        let ability_suffix = if ability_tokens.is_empty() {
            "".to_owned()
        } else {
            ability_tokens.join(", ")
        };
        PartialVMError::new(INVARIANT_ERROR)
            .with_sub_status(
                ErrorSubCode::TYPE_ARGUMENT_CONSTRAINTS_NOT_SATISFIED_FOR_STRUCT as u64,
            )
            .with_message(format!(
                "[{}] in instantiation of struct `{}`, constraints on type argument `{}{}` is not satisfied: {}",
                fun_target.func_env.get_full_name_str(),
                struct_env.get_full_name_str(),
                fun_target.global_env().symbol_pool().string(ty_param.0),
                ability_suffix,
                ty_arg.display(&Self::get_type_display_context(fun_target))
            ))
    }

    pub fn type_argument_access_out_of_bound_for_function(
        fun_target: &FunctionTarget,
        index: usize,
    ) -> PartialVMError {
        PartialVMError::new(INVARIANT_ERROR)
            .with_sub_status(ErrorSubCode::TYPE_ARGUMENT_ACCESS_OUT_OF_BOUND_FOR_FUNCTION as u64)
            .with_message(format!(
                "[{}] type parameter access out of bound (index {}, total {})",
                fun_target.func_env.get_full_name_str(),
                index,
                fun_target.get_type_parameters().len()
            ))
    }

    pub fn type_argument_access_out_of_bound_for_struct(
        fun_target: &FunctionTarget,
        struct_env: &StructEnv,
        index: usize,
    ) -> PartialVMError {
        PartialVMError::new(INVARIANT_ERROR)
            .with_sub_status(ErrorSubCode::TYPE_ARGUMENT_ACCESS_OUT_OF_BOUND_FOR_STRUCT as u64)
            .with_message(format!(
                "[{}] type parameter access out of bound for struct `{}`: (index {}, total {})",
                fun_target.func_env.get_full_name_str(),
                struct_env.get_full_name_str(),
                index,
                fun_target.get_type_parameters().len()
            ))
    }

    //
    // Errors related to bytecode operations
    //

    pub fn bytecode_operand_src_count_mismatch(
        fun_target: &FunctionTarget,
        bytecode: &Bytecode,
        expect_count: usize,
        actual_count: usize,
    ) -> PartialVMError {
        let label_offsets = Bytecode::label_offsets(fun_target.get_bytecode());
        PartialVMError::new(INVARIANT_ERROR)
            .with_sub_status(ErrorSubCode::BYTECODE_OPERAND_SRC_COUNT_MISMATCH as u64)
            .with_message(format!(
                "[{}] expect {} src operand(s) for bytecode {}, got {}",
                fun_target.func_env.get_full_name_str(),
                expect_count,
                bytecode.display(fun_target, &label_offsets),
                actual_count
            ))
    }

    pub fn bytecode_operand_dst_count_mismatch(
        fun_target: &FunctionTarget,
        bytecode: &Bytecode,
        expect_count: usize,
        actual_count: usize,
    ) -> PartialVMError {
        let label_offsets = Bytecode::label_offsets(fun_target.get_bytecode());
        PartialVMError::new(INVARIANT_ERROR)
            .with_sub_status(ErrorSubCode::BYTECODE_OPERAND_DST_COUNT_MISMATCH as u64)
            .with_message(format!(
                "[{}] expect {} dst operand(s) for bytecode {}, got {}",
                fun_target.func_env.get_full_name_str(),
                expect_count,
                bytecode.display(fun_target, &label_offsets),
                actual_count
            ))
    }

    pub fn bytecode_operand_src_type_mismatch(
        fun_target: &FunctionTarget,
        bytecode: &Bytecode,
        val: &SpecValue,
        ty: &Type,
    ) -> PartialVMError {
        let label_offsets = Bytecode::label_offsets(fun_target.get_bytecode());
        PartialVMError::new(INVARIANT_ERROR)
            .with_sub_status(ErrorSubCode::BYTECODE_OPERAND_SRC_TYPE_MISMATCH as u64)
            .with_message(format!(
                "[{}] expect a src operand of type {} for bytecode {}, got {:?}",
                fun_target.func_env.get_full_name_str(),
                ty.display(&Self::get_type_display_context(fun_target)),
                bytecode.display(fun_target, &label_offsets),
                val
            ))
    }

    pub fn bytecode_operand_dst_type_mismatch(
        fun_target: &FunctionTarget,
        bytecode: &Bytecode,
        val: &SpecValue,
        ty: &Type,
    ) -> PartialVMError {
        let label_offsets = Bytecode::label_offsets(fun_target.get_bytecode());
        PartialVMError::new(INVARIANT_ERROR)
            .with_sub_status(ErrorSubCode::BYTECODE_OPERAND_DST_TYPE_MISMATCH as u64)
            .with_message(format!(
                "[{}] expect a dst operand of type {} for bytecode {}, got {:?}",
                fun_target.func_env.get_full_name_str(),
                ty.display(&Self::get_type_display_context(fun_target)),
                bytecode.display(fun_target, &label_offsets),
                val
            ))
    }

    pub fn bytecode_label_invalid(fun_target: &FunctionTarget, label: Label) -> PartialVMError {
        PartialVMError::new(INVARIANT_ERROR)
            .with_sub_status(ErrorSubCode::BYTECODE_LABEL_INVALID as u64)
            .with_message(format!(
                "[{}] unable to find offset for label `L{}`",
                fun_target.func_env.get_full_name_str(),
                label.as_usize()
            ))
    }

    //
    // Errors related to function interpretation
    //

    pub fn function_already_terminated(fun_target: &FunctionTarget) -> PartialVMError {
        PartialVMError::new(INVARIANT_ERROR)
            .with_sub_status(ErrorSubCode::FUNCTION_ALREADY_TERMINATED as u64)
            .with_message(format!(
                "[{}] function already terminated",
                fun_target.func_env.get_full_name_str()
            ))
    }

    pub fn function_not_terminated(fun_target: &FunctionTarget, status: &str) -> PartialVMError {
        PartialVMError::new(INVARIANT_ERROR)
            .with_sub_status(ErrorSubCode::FUNCTION_NOT_TERMINATED as u64)
            .with_message(format!(
                "[{}] function not terminated (status: {})",
                fun_target.func_env.get_full_name_str(),
                status
            ))
    }

    //
    // Errors related to function returns
    //

    pub fn return_value_count_mismatch(
        fun_target: &FunctionTarget,
        expect_count: usize,
        actual_count: usize,
    ) -> PartialVMError {
        PartialVMError::new(INVARIANT_ERROR)
            .with_sub_status(ErrorSubCode::RETURN_VALUE_COUNT_MISMATCH as u64)
            .with_message(format!(
                "[{}] function returned {} values, expect {}",
                fun_target.func_env.get_full_name_str(),
                actual_count,
                expect_count
            ))
    }

    //
    // Errors related with aborts
    //

    pub fn abort_value_type_mismatch(
        fun_target: &FunctionTarget,
        val: &SpecValue,
        ty: &Type,
    ) -> PartialVMError {
        PartialVMError::new(INVARIANT_ERROR)
            .with_sub_status(ErrorSubCode::ABORT_VALUE_TYPE_MISMATCH as u64)
            .with_message(format!(
                "[{}] function aborted with invalid value type: expect {}, got {:?}",
                fun_target.func_env.get_full_name_str(),
                ty.display(&Self::get_type_display_context(fun_target)),
                val
            ))
    }

    pub fn abort_action_unexpected(
        fun_target: &FunctionTarget,
        bytecode: &Bytecode,
    ) -> PartialVMError {
        assert!(matches!(bytecode, Bytecode::Call(_, _, op, _, _) if !op.can_abort()));
        let label_offsets = Bytecode::label_offsets(fun_target.get_bytecode());
        PartialVMError::new(INVARIANT_ERROR)
            .with_sub_status(ErrorSubCode::ABORT_ACTION_UNEXPECTED as u64)
            .with_message(format!(
                "[{}] abort action specified at a bytecode that can not abort: {}",
                fun_target.func_env.get_full_name_str(),
                bytecode.display(fun_target, &label_offsets),
            ))
    }

    //
    // Utilities
    //

    fn get_type_display_context<'a>(fun_target: &'a FunctionTarget) -> TypeDisplayContext<'a> {
        let env = fun_target.global_env();
        let type_param_names = fun_target
            .get_type_parameters()
            .into_iter()
            .map(|param| param.0)
            .collect();
        TypeDisplayContext::WithEnv {
            env,
            type_param_names: Some(type_param_names),
        }
    }

    fn get_ability_tokens(abilities: AbilitySet) -> Vec<&'static str> {
        let mut ability_tokens = vec![];
        if abilities.has_copy() {
            ability_tokens.push("copy");
        }
        if abilities.has_drop() {
            ability_tokens.push("drop");
        }
        if abilities.has_store() {
            ability_tokens.push("store");
        }
        if abilities.has_key() {
            ability_tokens.push("key");
        }
        ability_tokens
    }
}
