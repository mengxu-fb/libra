// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use std::collections::BTreeMap;

use bytecode::{
    function_target::FunctionTarget,
    function_target_pipeline::{FunctionTargetsHolder, FunctionVariant},
};
use move_core_types::{
    language_storage::TypeTag,
    value::{MoveStruct, MoveValue},
    vm_status::StatusCode,
};
use move_model::{
    model::{AbilitySet, FunId, FunctionEnv, GlobalEnv, QualifiedId},
    ty::{PrimitiveType, Type},
};
use vm::errors::{Location, PartialVMError, PartialVMResult, VMResult};

use crate::{global_state::GlobalState, player, status::ErrorSubCode, value::SpecValue};

/// A stackless bytecode runtime in charge of pre- and post-execution checking, conversion, and
/// monitoring. The main, step-by-step interpretation loop is delegated to the `Player` instance.
pub struct Runtime<'env> {
    env: &'env GlobalEnv,
    functions: &'env FunctionTargetsHolder,
}

impl<'env> Runtime<'env> {
    //
    // public interfaces
    //

    /// Construct a runtime with all information pre-loaded.
    pub fn new(env: &'env GlobalEnv, functions: &'env FunctionTargetsHolder) -> Self {
        Self { env, functions }
    }

    /// Execute a function (identified by `fun_id`) with given type arguments, arguments, and a
    /// snapshot of the global state. Returns a tuple contains both the result of the execution
    /// and the new global state.
    ///
    /// NOTE: there may be multiple variants of the same function registered in the
    /// FunctionTargetsHolder, all variants will be executed and this function only return a new
    /// global state if results from all variants converges. Otherwise, the old state is returned
    /// and the VMResult is set to an error accordingly.
    pub fn execute(
        &self,
        fun_id: QualifiedId<FunId>,
        ty_args: &[TypeTag],
        args: &[MoveValue],
        global_state: GlobalState,
    ) -> (VMResult<Vec<SpecValue>>, GlobalState) {
        let fun_env = self.env.get_function(fun_id);

        // check validity of the arguments
        let converted_ty_args =
            match self.check_and_convert_function_type_arguments(&fun_env, ty_args) {
                Ok(converted) => converted,
                Err(err) => {
                    return (Err(err.finish(Location::Undefined)), global_state);
                }
            };
        let converted_args =
            match self.check_and_convert_function_arguments(&fun_env, &converted_ty_args, args) {
                Ok(converted) => converted,
                Err(err) => {
                    return (Err(err.finish(Location::Undefined)), global_state);
                }
            };

        // execute each variant of the function and collect results
        let mut variants: BTreeMap<_, _> = self
            .functions
            .get_targets(&fun_env)
            .into_iter()
            .map(|(fun_variant, fun_target)| {
                let mut state = global_state.clone();
                let result = self.execute_target(
                    &fun_target,
                    &converted_ty_args,
                    &converted_args,
                    &mut state,
                );
                (fun_variant, (result, state))
            })
            .collect();

        // cross-comparison of execution results
        let baseline = match variants.remove(&FunctionVariant::Baseline) {
            None => {
                let module_id = fun_env.module_env.get_verified_module().self_id();
                return (
                    Err(ErrorSubCode::no_baseline_variant(&fun_env)
                        .finish(Location::Module(module_id))),
                    global_state,
                );
            }
            Some(baseline) => baseline,
        };
        for (variant, result) in variants {
            if result != baseline {
                // TODO (mengxu) maybe show details of disagreement between the results?
                let module_id = fun_env.module_env.get_verified_module().self_id();
                return (
                    Err(
                        ErrorSubCode::discrepancies_between_variants(&fun_env, &variant)
                            .finish(Location::Module(module_id)),
                    ),
                    global_state,
                );
            }
        }

        // all execution results agree, return the common version
        baseline
    }

    //
    // execution internals
    //

    fn execute_target(
        &self,
        fun_target: &FunctionTarget<'env>,
        ty_args: &[Type],
        args: &[SpecValue],
        global_state: &mut GlobalState,
    ) -> VMResult<Vec<SpecValue>> {
        let module_id = fun_target.module_env().get_verified_module().self_id();
        player::entrypoint(self.functions, fun_target, ty_args, args, global_state)
            .map_err(|err| err.finish(Location::Module(module_id)))
    }

    //
    // checking and conversion
    //

    fn check_and_convert_function_type_arguments(
        &self,
        fun_env: &FunctionEnv<'env>,
        ty_args: &[TypeTag],
    ) -> PartialVMResult<Vec<Type>> {
        let ty_params = fun_env.get_type_parameters();
        if ty_params.len() != ty_args.len() {
            return Err(PartialVMError::new(
                StatusCode::NUMBER_OF_TYPE_ARGUMENTS_MISMATCH,
            ));
        }
        for (ty_arg, ty_param) in ty_args.iter().zip(ty_params) {
            if !ty_param.1 .0.is_subset(self.get_abilities(ty_arg)?) {
                return Err(PartialVMError::new(StatusCode::CONSTRAINT_NOT_SATISFIED));
            }
        }
        let converted_ty_args = ty_args
            .iter()
            .map(|ty_arg| Type::from_type_tag(ty_arg.to_owned(), self.env))
            .collect();
        Ok(converted_ty_args)
    }

    fn check_and_convert_function_arguments(
        &self,
        fun_env: &FunctionEnv<'env>,
        ty_args: &[Type],
        args: &[MoveValue],
    ) -> PartialVMResult<Vec<SpecValue>> {
        fn check_and_convert_move_value_against_expected_type(
            env: &GlobalEnv,
            ty_args: &[Type],
            val: &MoveValue,
            expected_ty: &Type,
        ) -> PartialVMResult<MoveValue> {
            let checked_val = match (val, expected_ty) {
                (MoveValue::Bool(v), Type::Primitive(PrimitiveType::Bool)) => MoveValue::Bool(*v),
                (MoveValue::U8(v), Type::Primitive(PrimitiveType::U8)) => MoveValue::U8(*v),
                (MoveValue::U64(v), Type::Primitive(PrimitiveType::U64)) => MoveValue::U64(*v),
                (MoveValue::U128(v), Type::Primitive(PrimitiveType::U128)) => MoveValue::U128(*v),
                (MoveValue::Address(v), Type::Primitive(PrimitiveType::Address)) => {
                    MoveValue::Address(*v)
                }
                (MoveValue::Signer(v), Type::Primitive(PrimitiveType::Signer)) => {
                    MoveValue::Signer(*v)
                }
                (MoveValue::Vector(elems), Type::Vector(elem_ty)) => {
                    let checked_elems = elems
                        .iter()
                        .map(|elem| {
                            check_and_convert_move_value_against_expected_type(
                                env, ty_args, elem, elem_ty,
                            )
                        })
                        .collect::<PartialVMResult<Vec<_>>>()?;
                    MoveValue::Vector(checked_elems)
                }
                (
                    MoveValue::Struct(move_struct),
                    Type::Struct(module_id, struct_id, struct_insts),
                ) => {
                    let fields = move_struct.fields();
                    let struct_env = env.get_struct(module_id.qualified(*struct_id));
                    if struct_env.get_field_count() != fields.len() {
                        return Err(PartialVMError::new(StatusCode::TYPE_MISMATCH));
                    }
                    let checked_fields = fields
                        .iter()
                        .zip(struct_env.get_fields())
                        .map(|(field_val, field_env)| {
                            check_and_convert_move_value_against_expected_type(
                                env,
                                struct_insts,
                                field_val,
                                &field_env.get_type(),
                            )
                        })
                        .collect::<PartialVMResult<Vec<_>>>()?;
                    MoveValue::Struct(MoveStruct::new(checked_fields))
                }
                (_, Type::TypeParameter(param_idx)) => {
                    let actual_type = ty_args
                        .get(*param_idx as usize)
                        .ok_or_else(|| PartialVMError::new(StatusCode::TYPE_MISMATCH))?;
                    check_and_convert_move_value_against_expected_type(
                        env,
                        ty_args,
                        val,
                        actual_type,
                    )?
                }
                // all other cases means a type error
                _ => {
                    return Err(PartialVMError::new(StatusCode::TYPE_MISMATCH));
                }
            };
            Ok(checked_val)
        }

        let params = fun_env.get_parameters();
        if params.len() != args.len() {
            return Err(PartialVMError::new(
                StatusCode::NUMBER_OF_ARGUMENTS_MISMATCH,
            ));
        }
        let mut converted_args = vec![];
        for (arg, (i, param)) in args.iter().zip(params.into_iter().enumerate()) {
            let param_ty = param.1;
            assert_eq!(fun_env.get_local_type(i), param_ty);
            let new_arg = check_and_convert_move_value_against_expected_type(
                self.env, ty_args, arg, &param_ty,
            )?;
            converted_args.push(SpecValue::Obj(new_arg));
        }
        Ok(converted_args)
    }

    //
    // information utilities
    //

    fn get_abilities(&self, ty: &TypeTag) -> PartialVMResult<AbilitySet> {
        let abilities = match ty {
            TypeTag::Bool | TypeTag::U8 | TypeTag::U64 | TypeTag::U128 | TypeTag::Address => {
                AbilitySet::PRIMITIVES
            }
            TypeTag::Signer => AbilitySet::SIGNER,
            TypeTag::Vector(elem_ty) => AbilitySet::polymorphic_abilities(
                AbilitySet::VECTOR,
                vec![self.get_abilities(elem_ty)?],
            ),
            TypeTag::Struct(struct_tag) => {
                let struct_id = self.env.find_struct_by_tag(struct_tag).ok_or_else(|| {
                    PartialVMError::new(StatusCode::TYPE_RESOLUTION_FAILURE).with_message(format!(
                        "Cannot find struct `{}::{}::{}`",
                        struct_tag.address.short_str_lossless(),
                        struct_tag.module,
                        struct_tag.name,
                    ))
                })?;
                let struct_env = self.env.get_struct(struct_id);
                let ty_arg_abilities = struct_tag
                    .type_params
                    .iter()
                    .map(|arg| self.get_abilities(arg))
                    .collect::<PartialVMResult<Vec<_>>>()?;
                AbilitySet::polymorphic_abilities(struct_env.get_abilities(), ty_arg_abilities)
            }
        };
        Ok(abilities)
    }
}
