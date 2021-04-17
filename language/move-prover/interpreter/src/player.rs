// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use bytecode::{
    function_target::FunctionTarget,
    function_target_pipeline::FunctionTargetsHolder,
    stackless_bytecode::{Bytecode, Constant, Operation},
};
use move_core_types::{
    account_address::AccountAddress,
    value::{MoveStruct, MoveValue},
    vm_status::StatusCode,
};
use move_model::ty::{PrimitiveType, Type};
use vm::errors::{PartialVMError, PartialVMResult};

use crate::{
    global_state::{resource_key_into_struct_type, struct_type_into_resource_key, GlobalState},
    local_state::{LocalState, TerminationStatus},
    status::ErrorSubCode,
    value::SpecValue,
};

/// Entrypoint of the step-by-step interpretation logic
pub fn entrypoint<'info, 'env>(
    fun_holder: &'env FunctionTargetsHolder,
    fun_target: &'info FunctionTarget<'env>,
    ty_args: &'info [Type],
    args: &[SpecValue],
    global_state: &mut GlobalState,
) -> PartialVMResult<Vec<SpecValue>> {
    let local_state = exec_function(fun_holder, fun_target, ty_args, args, global_state)?;
    let termination = local_state.into_termination_status();
    let return_vals = match termination {
        TerminationStatus::None => {
            return Err(ErrorSubCode::function_not_terminated(fun_target, "running"));
        }
        TerminationStatus::PostAbort => {
            return Err(ErrorSubCode::function_not_terminated(
                fun_target,
                "post-abort",
            ));
        }
        TerminationStatus::Abort(abort_code) => {
            return Err(PartialVMError::new(StatusCode::ABORTED).with_sub_status(abort_code));
        }
        TerminationStatus::Return(return_vals) => return_vals,
    };
    Ok(return_vals)
}

/// Execute a function with the type arguments and value arguments.
fn exec_function<'info, 'env>(
    fun_holder: &'env FunctionTargetsHolder,
    fun_target: &'info FunctionTarget<'env>,
    ty_args: &'info [Type],
    args: &[SpecValue],
    global_state: &mut GlobalState,
) -> PartialVMResult<LocalState<'info, 'env>> {
    let mut local_state = LocalState::new(fun_holder, fun_target, ty_args, args)?;
    // TODO(mengxu): implement the interpreter
    for bytecode in fun_target.get_bytecode() {
        exec_bytecode(bytecode, &mut local_state, global_state)?;
    }
    Ok(local_state)
}

/// Single-step a bytecode given the local and global state.
fn exec_bytecode(
    bytecode: &Bytecode,
    local_state: &mut LocalState,
    global_state: &mut GlobalState,
) -> PartialVMResult<()> {
    match bytecode {
        Bytecode::SpecBlock(..) => panic!("deprecated"),
        Bytecode::Assign(_, dst, src, kind) => {
            local_state.slot_assign(*src, *dst, kind)?;
            local_state.pc_next();
        }
        Bytecode::Load(_, dst, constant) => {
            let val = match constant {
                Constant::Bool(v) => MoveValue::Bool(*v),
                Constant::U8(v) => MoveValue::U8(*v),
                Constant::U64(v) => MoveValue::U64(*v),
                Constant::U128(v) => MoveValue::U128(*v),
                Constant::Address(v) => {
                    MoveValue::Address(AccountAddress::from_hex(format!("0x{:#x}", v)).unwrap())
                }
                Constant::ByteArray(v) => MoveValue::vector_u8(v.clone()),
            };
            local_state.put_bytecode_dst(*dst, SpecValue::Obj(val))?;
            local_state.pc_next();
        }
        Bytecode::Call(
            _,
            dsts,
            Operation::Function(callee_module_id, callee_fun_id, callee_ty_args),
            srcs,
            abort_act_opt,
        ) => {
            // collect src values
            let src_vals = local_state.get_bytecode_srcs(srcs)?;

            // get function of the same variant
            let info = &local_state.info;
            let callee_env = info.get_function_env(callee_module_id.qualified(*callee_fun_id))?;
            let callee_target = info.get_function_target(&callee_env);

            // transfer the control into the callee function
            let instantiated_ty_args = info.instantiate_type_args_fully(callee_ty_args)?;
            let callee_local_state = exec_function(
                local_state.info.fun_holder,
                &callee_target,
                &instantiated_ty_args,
                &src_vals,
                global_state,
            )?;

            // check callee termination status
            let termination = callee_local_state.into_termination_status();
            match termination {
                TerminationStatus::None => {
                    return Err(ErrorSubCode::function_not_terminated(
                        &callee_target,
                        "running",
                    ));
                }
                TerminationStatus::PostAbort => {
                    return Err(ErrorSubCode::function_not_terminated(
                        &callee_target,
                        "post-abort",
                    ));
                }
                TerminationStatus::Abort(abort_code) => match abort_act_opt {
                    None => local_state.terminate_with_abort_cascade(abort_code)?,
                    Some(abort_act) => {
                        let status_value = SpecValue::Obj(MoveValue::U64(abort_code));
                        local_state.put_bytecode_dst(abort_act.1, status_value)?;
                        local_state.transit_to_post_abort()?;
                        local_state.pc_jump(&abort_act.0)?;
                    }
                },
                TerminationStatus::Return(return_vals) => {
                    if return_vals.len() != dsts.len() {
                        return Err(ErrorSubCode::return_value_count_mismatch(
                            &callee_target,
                            dsts.len(),
                            return_vals.len(),
                        ));
                    }
                    local_state.put_bytecode_dsts(dsts, return_vals)?;
                    local_state.pc_next();
                }
            }
        }
        Bytecode::Call(
            _,
            dsts,
            Operation::Pack(module_id, struct_id, struct_insts),
            srcs,
            abort_act_opt,
        ) => {
            // sanity checks on abort actions
            if abort_act_opt.is_some() {
                return Err(ErrorSubCode::abort_action_unexpected(
                    local_state.info.fun_target,
                    bytecode,
                ));
            }

            // collect src values
            let src_vals = local_state.get_bytecode_srcs(srcs)?;

            // fully instantiate the struct type
            let info = &local_state.info;
            let (instantiated_struct_ty, instantiated_field_tys) =
                info.instantiate_struct_type_fully(*module_id, *struct_id, struct_insts)?;

            // sanity checks on operands
            info.check_bytecode_src_count(bytecode, srcs, instantiated_field_tys.len())?;
            info.check_bytecode_dst_count(bytecode, dsts, 1)?;

            // convert fields
            let field_vals = src_vals
                .into_iter()
                .zip(instantiated_field_tys)
                .map(|(src_val, field_ty)| match src_val {
                    SpecValue::Obj(obj) => Ok(obj),
                    SpecValue::Ref(_) => Err(ErrorSubCode::bytecode_operand_src_type_mismatch(
                        info.fun_target,
                        bytecode,
                        &src_val,
                        &field_ty,
                    )),
                })
                .collect::<PartialVMResult<Vec<_>>>()?;

            // construct the value
            let packed_val = SpecValue::Obj(MoveValue::Struct(MoveStruct::new(field_vals)));
            info.check_value_matches_type_operand_dst(
                bytecode,
                &packed_val,
                &instantiated_struct_ty,
            )?;
            local_state.put_bytecode_dsts(dsts, vec![packed_val])?;
            local_state.pc_next();
        }
        Bytecode::Call(
            _,
            dsts,
            Operation::Unpack(module_id, struct_id, struct_insts),
            srcs,
            abort_act_opt,
        ) => {
            // sanity checks on abort actions
            if abort_act_opt.is_some() {
                return Err(ErrorSubCode::abort_action_unexpected(
                    local_state.info.fun_target,
                    bytecode,
                ));
            }

            // collect src values
            let src_vals = local_state.get_bytecode_srcs(srcs)?;

            // fully instantiate the struct type
            let info = &local_state.info;
            let (instantiated_struct_ty, instantiated_field_tys) =
                info.instantiate_struct_type_fully(*module_id, *struct_id, struct_insts)?;

            // sanity checks on operands
            info.check_bytecode_dst_count(bytecode, srcs, 1)?;
            info.check_bytecode_src_count(bytecode, dsts, instantiated_field_tys.len())?;

            // convert fields
            let struct_val = src_vals.into_iter().next().unwrap();
            info.check_value_matches_type_operand_src(
                bytecode,
                &struct_val,
                &instantiated_struct_ty,
            )?;
            let dst_vals = match struct_val {
                SpecValue::Obj(MoveValue::Struct(fields)) => fields
                    .into_inner()
                    .into_iter()
                    .map(SpecValue::Obj)
                    .collect(),
                _ => {
                    return Err(ErrorSubCode::bytecode_operand_src_type_mismatch(
                        info.fun_target,
                        bytecode,
                        &struct_val,
                        &instantiated_struct_ty,
                    ));
                }
            };
            local_state.put_bytecode_dsts(dsts, dst_vals)?;
            local_state.pc_next();
        }
        Bytecode::Call(
            _,
            dsts,
            Operation::MoveTo(module_id, struct_id, struct_insts),
            srcs,
            abort_act_opt,
        ) => {
            // collect src values
            let mut src_vals = local_state.get_bytecode_srcs(srcs)?;

            // fully instantiate the struct type
            let info = &local_state.info;
            let (instantiated_struct_ty, _) =
                info.instantiate_struct_type_fully(*module_id, *struct_id, struct_insts)?;

            // sanity checks on operands
            info.check_bytecode_dst_count(bytecode, srcs, 0)?;
            info.check_bytecode_src_count(bytecode, dsts, 2)?;

            // check types
            let resource_val = src_vals.pop().unwrap();
            info.check_value_matches_type_operand_src(
                bytecode,
                &resource_val,
                &instantiated_struct_ty,
            )?;
            let resource_struct = resource_val.into_struct().unwrap();

            let account_val = src_vals.pop().unwrap();
            let account_address = account_val.into_signer().map_err(|malformed_val| {
                ErrorSubCode::bytecode_operand_src_type_mismatch(
                    info.fun_target,
                    bytecode,
                    &malformed_val,
                    &Type::Primitive(PrimitiveType::Signer),
                )
            })?;

            // put to global storage
            let exist_opt = global_state.put_resource(
                &account_address,
                struct_type_into_resource_key(instantiated_struct_ty).unwrap(),
                resource_struct,
            );
            match (exist_opt, abort_act_opt) {
                (None, _) => {
                    local_state.pc_next();
                }
                (Some(_), None) => {
                    return Err(PartialVMError::new(StatusCode::RESOURCE_ALREADY_EXISTS));
                }
                (Some(_), Some(abort_act)) => {
                    let status_value =
                        SpecValue::Obj(MoveValue::U64(StatusCode::RESOURCE_ALREADY_EXISTS as u64));
                    local_state.put_bytecode_dst(abort_act.1, status_value)?;
                    local_state.transit_to_post_abort()?;
                    local_state.pc_jump(&abort_act.0)?;
                }
            }
        }
        Bytecode::Call(
            _,
            dsts,
            Operation::MoveFrom(module_id, struct_id, struct_insts),
            srcs,
            abort_act_opt,
        ) => {
            // collect src values
            let src_vals = local_state.get_bytecode_srcs(srcs)?;

            // fully instantiate the struct type
            let info = &local_state.info;
            let (instantiated_struct_ty, _) =
                info.instantiate_struct_type_fully(*module_id, *struct_id, struct_insts)?;

            // sanity checks on operands
            info.check_bytecode_dst_count(bytecode, srcs, 1)?;
            info.check_bytecode_src_count(bytecode, dsts, 1)?;

            // check types
            let account_val = src_vals.into_iter().next().unwrap();
            let account_address = account_val.into_signer().map_err(|malformed_val| {
                ErrorSubCode::bytecode_operand_src_type_mismatch(
                    info.fun_target,
                    bytecode,
                    &malformed_val,
                    &Type::Primitive(PrimitiveType::Signer),
                )
            })?;
            let resource_key = struct_type_into_resource_key(instantiated_struct_ty).unwrap();
            let resource_opt = global_state.del_resource(&account_address, &resource_key);
            match (resource_opt, abort_act_opt) {
                (None, None) => {
                    return Err(PartialVMError::new(StatusCode::RESOURCE_DOES_NOT_EXIST));
                }
                (None, Some(abort_act)) => {
                    let status_value =
                        SpecValue::Obj(MoveValue::U64(StatusCode::RESOURCE_DOES_NOT_EXIST as u64));
                    local_state.put_bytecode_dst(abort_act.1, status_value)?;
                    local_state.transit_to_post_abort()?;
                    local_state.pc_jump(&abort_act.0)?;
                }
                (Some(resource_struct), _) => {
                    let resoruce_struct_ty = resource_key_into_struct_type(resource_key);
                    let resource_val = SpecValue::Obj(MoveValue::Struct(resource_struct));
                    info.check_value_matches_type_operand_src(
                        bytecode,
                        &resource_val,
                        &resoruce_struct_ty,
                    )?;
                    let dst_vals = vec![resource_val];
                    local_state.put_bytecode_dsts(dsts, dst_vals)?;
                    local_state.pc_next();
                }
            }
        }
        Bytecode::Branch(_, then_label, else_label, cond_idx) => {
            let cond = local_state.get_bytecode_src(*cond_idx)?;
            let cond_val = cond.into_bool().map_err(|malformed_val| {
                ErrorSubCode::bytecode_operand_src_type_mismatch(
                    local_state.info.fun_target,
                    bytecode,
                    &malformed_val,
                    &Type::Primitive(PrimitiveType::Bool),
                )
            })?;
            local_state.pc_jump(if cond_val { then_label } else { else_label })?;
        }
        Bytecode::Jump(_, label) => {
            local_state.pc_jump(label)?;
        }
        Bytecode::Abort(_, status_idx) => {
            local_state.terminate_with_abort(*status_idx)?;
        }
        Bytecode::Ret(_, return_slots) => {
            local_state.terminate_with_return(return_slots)?;
        }
        Bytecode::Label(..) | Bytecode::Nop(..) => {
            local_state.pc_next();
        }
        _ => unimplemented!("bytecode {:?} is not supported yet", bytecode),
    }
    Ok(())
}
