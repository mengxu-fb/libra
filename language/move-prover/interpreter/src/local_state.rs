// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use std::collections::BTreeMap;

use bytecode::{
    function_target::FunctionTarget,
    function_target_pipeline::FunctionTargetsHolder,
    stackless_bytecode::{AssignKind, Bytecode, Label},
};
use move_core_types::value::MoveValue;
use move_model::{
    ast::TempIndex,
    model::{
        AbilitySet, FunId, FunctionEnv, GlobalEnv, ModuleId, QualifiedId, StructEnv, StructId,
        TypeParameter,
    },
    ty::{PrimitiveType, Type},
};
use vm::{errors::PartialVMResult, file_format::CodeOffset};

use crate::{status::ErrorSubCode, value::SpecValue};

pub(crate) struct LocalInfo<'info, 'env> {
    pub(crate) fun_holder: &'env FunctionTargetsHolder,
    pub(crate) fun_target: &'info FunctionTarget<'env>,
    pub(crate) ty_args: &'info [Type],
    label_offsets: BTreeMap<Label, CodeOffset>,
}

impl<'info, 'env> LocalInfo<'info, 'env> {
    pub fn new(
        fun_holder: &'env FunctionTargetsHolder,
        fun_target: &'info FunctionTarget<'env>,
        ty_args: &'info [Type],
    ) -> Self {
        Self {
            fun_holder,
            fun_target,
            ty_args,
            label_offsets: Bytecode::label_offsets(fun_target.get_bytecode()),
        }
    }

    //
    // getters with error checking
    //

    fn get_local_type(&self, idx: TempIndex) -> PartialVMResult<&Type> {
        if idx >= self.fun_target.get_local_count() {
            return Err(ErrorSubCode::local_access_out_of_bound(
                self.fun_target,
                idx,
            ));
        }
        Ok(self.fun_target.get_local_type(idx))
    }

    pub fn get_function_env(
        &'env self,
        qualified_id: QualifiedId<FunId>,
    ) -> PartialVMResult<FunctionEnv<'env>> {
        let env = self.fun_target.global_env();
        let current_variant = &self.fun_target.data.variant;
        for (qid, variant) in self.fun_holder.get_funs_and_variants() {
            if qid == qualified_id && current_variant == &variant {
                return Ok(env.get_function(qualified_id));
            }
        }
        Err(ErrorSubCode::env_function_lookup_failure(env, qualified_id))
    }

    pub fn get_function_target(&self, fun_env: &'env FunctionEnv<'env>) -> FunctionTarget<'env> {
        let variant = &self.fun_target.data.variant;
        self.fun_holder.get_target(fun_env, variant)
    }

    pub fn get_struct_env(
        &'env self,
        qualified_id: QualifiedId<StructId>,
    ) -> PartialVMResult<StructEnv<'env>> {
        let env = self.fun_target.global_env();
        for module_data in &env.module_data {
            if module_data.id == qualified_id.module_id {
                for struct_id in module_data.struct_data.keys().copied() {
                    if struct_id == qualified_id.id {
                        return Ok(env.get_struct(qualified_id));
                    }
                }
            }
        }
        Err(ErrorSubCode::env_struct_lookup_failure(env, qualified_id))
    }

    pub fn get_offset_from_label(&self, label: &Label) -> PartialVMResult<CodeOffset> {
        self.label_offsets
            .get(label)
            .copied()
            .ok_or_else(|| ErrorSubCode::bytecode_label_invalid(self.fun_target, *label))
    }

    //
    // checking procedures
    //

    fn check_value_matches_type(&self, val: &SpecValue, ty: &Type) -> bool {
        fn check_object_matches_type_recursive(
            env: &GlobalEnv,
            ty_args: &[Type],
            val: &MoveValue,
            ty: &Type,
        ) -> bool {
            match (val, ty) {
                (MoveValue::Bool(..), Type::Primitive(PrimitiveType::Bool)) => true,
                (MoveValue::U8(..), Type::Primitive(PrimitiveType::U8)) => true,
                (MoveValue::U64(..), Type::Primitive(PrimitiveType::U64)) => true,
                (MoveValue::U128(..), Type::Primitive(PrimitiveType::U128)) => true,
                (MoveValue::Address(..), Type::Primitive(PrimitiveType::Address)) => true,
                (MoveValue::Signer(..), Type::Primitive(PrimitiveType::Signer)) => true,
                (MoveValue::Vector(elems), Type::Vector(elem_ty)) => elems
                    .iter()
                    .all(|elem| check_object_matches_type_recursive(env, ty_args, elem, elem_ty)),
                (
                    MoveValue::Struct(move_struct),
                    Type::Struct(module_id, struct_id, struct_insts),
                ) => {
                    let fields = move_struct.fields();
                    let struct_env = env.get_struct(module_id.qualified(*struct_id));
                    struct_env.get_field_count() == fields.len()
                        && fields.iter().zip(struct_env.get_fields()).all(
                            |(field_val, field_env)| {
                                check_object_matches_type_recursive(
                                    env,
                                    struct_insts,
                                    field_val,
                                    &field_env.get_type(),
                                )
                            },
                        )
                }
                (_, Type::TypeParameter(param_idx)) => {
                    ty_args
                        .get(*param_idx as usize)
                        .map_or(false, |actual_type| {
                            check_object_matches_type_recursive(env, ty_args, val, actual_type)
                        })
                }
                // all other cases means a type error
                _ => false,
            }
        }

        let env = self.fun_target.global_env();
        match val {
            SpecValue::Obj(move_val) => {
                check_object_matches_type_recursive(env, self.ty_args, move_val, ty)
            }
            SpecValue::Ref(move_val) => match ty {
                Type::Reference(_, base_ty) => {
                    check_object_matches_type_recursive(env, self.ty_args, move_val, base_ty)
                }
                // all other cases means a type error
                _ => false,
            },
        }
    }

    pub fn check_value_matches_type_local(
        &self,
        idx: TempIndex,
        val: &SpecValue,
    ) -> PartialVMResult<()> {
        let ty = self.get_local_type(idx)?;
        if !self.check_value_matches_type(val, ty) {
            return Err(ErrorSubCode::local_type_mismatch(
                self.fun_target,
                idx,
                val,
                ty,
            ));
        }
        Ok(())
    }

    pub fn check_value_matches_type_operand_src(
        &self,
        bytecode: &Bytecode,
        val: &SpecValue,
        ty: &Type,
    ) -> PartialVMResult<()> {
        if !self.check_value_matches_type(val, ty) {
            return Err(ErrorSubCode::bytecode_operand_src_type_mismatch(
                self.fun_target,
                bytecode,
                val,
                ty,
            ));
        }
        Ok(())
    }

    pub fn check_value_matches_type_operand_dst(
        &self,
        bytecode: &Bytecode,
        val: &SpecValue,
        ty: &Type,
    ) -> PartialVMResult<()> {
        if !self.check_value_matches_type(val, ty) {
            return Err(ErrorSubCode::bytecode_operand_dst_type_mismatch(
                self.fun_target,
                bytecode,
                val,
                ty,
            ));
        }
        Ok(())
    }

    pub fn check_bytecode_src_count(
        &self,
        bytecode: &Bytecode,
        srcs: &[TempIndex],
        expected_count: usize,
    ) -> PartialVMResult<()> {
        if srcs.len() != expected_count {
            return Err(ErrorSubCode::bytecode_operand_src_count_mismatch(
                self.fun_target,
                bytecode,
                expected_count,
                srcs.len(),
            ));
        }
        Ok(())
    }

    pub fn check_bytecode_dst_count(
        &self,
        bytecode: &Bytecode,
        dsts: &[TempIndex],
        expected_count: usize,
    ) -> PartialVMResult<()> {
        if dsts.len() != expected_count {
            return Err(ErrorSubCode::bytecode_operand_dst_count_mismatch(
                self.fun_target,
                bytecode,
                expected_count,
                dsts.len(),
            ));
        }
        Ok(())
    }

    //
    // conversion procedures
    //

    pub fn instantiate_struct_type_fully(
        &self,
        module_id: ModuleId,
        struct_id: StructId,
        struct_insts: &[Type],
    ) -> PartialVMResult<(Type, Vec<Type>)> {
        let struct_env = self.get_struct_env(module_id.qualified(struct_id))?;
        let new_struct_insts = struct_insts
            .iter()
            .map(|struct_inst| self.instantiate_type_fully(struct_inst))
            .collect::<PartialVMResult<Vec<_>>>()?;
        check_type_args_for_struct(self.fun_target, &struct_env, &new_struct_insts)?;

        let new_field_tys = struct_env
            .get_fields()
            .map(|field_env| match field_env.get_type() {
                Type::TypeParameter(param_idx) => new_struct_insts
                    .get(param_idx as usize)
                    .cloned()
                    .ok_or_else(|| {
                        ErrorSubCode::type_argument_access_out_of_bound_for_struct(
                            self.fun_target,
                            &struct_env,
                            param_idx as usize,
                        )
                    }),
                field_ty => Ok(field_ty),
            })
            .collect::<PartialVMResult<Vec<_>>>()?;

        let new_struct_ty = Type::Struct(module_id, struct_id, new_struct_insts);
        Ok((new_struct_ty, new_field_tys))
    }

    pub fn instantiate_type_fully(&self, ty: &Type) -> PartialVMResult<Type> {
        let new_ty = match ty {
            Type::Primitive(p) => Type::Primitive(*p),
            Type::Tuple(comp_tys) => {
                let new_comp_tys = comp_tys
                    .iter()
                    .map(|comp_ty| self.instantiate_type_fully(comp_ty))
                    .collect::<PartialVMResult<Vec<_>>>()?;
                Type::Tuple(new_comp_tys)
            }
            Type::Vector(elem_ty) => {
                let new_elem_ty = self.instantiate_type_fully(elem_ty)?;
                Type::Vector(Box::new(new_elem_ty))
            }
            Type::Struct(module_id, struct_id, struct_insts) => {
                let (new_struct_ty, _) =
                    self.instantiate_struct_type_fully(*module_id, *struct_id, struct_insts)?;
                new_struct_ty
            }
            Type::TypeParameter(param_idx) => self
                .ty_args
                .get(*param_idx as usize)
                .ok_or_else(|| {
                    ErrorSubCode::type_argument_access_out_of_bound_for_function(
                        self.fun_target,
                        *param_idx as usize,
                    )
                })?
                .clone(),
            Type::Reference(is_mut, ref_ty) => {
                let new_ref_ty = self.instantiate_type_fully(ref_ty)?;
                Type::Reference(*is_mut, Box::new(new_ref_ty))
            }
            Type::Fun(arg_tys, ret_ty) => {
                let new_arg_tys = arg_tys
                    .iter()
                    .map(|arg_ty| self.instantiate_type_fully(arg_ty))
                    .collect::<PartialVMResult<Vec<_>>>()?;
                let new_ret_ty = self.instantiate_type_fully(ret_ty)?;
                Type::Fun(new_arg_tys, Box::new(new_ret_ty))
            }
            Type::TypeDomain(sub_ty) => {
                let new_sub_ty = self.instantiate_type_fully(sub_ty)?;
                Type::TypeDomain(Box::new(new_sub_ty))
            }
            Type::ResourceDomain(module_id, struct_id, struct_insts_opt) => {
                let struct_env = self.get_struct_env(module_id.qualified(*struct_id))?;
                let new_struct_insts_opt = match struct_insts_opt {
                    None => None,
                    Some(struct_insts) => {
                        let new_struct_insts = struct_insts
                            .iter()
                            .map(|struct_inst| self.instantiate_type_fully(struct_inst))
                            .collect::<PartialVMResult<Vec<_>>>()?;
                        check_type_args_for_struct(
                            self.fun_target,
                            &struct_env,
                            &new_struct_insts,
                        )?;
                        Some(new_struct_insts)
                    }
                };
                Type::ResourceDomain(*module_id, *struct_id, new_struct_insts_opt)
            }
            Type::TypeLocal(sym) => Type::TypeLocal(*sym),
            Type::Error => Type::Error,
            Type::Var(vidx) => Type::Var(*vidx),
        };
        Ok(new_ty)
    }

    pub fn instantiate_type_args_fully(&self, ty_args: &[Type]) -> PartialVMResult<Vec<Type>> {
        ty_args
            .iter()
            .map(|ty_arg| self.instantiate_type_fully(ty_arg))
            .collect()
    }
}

#[derive(Debug)]
pub(crate) enum TerminationStatus {
    None,
    PostAbort,
    Return(Vec<SpecValue>),
    Abort(u64),
}

pub(crate) struct LocalState<'info, 'env> {
    /// Holds the information needed for local (function-level) execution
    pub(crate) info: LocalInfo<'info, 'env>,
    /// slots that holds local variables
    slots: Vec<Option<SpecValue>>,
    /// program counter
    pc: CodeOffset,
    /// termination status
    termination: TerminationStatus,
}

impl<'info, 'env> LocalState<'info, 'env> {
    pub fn new(
        fun_holder: &'env FunctionTargetsHolder,
        fun_target: &'info FunctionTarget<'env>,
        ty_args: &'info [Type],
        args: &[SpecValue],
    ) -> PartialVMResult<Self> {
        // check invariants related to type arguments
        check_type_args_for_function(fun_target, ty_args)?;

        // check invariants related to arguments
        let param_count = fun_target.get_parameter_count();
        if param_count != args.len() {
            return Err(ErrorSubCode::argument_count_mismatch(
                fun_target,
                args.len(),
            ));
        }
        let local_count = fun_target.get_local_count();
        if local_count < args.len() {
            return Err(ErrorSubCode::local_count_less_than_argument_count(
                fun_target,
                args.len(),
            ));
        }

        // check type mismatches
        let info = LocalInfo::new(fun_holder, fun_target, ty_args);
        let params = fun_target.func_env.get_parameters();
        for (idx, arg) in args.iter().enumerate() {
            let local_ty = fun_target.get_local_type(idx);
            let param_ty = &params.get(idx).unwrap().1;
            assert_eq!(local_ty, param_ty);
            if !info.check_value_matches_type(arg, local_ty) {
                return Err(ErrorSubCode::local_type_mismatch(
                    fun_target, idx, arg, local_ty,
                ));
            }
        }

        // all checks passed, construct the local state
        let mut slots: Vec<_> = args.iter().cloned().map(Some).collect();
        for _ in args.len()..local_count {
            slots.push(None);
        }
        Ok(Self {
            info,
            slots,
            pc: 0,
            termination: TerminationStatus::None,
        })
    }

    //
    // local slot operations
    //

    fn get_slot(&self, idx: TempIndex) -> PartialVMResult<&Option<SpecValue>> {
        self.slots
            .get(idx)
            .ok_or_else(|| ErrorSubCode::local_access_out_of_bound(self.info.fun_target, idx))
    }

    fn get_slot_mut(&mut self, idx: TempIndex) -> PartialVMResult<&mut Option<SpecValue>> {
        let fun_target = self.info.fun_target;
        self.slots
            .get_mut(idx)
            .ok_or_else(|| ErrorSubCode::local_access_out_of_bound(fun_target, idx))
    }

    fn slot_move(&mut self, idx: TempIndex) -> PartialVMResult<SpecValue> {
        self.get_slot_mut(idx)?
            .take()
            .ok_or_else(|| ErrorSubCode::local_use_after_move(self.info.fun_target, idx))
    }

    fn slot_copy(&self, idx: TempIndex) -> PartialVMResult<SpecValue> {
        self.get_slot(idx)?
            .clone()
            .ok_or_else(|| ErrorSubCode::local_use_after_move(self.info.fun_target, idx))
    }

    fn slot_store(&mut self, idx: TempIndex, val: SpecValue) -> PartialVMResult<()> {
        self.info.check_value_matches_type_local(idx, &val)?;
        *self.get_slot_mut(idx)? = Some(val);
        Ok(())
    }

    pub fn slot_assign(
        &mut self,
        src: TempIndex,
        dst: TempIndex,
        kind: &AssignKind,
    ) -> PartialVMResult<()> {
        let val = match kind {
            AssignKind::Move | AssignKind::Store => self.slot_move(src)?,
            AssignKind::Copy => self.slot_copy(src)?,
        };
        self.slot_store(dst, val)
    }

    pub fn get_bytecode_src(&mut self, src: TempIndex) -> PartialVMResult<SpecValue> {
        self.slot_move(src)
    }

    pub fn get_bytecode_srcs(&mut self, srcs: &[TempIndex]) -> PartialVMResult<Vec<SpecValue>> {
        srcs.iter().map(|idx| self.get_bytecode_src(*idx)).collect()
    }

    pub fn put_bytecode_dst(&mut self, dst: TempIndex, val: SpecValue) -> PartialVMResult<()> {
        self.slot_store(dst, val)
    }

    pub fn put_bytecode_dsts(
        &mut self,
        dsts: &[TempIndex],
        vals: Vec<SpecValue>,
    ) -> PartialVMResult<()> {
        assert_eq!(dsts.len(), vals.len());
        for (dst, val) in dsts.iter().zip(vals) {
            self.put_bytecode_dst(*dst, val)?;
        }
        Ok(())
    }

    //
    // pc operations
    //

    pub fn pc_next(&mut self) {
        self.pc.checked_add(1).expect("PC should never overflow");
    }

    pub fn pc_jump(&mut self, dest: &Label) -> PartialVMResult<()> {
        self.pc = self.info.get_offset_from_label(dest)?;
        Ok(())
    }

    //
    // termination status
    //

    fn check_not_terminated(&self) -> PartialVMResult<()> {
        if !matches!(self.termination, TerminationStatus::None) {
            return Err(ErrorSubCode::function_already_terminated(
                self.info.fun_target,
            ));
        }
        Ok(())
    }

    pub fn terminate_with_abort(&mut self, status_slot: TempIndex) -> PartialVMResult<()> {
        self.check_not_terminated()?;
        let status_value = self.slot_move(status_slot)?;
        let abort_code = status_value.into_u64().map_err(|malformed_val| {
            ErrorSubCode::abort_value_type_mismatch(
                self.info.fun_target,
                &malformed_val,
                &Type::Primitive(PrimitiveType::U64),
            )
        })?;
        self.termination = TerminationStatus::Abort(abort_code);
        Ok(())
    }

    pub fn terminate_with_return(&mut self, return_slots: &[TempIndex]) -> PartialVMResult<()> {
        self.check_not_terminated()?;
        let return_values = return_slots
            .iter()
            .map(|slot| self.slot_move(*slot))
            .collect::<PartialVMResult<Vec<_>>>()?;
        self.termination = TerminationStatus::Return(return_values);
        Ok(())
    }

    pub fn terminate_with_abort_cascade(&mut self, abort_code: u64) -> PartialVMResult<()> {
        self.check_not_terminated()?;
        self.termination = TerminationStatus::Abort(abort_code);
        Ok(())
    }

    pub fn transit_to_post_abort(&mut self) -> PartialVMResult<()> {
        self.check_not_terminated()?;
        self.termination = TerminationStatus::PostAbort;
        Ok(())
    }

    pub fn into_termination_status(self) -> TerminationStatus {
        self.termination
    }
}

//
// information utilities
//

/// Get the abilities of this type, if this type is compatible with a move type.
fn get_abilities(ty: &Type, env: &GlobalEnv) -> Option<AbilitySet> {
    match ty {
        Type::Primitive(PrimitiveType::Bool)
        | Type::Primitive(PrimitiveType::U8)
        | Type::Primitive(PrimitiveType::U64)
        | Type::Primitive(PrimitiveType::U128)
        | Type::Primitive(PrimitiveType::Address) => Some(AbilitySet::PRIMITIVES),
        Type::Primitive(PrimitiveType::Signer) => Some(AbilitySet::SIGNER),
        // spec-specific primitive types do not have abilities
        Type::Primitive(_) => None,
        // a tuple can never be used to instantiate generics
        Type::Tuple(_) => None,
        Type::Vector(elem_ty) => get_abilities(elem_ty, env).map(|elem_abilities| {
            AbilitySet::polymorphic_abilities(AbilitySet::VECTOR, vec![elem_abilities])
        }),
        Type::Struct(module_id, struct_id, struct_insts) => {
            let struct_env = env.get_struct(module_id.qualified(*struct_id));
            let inst_abilities_opt = struct_insts
                .iter()
                .map(|ty_inst| get_abilities(ty_inst, env))
                .collect::<Option<Vec<_>>>();
            inst_abilities_opt.map(|inst_abilities| {
                AbilitySet::polymorphic_abilities(struct_env.get_abilities(), inst_abilities)
            })
        }
        Type::Reference(..) => Some(AbilitySet::REFERENCES),
        // the `ty` should be fully instantiated
        Type::TypeParameter(..) => None,
        // spec-specific types do not have abilities
        _ => None,
    }
}

//
// checking utilities
//

fn check_type_satisfies_constraints(
    env: &GlobalEnv,
    ty_arg: &Type,
    ty_param: &TypeParameter,
) -> Option<bool> {
    let ty_ability_constraints = ty_param.1 .0;
    get_abilities(ty_arg, env).map(|ty_abilities| ty_ability_constraints.is_subset(ty_abilities))
}

fn check_type_args_for_function(
    fun_target: &FunctionTarget,
    ty_args: &[Type],
) -> PartialVMResult<()> {
    let ty_params = fun_target.get_type_parameters();
    if ty_params.len() != ty_args.len() {
        return Err(ErrorSubCode::type_argument_count_mismatch_for_function(
            fun_target,
            ty_args.len(),
        ));
    }
    let env = fun_target.global_env();
    for (idx, ty_arg) in ty_args.iter().enumerate() {
        let ty_param = ty_params.get(idx).unwrap();
        let is_sat = check_type_satisfies_constraints(env, ty_arg, ty_param).ok_or_else(|| {
            ErrorSubCode::type_argument_invalid_for_function(fun_target, idx, ty_arg)
        })?;
        if !is_sat {
            return Err(
                ErrorSubCode::type_argument_constraints_not_satisfied_for_function(
                    fun_target, idx, ty_arg,
                ),
            );
        }
    }
    Ok(())
}

fn check_type_args_for_struct(
    fun_target: &FunctionTarget,
    struct_env: &StructEnv,
    ty_args: &[Type],
) -> PartialVMResult<()> {
    let ty_params = struct_env.get_type_parameters();
    if ty_params.len() != ty_args.len() {
        return Err(ErrorSubCode::type_argument_count_mismatch_for_struct(
            fun_target,
            struct_env,
            ty_args.len(),
        ));
    }
    let env = fun_target.global_env();
    for (idx, ty_arg) in ty_args.iter().enumerate() {
        let ty_param = ty_params.get(idx).unwrap();
        let is_sat = check_type_satisfies_constraints(env, ty_arg, ty_param).ok_or_else(|| {
            ErrorSubCode::type_argument_invalid_for_struct(fun_target, struct_env, idx, ty_arg)
        })?;
        if !is_sat {
            return Err(
                ErrorSubCode::type_argument_constraints_not_satisfied_for_struct(
                    fun_target, struct_env, idx, ty_arg,
                ),
            );
        }
    }
    Ok(())
}
