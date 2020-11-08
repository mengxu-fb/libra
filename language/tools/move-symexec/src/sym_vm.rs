// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use log::warn;

use move_core_types::{account_address::AccountAddress, transaction_argument::TransactionArgument};
use move_vm_types::values::{IntegerValue, Value};
use vm::{
    access::ScriptAccess,
    file_format::{Bytecode, CompiledScript, SignatureToken},
};

use crate::{
    sym_exec_graph::{ExecBlock, ExecGraph, ExecWalker, ExecWalkerStep},
    sym_setup::{ExecStructInfo, ExecTypeArg, StructContext, SymSetup},
    sym_smtlib::{SmtCtxt, SmtKind},
    sym_type_graph::TypeGraph,
    sym_vm_types::{SymFrame, SymTransactionArgument, SymValue},
};

/// Config: whether to simplify smt expressions upon construction
const CONF_SMT_AUTO_SIMPLIFY: bool = true;

/// The symbolic interpreter that examines instructions one by one
pub(crate) struct SymVM<'a> {
    /// A wrapper over the smt solver context manager
    smt_ctxt: SmtCtxt,
    /// The oracle for environmental information
    setup: &'a SymSetup<'a>,
    /// The script to run symbolization on
    script: &'a CompiledScript,
    /// The execution graph containing all code
    exec_graph: &'a ExecGraph,
    /// Maps all struct types to names of the corresponding smt types
    type_graph: &'a TypeGraph,
}

impl<'a> SymVM<'a> {
    fn type_arg_to_smt_kind(type_arg: &ExecTypeArg, type_graph: &TypeGraph) -> SmtKind {
        match type_arg {
            ExecTypeArg::Bool => SmtKind::Bool,
            ExecTypeArg::U8 => SmtKind::bitvec_u8(),
            ExecTypeArg::U64 => SmtKind::bitvec_u64(),
            ExecTypeArg::U128 => SmtKind::bitvec_u128(),
            ExecTypeArg::Address => SmtKind::bitvec_address(),
            ExecTypeArg::Signer => SmtKind::bitvec_address(),
            ExecTypeArg::Vector { element_type } => SmtKind::Vector {
                element_kind: Box::new(SymVM::type_arg_to_smt_kind(
                    element_type.as_ref(),
                    type_graph,
                )),
            },
            ExecTypeArg::Struct { context, type_args } => SmtKind::Struct {
                struct_name: type_graph
                    .get_struct_name(context, type_args)
                    .unwrap()
                    .to_owned(),
            },
            ExecTypeArg::Reference { referred_type }
            | ExecTypeArg::MutableReference { referred_type } => SmtKind::Reference {
                referred_kind: Box::new(SymVM::type_arg_to_smt_kind(
                    referred_type.as_ref(),
                    type_graph,
                )),
            },
            ExecTypeArg::TypeParameter { actual_type, .. } => {
                SymVM::type_arg_to_smt_kind(actual_type.as_ref(), type_graph)
            }
        }
    }

    pub fn new(
        setup: &'a SymSetup,
        script: &'a CompiledScript,
        exec_graph: &'a ExecGraph,
        type_graph: &'a TypeGraph,
    ) -> Self {
        let mut smt_ctxt = SmtCtxt::new(CONF_SMT_AUTO_SIMPLIFY);

        // pre-compute the struct smt types
        for (struct_name, struct_info) in type_graph.reverse_topological_sort() {
            match struct_info {
                ExecStructInfo::Native => {
                    // TODO: we should have a dedicated modeling for
                    // native struct types
                    warn!("A native struct type is ignored: {}", struct_name)
                }
                ExecStructInfo::Declared {
                    field_vec,
                    field_map,
                } => {
                    let field_smt_kinds: Vec<(String, SmtKind)> = field_vec
                        .iter()
                        .map(|field_name| {
                            (
                                field_name.clone().into_string(),
                                SymVM::type_arg_to_smt_kind(
                                    field_map.get(field_name).unwrap(),
                                    type_graph,
                                ),
                            )
                        })
                        .collect();
                    smt_ctxt.create_smt_struct(struct_name.to_owned(), field_smt_kinds);
                }
            }
        }

        // done
        Self {
            smt_ctxt,
            setup,
            script,
            exec_graph,
            type_graph,
        }
    }

    pub fn interpret(&self, signers: &[AccountAddress], sym_args: &[SymTransactionArgument]) {
        // collect value signatures
        let val_arg_sigs = self.script.signature_at(self.script.as_inner().parameters);

        // check that we got the correct number of value arguments
        // NOTE: signers must come before value arguments, if present
        // in the signature
        let use_signers = !val_arg_sigs.is_empty()
            && match val_arg_sigs.0.get(0).unwrap() {
                SignatureToken::Reference(inner) => matches!(&**inner, SignatureToken::Signer),
                _ => false,
            };

        debug_assert_eq!(
            val_arg_sigs.len(),
            if use_signers { signers.len() } else { 0 } + sym_args.len()
        );

        // find value types other than signers
        let arg_index_start = if use_signers {
            let num_signers = signers.len();
            debug_assert_ne!(num_signers, 0);
            debug_assert!(
                (1..num_signers).all(|i| match val_arg_sigs.0.get(i).unwrap() {
                    SignatureToken::Reference(inner) => matches!(&**inner, SignatureToken::Signer),
                    _ => false,
                })
            );
            num_signers
        } else {
            0
        };

        // turn transaction argument into values
        let mut sym_inputs: Vec<SymValue> = vec![];
        if use_signers {
            for signer in signers {
                sym_inputs.push(SymValue::from_transaction_argument(
                    &self.smt_ctxt,
                    &SignatureToken::Signer,
                    &SymTransactionArgument::Concrete(TransactionArgument::Address(*signer)),
                ));
            }
        }
        for (i, arg) in sym_args.iter().enumerate() {
            sym_inputs.push(SymValue::from_transaction_argument(
                &self.smt_ctxt,
                val_arg_sigs.0.get(arg_index_start + i).unwrap(),
                arg,
            ));
        }

        // prepare the first frame (locals + stack), in particular, the
        // locals consist of two parts
        // - the arguments, which have initial symbolic values set and
        // - the local variables, which are empty in the beginning
        let init_local_sigs = self.script.signature_at(self.script.code().locals);
        let mut call_stack = vec![SymFrame::new(sym_inputs, init_local_sigs.len())];
        let mut scc_stack = vec![];

        // symbolically walk the exec graph
        let mut walker = ExecWalker::new(self.exec_graph);
        while let Some(walker_step) = walker.next() {
            match walker_step {
                ExecWalkerStep::SccEntry(scc_id) => {
                    scc_stack.push(scc_id);
                }
                ExecWalkerStep::SccExit(scc_id) => {
                    let exiting_scc_id = scc_stack.pop().unwrap();
                    debug_assert_eq!(scc_id, exiting_scc_id);
                }
                ExecWalkerStep::Block(block) => {
                    self.symbolize_block(block, &mut call_stack);
                }
            }
        }

        // we should have nothing left in the stack after execution
        debug_assert!(scc_stack.is_empty());
        // TODO: check call_stack is empty
    }

    fn symbolize_block<'smt>(
        &'smt self,
        exec_block: &ExecBlock,
        call_stack: &mut Vec<SymFrame<'smt>>,
    ) {
        let exec_unit = self
            .setup
            .get_exec_unit_by_context(&exec_block.code_context)
            .unwrap();

        let current_frame = call_stack.last_mut().unwrap();
        for instruction in &exec_block.instructions {
            match instruction {
                // stack operations
                Bytecode::Pop => {
                    current_frame.stack_pop();
                }
                // loading constants
                Bytecode::LdU8(val) => {
                    current_frame.stack_push(SymValue::u8_const(&self.smt_ctxt, *val))
                }
                Bytecode::LdU64(val) => {
                    current_frame.stack_push(SymValue::u64_const(&self.smt_ctxt, *val))
                }
                Bytecode::LdU128(val) => {
                    current_frame.stack_push(SymValue::u128_const(&self.smt_ctxt, *val))
                }
                Bytecode::LdTrue => {
                    current_frame.stack_push(SymValue::bool_const(&self.smt_ctxt, true))
                }
                Bytecode::LdFalse => {
                    current_frame.stack_push(SymValue::bool_const(&self.smt_ctxt, false))
                }
                Bytecode::LdConst(idx) => {
                    let val_constant =
                        Value::deserialize_constant(exec_unit.constant_at(*idx)).unwrap();
                    if let Ok(val_integer) = val_constant
                        .copy_value()
                        .unwrap()
                        .value_as::<IntegerValue>()
                    {
                        match val_integer {
                            IntegerValue::U8(val) => {
                                current_frame.stack_push(SymValue::u8_const(&self.smt_ctxt, val));
                            }
                            IntegerValue::U64(val) => {
                                current_frame.stack_push(SymValue::u64_const(&self.smt_ctxt, val));
                            }
                            IntegerValue::U128(val) => {
                                current_frame.stack_push(SymValue::u128_const(&self.smt_ctxt, val));
                            }
                        }
                    } else if let Ok(val_address) = val_constant
                        .copy_value()
                        .unwrap()
                        .value_as::<AccountAddress>()
                    {
                        current_frame
                            .stack_push(SymValue::address_const(&self.smt_ctxt, val_address));
                    } else if let Ok(val_vector_u8) =
                        val_constant.copy_value().unwrap().value_as::<Vec<u8>>()
                    {
                        current_frame
                            .stack_push(SymValue::vector_u8_const(&self.smt_ctxt, val_vector_u8));
                    } else {
                        panic!(
                            "Loading arbitrary types of constants is not yet supported: {:?}",
                            val_constant
                        );
                    }
                }
                // cast operations
                Bytecode::CastU8 => {
                    // TODO: check out-of-bound possibility
                    let sym = current_frame.stack_pop();
                    current_frame.stack_push(sym.cast_u8());
                }
                Bytecode::CastU64 => {
                    // TODO: check out-of-bound possibility
                    let sym = current_frame.stack_pop();
                    current_frame.stack_push(sym.cast_u64());
                }
                Bytecode::CastU128 => {
                    // TODO: check out-of-bound possibility
                    let sym = current_frame.stack_pop();
                    current_frame.stack_push(sym.cast_u128());
                }
                // arithmetic operations
                Bytecode::Add => {
                    // TODO: check overflow
                    let rhs = current_frame.stack_pop();
                    let lhs = current_frame.stack_pop();
                    current_frame.stack_push(lhs.add(&rhs));
                }
                Bytecode::Sub => {
                    // TODO: check underflow
                    let rhs = current_frame.stack_pop();
                    let lhs = current_frame.stack_pop();
                    current_frame.stack_push(lhs.sub(&rhs));
                }
                Bytecode::Mul => {
                    // TODO: check overflow
                    let rhs = current_frame.stack_pop();
                    let lhs = current_frame.stack_pop();
                    current_frame.stack_push(lhs.mul(&rhs));
                }
                Bytecode::Mod => {
                    // NOTE: unsigned rem cannot over- or under-flow
                    let rhs = current_frame.stack_pop();
                    let lhs = current_frame.stack_pop();
                    current_frame.stack_push(lhs.rem(&rhs));
                }
                Bytecode::Div => {
                    // NOTE: unsigned div cannot over- or under-flow
                    let rhs = current_frame.stack_pop();
                    let lhs = current_frame.stack_pop();
                    current_frame.stack_push(lhs.div(&rhs));
                }
                // bitwise operations
                Bytecode::BitAnd => {
                    let rhs = current_frame.stack_pop();
                    let lhs = current_frame.stack_pop();
                    current_frame.stack_push(lhs.bit_and(&rhs));
                }
                Bytecode::BitOr => {
                    let rhs = current_frame.stack_pop();
                    let lhs = current_frame.stack_pop();
                    current_frame.stack_push(lhs.bit_or(&rhs));
                }
                Bytecode::Xor => {
                    let rhs = current_frame.stack_pop();
                    let lhs = current_frame.stack_pop();
                    current_frame.stack_push(lhs.bit_xor(&rhs));
                }
                Bytecode::Shl => {
                    let rhs = current_frame.stack_pop();
                    let lhs = current_frame.stack_pop();
                    current_frame.stack_push(lhs.shl(&rhs));
                }
                Bytecode::Shr => {
                    let rhs = current_frame.stack_pop();
                    let lhs = current_frame.stack_pop();
                    current_frame.stack_push(lhs.shr(&rhs));
                }
                // comparison operations
                Bytecode::Gt => {
                    let rhs = current_frame.stack_pop();
                    let lhs = current_frame.stack_pop();
                    current_frame.stack_push(lhs.gt(&rhs));
                }
                Bytecode::Ge => {
                    let rhs = current_frame.stack_pop();
                    let lhs = current_frame.stack_pop();
                    current_frame.stack_push(lhs.ge(&rhs));
                }
                Bytecode::Le => {
                    let rhs = current_frame.stack_pop();
                    let lhs = current_frame.stack_pop();
                    current_frame.stack_push(lhs.le(&rhs));
                }
                Bytecode::Lt => {
                    let rhs = current_frame.stack_pop();
                    let lhs = current_frame.stack_pop();
                    current_frame.stack_push(lhs.lt(&rhs));
                }
                // boolean operations
                Bytecode::And => {
                    let rhs = current_frame.stack_pop();
                    let lhs = current_frame.stack_pop();
                    current_frame.stack_push(lhs.and(&rhs));
                }
                Bytecode::Or => {
                    let rhs = current_frame.stack_pop();
                    let lhs = current_frame.stack_pop();
                    current_frame.stack_push(lhs.or(&rhs));
                }
                Bytecode::Not => {
                    let sym = current_frame.stack_pop();
                    current_frame.stack_push(sym.not());
                }
                // generic equality
                Bytecode::Eq => {
                    let rhs = current_frame.stack_pop();
                    let lhs = current_frame.stack_pop();
                    current_frame.stack_push(lhs.eq(&rhs));
                }
                Bytecode::Neq => {
                    let rhs = current_frame.stack_pop();
                    let lhs = current_frame.stack_pop();
                    current_frame.stack_push(lhs.ne(&rhs));
                }
                // struct constructions
                Bytecode::Pack(idx) => {
                    let struct_context = exec_unit.struct_context_by_def_index(*idx);
                    self.struct_pack(&struct_context, &[], current_frame);
                }
                Bytecode::PackGeneric(idx) => {
                    let struct_context = exec_unit.struct_context_by_generic_index(*idx);
                    let struct_inst_sig =
                        exec_unit.struct_instantiation_signature_by_generic_index(*idx);
                    let inst_args: Vec<ExecTypeArg> = struct_inst_sig
                        .0
                        .iter()
                        .map(|token| {
                            ExecTypeArg::convert_from_signature_token(
                                token,
                                &exec_unit.as_comp_unit(),
                                &exec_block.type_args,
                            )
                        })
                        .collect();
                    self.struct_pack(&struct_context, &inst_args, current_frame);
                }
                Bytecode::Unpack(idx) => {
                    let struct_context = exec_unit.struct_context_by_def_index(*idx);
                    self.struct_unpack(&struct_context, &[], current_frame);
                }
                Bytecode::UnpackGeneric(idx) => {
                    let struct_context = exec_unit.struct_context_by_generic_index(*idx);
                    let struct_inst_sig =
                        exec_unit.struct_instantiation_signature_by_generic_index(*idx);
                    let inst_args: Vec<ExecTypeArg> = struct_inst_sig
                        .0
                        .iter()
                        .map(|token| {
                            ExecTypeArg::convert_from_signature_token(
                                token,
                                &exec_unit.as_comp_unit(),
                                &exec_block.type_args,
                            )
                        })
                        .collect();
                    self.struct_unpack(&struct_context, &inst_args, current_frame);
                }
                // manipulations over local slots
                Bytecode::CopyLoc(idx) => {
                    let sym = current_frame.local_copy(*idx as usize);
                    // TODO: worry about uninitialized read?
                    current_frame.stack_push(sym.unwrap());
                }
                Bytecode::MoveLoc(idx) => {
                    let sym = current_frame.local_move(*idx as usize);
                    // TODO: worry about uninitialized read?
                    current_frame.stack_push(sym.unwrap());
                }
                Bytecode::StLoc(idx) => {
                    let sym = current_frame.stack_pop();
                    // TODO: worry about store index overflow?
                    current_frame.local_store(*idx as usize, sym);
                }
                // misc
                Bytecode::Nop => {}
                // the rest
                _ => {
                    println!("INSTRUCTION NOT SUPPORTED: {:?}", instruction);
                }
            }
        }
    }

    // utility functions
    fn struct_pack<'smt>(
        &'smt self,
        struct_context: &StructContext,
        struct_type_args: &[ExecTypeArg],
        current_frame: &mut SymFrame<'smt>,
    ) {
        let struct_name = self
            .type_graph
            .get_struct_name(&struct_context, struct_type_args)
            .unwrap();
        let struct_info = self.type_graph.get_struct_info_by_name(struct_name);
        match struct_info {
            ExecStructInfo::Native => panic!("Native struct is not supported yet"),
            ExecStructInfo::Declared { field_vec, .. } => {
                let struct_kind = SmtKind::Struct {
                    struct_name: struct_name.to_owned(),
                };
                let fields: Vec<SymValue> = (0..field_vec.len())
                    .map(|_| current_frame.stack_pop())
                    .collect();
                let field_refs: Vec<&SymValue> = fields.iter().map(|field| field).collect();
                let sym = SymValue::struct_const(&self.smt_ctxt, &struct_kind, &field_refs);
                current_frame.stack_push(sym);
            }
        }
    }

    fn struct_unpack<'smt>(
        &'smt self,
        struct_context: &StructContext,
        struct_type_args: &[ExecTypeArg],
        current_frame: &mut SymFrame<'smt>,
    ) {
        let struct_name = self
            .type_graph
            .get_struct_name(&struct_context, struct_type_args)
            .unwrap();
        let struct_info = self.type_graph.get_struct_info_by_name(struct_name);
        match struct_info {
            ExecStructInfo::Native => panic!("Native struct is not supported yet"),
            ExecStructInfo::Declared { field_vec, .. } => {
                let sym = current_frame.stack_pop();
                for field_sym in sym.unpack(field_vec.len()) {
                    current_frame.stack_push(field_sym);
                }
            }
        }
    }
}
