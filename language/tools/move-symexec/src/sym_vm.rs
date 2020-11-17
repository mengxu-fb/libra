// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use itertools::Itertools;
use log::{debug, warn};
use std::collections::HashMap;

use move_core_types::{account_address::AccountAddress, transaction_argument::TransactionArgument};
use move_vm_types::values::{IntegerValue, Value};
use vm::{
    access::ScriptAccess,
    file_format::{Bytecode, CodeOffset, CompiledScript, SignatureToken},
};

use crate::{
    sym_exec_graph::{ExecBlock, ExecBlockId, ExecGraph, ExecSccId, ExecWalker, ExecWalkerStep},
    sym_setup::{ExecStructInfo, ExecTypeArg, StructContext, SymSetup},
    sym_smtlib::{SmtCtxt, SmtExpr, SmtKind, SmtResult},
    sym_type_graph::TypeGraph,
    sym_vm_types::{SymFrame, SymTransactionArgument, SymValue},
};

/// Config: whether to simplify smt expressions upon construction
const CONF_SMT_AUTO_SIMPLIFY: bool = true;

#[derive(Clone, Debug, Eq, Hash, PartialEq, Ord, PartialOrd)]
struct SymIntraSccFlow {
    src_scc_id: ExecSccId,
    src_block_id: ExecBlockId,
    dst_scc_id: ExecSccId,
    dst_block_id: ExecBlockId,
}

struct SymSccInfo<'smt> {
    /// The scc_id where all scc_ids in the edge_conds resides in
    scc_id: Option<ExecSccId>,
    /// Entry condition
    entry_cond: SmtExpr<'smt>,
    /// Conditions for flows (i.e., edges) within this scc only
    edge_conds: HashMap<SymIntraSccFlow, SmtExpr<'smt>>,
}

impl<'smt> SymSccInfo<'smt> {
    fn for_base(ctxt: &'smt SmtCtxt) -> Self {
        Self {
            scc_id: None,
            entry_cond: ctxt.bool_const(true),
            edge_conds: HashMap::new(),
        }
    }

    fn for_cycle(ctxt: &'smt SmtCtxt, scc_id: ExecSccId) -> Self {
        Self {
            scc_id: Some(scc_id),
            // TODO: this is a fake condition
            entry_cond: ctxt.bool_const(true),
            edge_conds: HashMap::new(),
        }
    }

    /// Get the condition associated with this edge (panic if non-exist)
    fn get_edge_cond(
        &self,
        src_scc_id: ExecSccId,
        src_block_id: ExecBlockId,
        dst_scc_id: ExecSccId,
        dst_block_id: ExecBlockId,
    ) -> &SmtExpr<'smt> {
        let key = SymIntraSccFlow {
            src_scc_id,
            src_block_id,
            dst_scc_id,
            dst_block_id,
        };
        self.edge_conds.get(&key).unwrap()
    }

    /// Put the condition associated with this edge (panic if exists)
    fn put_edge_cond(
        &mut self,
        src_scc_id: ExecSccId,
        src_block_id: ExecBlockId,
        dst_scc_id: ExecSccId,
        dst_block_id: ExecBlockId,
        condition: SmtExpr<'smt>,
    ) {
        let key = SymIntraSccFlow {
            src_scc_id,
            src_block_id,
            dst_scc_id,
            dst_block_id,
        };
        let exists = self.edge_conds.insert(key, condition);
        debug_assert!(exists.is_none());
    }
}

enum SymBlockTermReason {
    Normal,
    Ret,
}

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

        // tracks the sccs that contain cycles only (except the base),
        // and this is by definition -- an scc containing a single block
        // will not be able to form a stack.
        let mut scc_stack = vec![SymSccInfo::for_base(&self.smt_ctxt)];

        // symbolically walk the exec graph
        let mut walker = ExecWalker::new(self.exec_graph);
        while let Some(walker_step) = walker.next() {
            match walker_step {
                ExecWalkerStep::CycleEntry { scc_id } => {
                    scc_stack.push(SymSccInfo::for_cycle(&self.smt_ctxt, scc_id));
                }
                ExecWalkerStep::CycleExit { scc_id } => {
                    let exiting_scc_id = scc_stack.pop().unwrap().scc_id.unwrap();
                    debug_assert_eq!(scc_id, exiting_scc_id);
                }
                ExecWalkerStep::Block {
                    scc_id,
                    block,
                    incoming_edges,
                    outgoing_edges,
                } => {
                    // log information
                    debug!("Block: {}::{}", scc_id, block.block_id);
                    debug!(
                        "Incoming edges: [{}]",
                        incoming_edges
                            .iter()
                            .map(|(edge_scc_id, edge_block_id)| format!(
                                "{}::{}",
                                edge_scc_id, edge_block_id
                            ))
                            .join("-")
                    );
                    debug!(
                        "Outgoing edges: [{}]",
                        outgoing_edges
                            .iter()
                            .map(|(edge_scc_id, edge_block_id)| format!(
                                "{}::{}",
                                edge_scc_id, edge_block_id
                            ))
                            .join("-")
                    );

                    // derive the reachability condition for this block
                    let mut scc_info = scc_stack.last_mut().unwrap();
                    let reach_cond = if incoming_edges.is_empty() {
                        // this is the entry block of this scc, so,
                        // just simply take the entry condition
                        scc_info.entry_cond.clone()
                    } else {
                        incoming_edges.iter().fold(
                            self.smt_ctxt.bool_const(false),
                            |cond, (src_scc_id, src_block_id)| {
                                cond.or(scc_info.get_edge_cond(
                                    *src_scc_id,
                                    *src_block_id,
                                    scc_id,
                                    block.block_id,
                                ))
                            },
                        )
                    };
                    debug!("Reaching condition: {}", reach_cond);

                    // if this block is not even reachable, shortcut the
                    // execution and do not go into the block
                    let feasible = match self.smt_ctxt.solve(&[&reach_cond]) {
                        SmtResult::SAT => true,
                        SmtResult::UNSAT => false,
                        SmtResult::UNKNOWN => {
                            // TODO: assume that things are decidable for now
                            panic!("SMT solver returns an unknown result");
                        }
                    };
                    if !feasible {
                        for (dst_scc_id, dst_block_id) in outgoing_edges {
                            scc_info.put_edge_cond(
                                scc_id,
                                block.block_id,
                                dst_scc_id,
                                dst_block_id,
                                self.smt_ctxt.bool_const(false),
                            );
                        }
                        continue;
                    }

                    // go over the block
                    let term = self.symbolize_block(
                        scc_id,
                        block,
                        &reach_cond,
                        &outgoing_edges,
                        &mut scc_info,
                        &mut call_stack,
                    );

                    match term {
                        SymBlockTermReason::Normal => {}
                        SymBlockTermReason::Ret => {
                            let mut current_frame = call_stack.pop().unwrap();

                            let exec_unit = self
                                .setup
                                .get_exec_unit_by_context(&block.code_context)
                                .unwrap();
                            let returns_num_opt =
                                exec_unit.returns_signature().map(|sig| sig.len());

                            if let Some(returns_num) = returns_num_opt {
                                let parent_frame = call_stack.last_mut().unwrap();

                                // clear the arguments
                                let params_num = exec_unit.params_signature().len();
                                for _ in 0..params_num {
                                    parent_frame.stack_pop();
                                }

                                // transfer the return values
                                SymFrame::stack_transfer(
                                    &mut current_frame,
                                    parent_frame,
                                    returns_num,
                                );
                            } else {
                                // we are returning from the script
                                debug_assert!(call_stack.is_empty());
                            }
                        }
                    }
                }
            }
        }

        // pop the base scc
        let base_scc = scc_stack.pop().unwrap();
        debug_assert!(base_scc.scc_id.is_none());

        // we should have nothing left in the stack after execution
        debug_assert!(scc_stack.is_empty());
        debug_assert!(call_stack.is_empty());
    }

    fn symbolize_block<'smt>(
        &'smt self,
        scc_id: ExecSccId,
        exec_block: &ExecBlock,
        reach_cond: &SmtExpr<'smt>,
        outgoing_edges: &[(ExecSccId, ExecBlockId)],
        scc_info: &mut SymSccInfo<'smt>,
        call_stack: &mut Vec<SymFrame<'smt>>,
    ) -> SymBlockTermReason {
        let exec_unit = self
            .setup
            .get_exec_unit_by_context(&exec_block.code_context)
            .unwrap();
        let current_frame = call_stack.last_mut().unwrap();

        for (pos, instruction) in exec_block.instructions.iter().enumerate() {
            debug!("Instruction {}: {:?}", pos, instruction);
            match instruction {
                // stack operations
                Bytecode::Pop => {
                    current_frame.stack_pop();
                }
                Bytecode::Ret => {
                    debug_assert_eq!(pos + 1, exec_block.instructions.len());
                    return SymBlockTermReason::Ret;
                }
                // loading constants
                Bytecode::LdU8(val) => {
                    current_frame.stack_push(SymValue::u8_const(&self.smt_ctxt, *val, reach_cond))
                }
                Bytecode::LdU64(val) => {
                    current_frame.stack_push(SymValue::u64_const(&self.smt_ctxt, *val, reach_cond))
                }
                Bytecode::LdU128(val) => {
                    current_frame.stack_push(SymValue::u128_const(&self.smt_ctxt, *val, reach_cond))
                }
                Bytecode::LdTrue => {
                    current_frame.stack_push(SymValue::bool_const(&self.smt_ctxt, true, reach_cond))
                }
                Bytecode::LdFalse => {
                    current_frame.stack_push(SymValue::bool_const(
                        &self.smt_ctxt,
                        false,
                        reach_cond,
                    ));
                }
                Bytecode::LdConst(idx) => {
                    let val_constant =
                        Value::deserialize_constant(exec_unit.constant_at(*idx)).unwrap();
                    let sym = if let Ok(val_integer) = val_constant
                        .copy_value()
                        .unwrap()
                        .value_as::<IntegerValue>()
                    {
                        match val_integer {
                            IntegerValue::U8(val) => {
                                SymValue::u8_const(&self.smt_ctxt, val, reach_cond)
                            }
                            IntegerValue::U64(val) => {
                                SymValue::u64_const(&self.smt_ctxt, val, reach_cond)
                            }
                            IntegerValue::U128(val) => {
                                SymValue::u128_const(&self.smt_ctxt, val, reach_cond)
                            }
                        }
                    } else if let Ok(val_address) = val_constant
                        .copy_value()
                        .unwrap()
                        .value_as::<AccountAddress>()
                    {
                        SymValue::address_const(&self.smt_ctxt, val_address, reach_cond)
                    } else if let Ok(val_vector_u8) =
                        val_constant.copy_value().unwrap().value_as::<Vec<u8>>()
                    {
                        SymValue::vector_u8_const(&self.smt_ctxt, val_vector_u8, reach_cond)
                    } else {
                        panic!(
                            "Loading arbitrary types of constants is not yet supported: {:?}",
                            val_constant
                        );
                    };
                    current_frame.stack_push(sym);
                }
                // cast operations
                Bytecode::CastU8 => {
                    // TODO: check out-of-bound possibility
                    let sym = current_frame.stack_pop();
                    current_frame.stack_push(sym.cast_u8(reach_cond));
                }
                Bytecode::CastU64 => {
                    // TODO: check out-of-bound possibility
                    let sym = current_frame.stack_pop();
                    current_frame.stack_push(sym.cast_u64(reach_cond));
                }
                Bytecode::CastU128 => {
                    // TODO: check out-of-bound possibility
                    let sym = current_frame.stack_pop();
                    current_frame.stack_push(sym.cast_u128(reach_cond));
                }
                // arithmetic operations
                Bytecode::Add => {
                    // TODO: check overflow
                    let rhs = current_frame.stack_pop();
                    let lhs = current_frame.stack_pop();
                    current_frame.stack_push(lhs.add(&rhs, reach_cond));
                }
                Bytecode::Sub => {
                    // TODO: check underflow
                    let rhs = current_frame.stack_pop();
                    let lhs = current_frame.stack_pop();
                    current_frame.stack_push(lhs.sub(&rhs, reach_cond));
                }
                Bytecode::Mul => {
                    // TODO: check overflow
                    let rhs = current_frame.stack_pop();
                    let lhs = current_frame.stack_pop();
                    current_frame.stack_push(lhs.mul(&rhs, reach_cond));
                }
                Bytecode::Mod => {
                    // NOTE: unsigned rem cannot over- or under-flow
                    let rhs = current_frame.stack_pop();
                    let lhs = current_frame.stack_pop();
                    current_frame.stack_push(lhs.rem(&rhs, reach_cond));
                }
                Bytecode::Div => {
                    // NOTE: unsigned div cannot over- or under-flow
                    let rhs = current_frame.stack_pop();
                    let lhs = current_frame.stack_pop();
                    current_frame.stack_push(lhs.div(&rhs, reach_cond));
                }
                // bitwise operations
                Bytecode::BitAnd => {
                    let rhs = current_frame.stack_pop();
                    let lhs = current_frame.stack_pop();
                    current_frame.stack_push(lhs.bit_and(&rhs, reach_cond));
                }
                Bytecode::BitOr => {
                    let rhs = current_frame.stack_pop();
                    let lhs = current_frame.stack_pop();
                    current_frame.stack_push(lhs.bit_or(&rhs, reach_cond));
                }
                Bytecode::Xor => {
                    let rhs = current_frame.stack_pop();
                    let lhs = current_frame.stack_pop();
                    current_frame.stack_push(lhs.bit_xor(&rhs, reach_cond));
                }
                Bytecode::Shl => {
                    let rhs = current_frame.stack_pop();
                    let lhs = current_frame.stack_pop();
                    current_frame.stack_push(lhs.shl(&rhs, reach_cond));
                }
                Bytecode::Shr => {
                    let rhs = current_frame.stack_pop();
                    let lhs = current_frame.stack_pop();
                    current_frame.stack_push(lhs.shr(&rhs, reach_cond));
                }
                // comparison operations
                Bytecode::Gt => {
                    let rhs = current_frame.stack_pop();
                    let lhs = current_frame.stack_pop();
                    current_frame.stack_push(lhs.gt(&rhs, reach_cond));
                }
                Bytecode::Ge => {
                    let rhs = current_frame.stack_pop();
                    let lhs = current_frame.stack_pop();
                    current_frame.stack_push(lhs.ge(&rhs, reach_cond));
                }
                Bytecode::Le => {
                    let rhs = current_frame.stack_pop();
                    let lhs = current_frame.stack_pop();
                    current_frame.stack_push(lhs.le(&rhs, reach_cond));
                }
                Bytecode::Lt => {
                    let rhs = current_frame.stack_pop();
                    let lhs = current_frame.stack_pop();
                    current_frame.stack_push(lhs.lt(&rhs, reach_cond));
                }
                // boolean operations
                Bytecode::And => {
                    let rhs = current_frame.stack_pop();
                    let lhs = current_frame.stack_pop();
                    current_frame.stack_push(lhs.and(&rhs, reach_cond));
                }
                Bytecode::Or => {
                    let rhs = current_frame.stack_pop();
                    let lhs = current_frame.stack_pop();
                    current_frame.stack_push(lhs.or(&rhs, reach_cond));
                }
                Bytecode::Not => {
                    let sym = current_frame.stack_pop();
                    current_frame.stack_push(sym.not(reach_cond));
                }
                // generic equality
                Bytecode::Eq => {
                    let rhs = current_frame.stack_pop();
                    let lhs = current_frame.stack_pop();
                    current_frame.stack_push(lhs.eq(&rhs, reach_cond));
                }
                Bytecode::Neq => {
                    let rhs = current_frame.stack_pop();
                    let lhs = current_frame.stack_pop();
                    current_frame.stack_push(lhs.ne(&rhs, reach_cond));
                }
                // struct constructions
                Bytecode::Pack(idx) => {
                    let struct_context = exec_unit.struct_context_by_def_index(*idx);
                    self.struct_pack(&struct_context, &[], reach_cond, current_frame);
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
                    self.struct_pack(&struct_context, &inst_args, reach_cond, current_frame);
                }
                Bytecode::Unpack(idx) => {
                    let struct_context = exec_unit.struct_context_by_def_index(*idx);
                    self.struct_unpack(&struct_context, &[], reach_cond, current_frame);
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
                    self.struct_unpack(&struct_context, &inst_args, reach_cond, current_frame);
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
                // branching
                Bytecode::Branch(offset) => {
                    self.handle_branch(
                        *offset,
                        reach_cond,
                        scc_id,
                        exec_block.block_id,
                        outgoing_edges,
                        scc_info,
                    );
                }
                Bytecode::BrTrue(offset) => {
                    let sym = current_frame.stack_pop();
                    let cond_t = sym.flatten_as_predicate(true).and(reach_cond);
                    let cond_f = sym.flatten_as_predicate(false).and(reach_cond);

                    // we can safely unwrap the code_offset
                    self.handle_branch(
                        *offset,
                        &cond_t,
                        scc_id,
                        exec_block.block_id,
                        outgoing_edges,
                        scc_info,
                    );
                    self.handle_branch(
                        exec_block.code_offset.unwrap() + 1,
                        &cond_f,
                        scc_id,
                        exec_block.block_id,
                        outgoing_edges,
                        scc_info,
                    );
                }
                Bytecode::BrFalse(offset) => {
                    let sym = current_frame.stack_pop();
                    let cond_t = sym.flatten_as_predicate(true).and(reach_cond);
                    let cond_f = sym.flatten_as_predicate(false).and(reach_cond);

                    // we can safely unwrap the code_offset
                    self.handle_branch(
                        *offset,
                        &cond_f,
                        scc_id,
                        exec_block.block_id,
                        outgoing_edges,
                        scc_info,
                    );
                    self.handle_branch(
                        exec_block.code_offset.unwrap() + 1,
                        &cond_t,
                        scc_id,
                        exec_block.block_id,
                        outgoing_edges,
                        scc_info,
                    );
                }
                // misc
                Bytecode::Nop => {}
                // the rest
                _ => {
                    println!("INSTRUCTION NOT SUPPORTED: {:?}", instruction);
                }
            }
        }

        // normal block end
        SymBlockTermReason::Normal
    }

    // utility functions
    fn struct_pack<'smt>(
        &'smt self,
        struct_context: &StructContext,
        struct_type_args: &[ExecTypeArg],
        reach_cond: &SmtExpr<'smt>,
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
                let sym =
                    SymValue::struct_const(&self.smt_ctxt, &struct_kind, &field_refs, reach_cond);
                current_frame.stack_push(sym);
            }
        }
    }

    fn struct_unpack<'smt>(
        &'smt self,
        struct_context: &StructContext,
        struct_type_args: &[ExecTypeArg],
        reach_cond: &SmtExpr<'smt>,
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
                for field_sym in sym.unpack(field_vec.len(), reach_cond) {
                    current_frame.stack_push(field_sym);
                }
            }
        }
    }

    fn handle_branch<'smt>(
        &'smt self,
        offset: CodeOffset,
        branch_cond: &SmtExpr<'smt>,
        src_scc_id: ExecSccId,
        src_block_id: ExecBlockId,
        outgoing_edges: &[(ExecSccId, ExecBlockId)],
        scc_info: &mut SymSccInfo<'smt>,
    ) {
        let mut branch_targets: Vec<&(ExecSccId, ExecBlockId)> = outgoing_edges
            .iter()
            .filter(|(_, out_block_id)| {
                self.exec_graph
                    .get_block_by_block_id(*out_block_id)
                    .code_offset
                    // there is no way to branch into an
                    // artificial block, so if the code_offset is None,
                    // simply return false
                    .map_or(false, |code_offset| code_offset == offset)
            })
            .collect();

        if let Some((dst_scc_id, dst_block_id)) = branch_targets.pop() {
            scc_info.put_edge_cond(
                src_scc_id,
                src_block_id,
                *dst_scc_id,
                *dst_block_id,
                branch_cond.clone(),
            );
        }
        // there is at max one target
        debug_assert!(branch_targets.is_empty());
    }
}
