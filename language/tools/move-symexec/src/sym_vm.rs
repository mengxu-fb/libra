// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use itertools::Itertools;
use log::{debug, warn};
use std::collections::HashMap;

use bytecode::stackless_bytecode::{AssignKind, Bytecode, Constant, Operation};
use move_core_types::account_address::AccountAddress;
use spec_lang::ty::{PrimitiveType, Type};

use crate::{
    sym_exec_graph::{ExecBlock, ExecBlockId, ExecGraph, ExecSccId, ExecWalker, ExecWalkerStep},
    sym_oracle::SymOracle,
    sym_smtlib::{SmtCtxt, SmtExpr, SmtKind},
    sym_type_graph::{ExecStructInfo, TypeGraph},
    sym_typing::ExecTypeArg,
    sym_vm_types::{SymFrame, SymTransactionArgument, SymValue, ADDRESS_SMT_KIND, SIGNER_SMT_KIND},
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

/// The symbolic interpreter that examines instructions one by one
pub(crate) struct SymVM<'env, 'sym> {
    /// A wrapper over the smt solver context manager
    smt_ctxt: SmtCtxt,
    /// The oracle for environmental information
    oracle: &'env SymOracle<'env>,
    /// The execution graph containing all code
    exec_graph: &'sym ExecGraph<'env>,
    /// Maps all struct types to names of the corresponding smt types
    type_graph: &'sym TypeGraph<'env>,
}

impl<'env, 'sym> SymVM<'env, 'sym> {
    pub fn new(
        oracle: &'env SymOracle<'env>,
        exec_graph: &'sym ExecGraph<'env>,
        type_graph: &'sym TypeGraph<'env>,
    ) -> Self {
        let mut smt_ctxt = SmtCtxt::new(CONF_SMT_AUTO_SIMPLIFY);

        // pre-compute the types for move first class citizens
        smt_ctxt.create_move_type_address();
        smt_ctxt.create_move_type_signer();

        // pre-compute the struct smt types
        for (struct_name, struct_info) in type_graph.reverse_topological_sort() {
            match struct_info {
                ExecStructInfo::Native => {
                    // TODO: we should have a dedicated modeling for native struct types
                    warn!("A native struct type is ignored: {}", struct_name)
                }
                ExecStructInfo::Declared {
                    field_vec,
                    field_map,
                } => {
                    let field_smt_kinds: Vec<(String, SmtKind)> = field_vec
                        .iter()
                        .map(|field_env| {
                            (
                                field_env
                                    .struct_env
                                    .symbol_pool()
                                    .string(field_env.get_name())
                                    .as_str()
                                    .to_owned(),
                                type_arg_to_smt_kind(
                                    field_map.get(&field_env.get_id()).unwrap(),
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
            oracle,
            exec_graph,
            type_graph,
        }
    }

    pub fn interpret(
        &self,
        sigs_opt: Option<&[AccountAddress]>,
        sym_args: &[SymTransactionArgument],
    ) -> Result<()> {
        // get the script exec unit to kickstart the symbolization
        let script_main = self.oracle.get_script_exec_unit();
        let script_data = script_main.get_target();
        let params = script_main.func_env.get_parameters();

        // turn signers into values
        let mut sym_inputs: Vec<SymValue> = vec![];
        if let Some(signers) = sigs_opt {
            let signer_type =
                Type::Reference(false, Box::new(Type::Primitive(PrimitiveType::Signer)));
            for (i, signer) in signers.iter().enumerate() {
                debug_assert_eq!(params.get(i).unwrap().1, signer_type);
                sym_inputs.push(SymValue::signer_const(
                    &self.smt_ctxt,
                    *signer,
                    &self.smt_ctxt.bool_const(true),
                )?);
            }
        }

        // turn transaction argument into values
        let arg_index_start = sigs_opt.map_or(0, |signers| signers.len());
        for (i, arg) in sym_args.iter().enumerate() {
            sym_inputs.push(SymValue::from_transaction_argument(
                &self.smt_ctxt,
                &params.get(arg_index_start + i).unwrap().1,
                arg,
            )?);
        }
        debug_assert_eq!(sym_inputs.len(), script_data.get_parameter_count());

        // prepare the first frame, in particular, the input arguments
        let mut init_frame = SymFrame::new(&self.smt_ctxt, script_main.func_data.local_types.len());
        for (i, sym_arg) in sym_inputs.iter().enumerate() {
            debug!("Argument {}", i);
            init_frame.store_local(
                *script_data
                    .get_local_index(params.get(i).unwrap().0)
                    .unwrap(),
                sym_arg,
                &self.smt_ctxt.bool_const(true),
            )?;
        }
        for (input_index, local_index) in &script_main.func_data.param_proxy_map {
            debug!("Argument {}", input_index);
            init_frame.store_local(
                *local_index,
                sym_inputs.get(*input_index).unwrap(),
                &self.smt_ctxt.bool_const(true),
            )?;
        }
        let mut call_stack = vec![init_frame];

        // tracks the sccs that contain cycles only (except the base), and this is by definition,
        // i.e., an scc containing a single block will not be able to form a stack.
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
                    block_id,
                    incoming_edges,
                    outgoing_edges,
                } => {
                    // log information
                    debug!("Block: {} (scc: {})", block_id, scc_id);
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
                        // this is the entry block of this scc, so just take the entry condition
                        scc_info.entry_cond.clone()
                    } else {
                        incoming_edges.iter().fold(
                            self.smt_ctxt.bool_const(false),
                            |cond, (src_scc_id, src_block_id)| {
                                cond.or(scc_info.get_edge_cond(
                                    *src_scc_id,
                                    *src_block_id,
                                    scc_id,
                                    block_id,
                                ))
                            },
                        )
                    };
                    debug!("Reaching condition: {}", reach_cond);

                    // if this block is not even reachable, shortcut the execution
                    if !self.smt_ctxt.is_feasible_assume_solvable(&[&reach_cond])? {
                        for (dst_scc_id, dst_block_id) in outgoing_edges {
                            scc_info.put_edge_cond(
                                scc_id,
                                block_id,
                                dst_scc_id,
                                dst_block_id,
                                self.smt_ctxt.bool_const(false),
                            );
                        }
                        continue;
                    }

                    // now symbolize the block
                    let block = self.exec_graph.get_block_by_block_id(block_id);
                    let is_return_block = self.symbolize_block(
                        scc_id,
                        block,
                        &reach_cond,
                        &outgoing_edges,
                        &mut scc_info,
                        &mut call_stack,
                    )?;

                    // pop the call stack if this is a return block
                    if is_return_block {
                        let mut current_frame = call_stack.pop().unwrap();
                    }
                }
            }
        }

        // we should have nothing left in the stack after execution, unless the execution runs into
        // a function that only aborts but never returns
        if let Some(call_frame) = call_stack.pop() {
            debug_assert!(call_frame.get_returns().is_none());
        } else {
            // pop the base scc
            let base_scc = scc_stack.pop().unwrap();
            debug_assert!(base_scc.scc_id.is_none());
            debug_assert!(scc_stack.is_empty());
        }

        // done
        Ok(())
    }

    fn symbolize_block<'smt>(
        &'smt self,
        scc_id: ExecSccId,
        block: &ExecBlock<'env>,
        reach_cond: &SmtExpr<'smt>,
        outgoing_edges: &[(ExecSccId, ExecBlockId)],
        scc_info: &mut SymSccInfo<'smt>,
        call_stack: &mut Vec<SymFrame<'smt>>,
    ) -> Result<bool> {
        let func_env = block.exec_unit;
        let current_frame = call_stack.last_mut().unwrap();
        for (pos, instruction) in block.instructions.iter().enumerate() {
            debug!(
                "Instruction {}: {}",
                pos,
                instruction.display(func_env.get_target())
            );
            match instruction {
                Bytecode::Assign(_, dst, src, kind) => {
                    match kind {
                        // TODO: borrow analysis treats Move and Store equally, follow suite here
                        AssignKind::Move | AssignKind::Store => {
                            let sym = current_frame.move_local(*src, reach_cond)?;
                            current_frame.store_local(*dst, &sym, reach_cond)?;
                        }
                        AssignKind::Copy => {
                            let sym = current_frame.copy_local(*src, reach_cond)?;
                            current_frame.store_local(*dst, &sym, reach_cond)?;
                        }
                    }
                }
                Bytecode::Call(_, rets, op, args) => {
                    match op {
                        // builtins
                        Operation::Destroy => {
                            for idx in args {
                                current_frame.destroy_local(*idx, reach_cond)?;
                            }
                        }
                        _ => bail!("Operation not supported yet"),
                    }
                }
                Bytecode::Ret(_, rets) => {
                    // this block is a return block
                    debug_assert_eq!(pos + 1, block.instructions.len());
                    current_frame.set_returns(rets);
                    return Ok(true);
                }
                Bytecode::Load(_, dst, val) => {
                    let sym = self.symbolize_constant(val, reach_cond)?;
                    current_frame.store_local(*dst, &sym, reach_cond)?;
                }
                Bytecode::Branch(..) => bail!("Operation not supported yet"),
                Bytecode::Jump(..) => bail!("Operation not supported yet"),
                Bytecode::Abort(..) => {
                    // TODO: solve for reachable inputs
                }
                // nop or equivalent
                Bytecode::Label(..) | Bytecode::SpecBlock(..) | Bytecode::Nop(..) => {}
            };
        }

        // the block is not a return block
        Ok(false)
    }

    fn symbolize_constant<'smt>(
        &'smt self,
        val: &Constant,
        cond: &SmtExpr<'smt>,
    ) -> Result<SymValue<'smt>> {
        match val {
            Constant::Bool(v) => SymValue::bool_const(&self.smt_ctxt, *v, cond),
            Constant::U8(v) => SymValue::u8_const(&self.smt_ctxt, *v, cond),
            Constant::U64(v) => SymValue::u64_const(&self.smt_ctxt, *v, cond),
            Constant::U128(v) => SymValue::u128_const(&self.smt_ctxt, *v, cond),
            Constant::Address(v) => SymValue::address_const(
                &self.smt_ctxt,
                AccountAddress::from_hex_literal(&format!("{:#X}", v)).unwrap(),
                cond,
            ),
            Constant::ByteArray(v) => SymValue::vector_u8_const(&self.smt_ctxt, v.clone(), cond),
        }
    }
}

// utilities
fn type_arg_to_smt_kind(type_arg: &ExecTypeArg, type_graph: &TypeGraph) -> SmtKind {
    match type_arg {
        ExecTypeArg::Bool => SmtKind::Bool,
        ExecTypeArg::U8 => SmtKind::bitvec_u8(),
        ExecTypeArg::U64 => SmtKind::bitvec_u64(),
        ExecTypeArg::U128 => SmtKind::bitvec_u128(),
        ExecTypeArg::Address => ADDRESS_SMT_KIND.clone(),
        ExecTypeArg::Signer => SIGNER_SMT_KIND.clone(),
        ExecTypeArg::Vector { element_type } => SmtKind::Vector {
            element_kind: Box::new(type_arg_to_smt_kind(element_type.as_ref(), type_graph)),
        },
        ExecTypeArg::Struct {
            struct_info,
            type_args,
        } => SmtKind::Struct {
            struct_name: type_graph
                .get_struct_name(&struct_info.struct_id, type_args)
                .unwrap()
                .to_owned(),
        },
        ExecTypeArg::Reference { referred_type, .. } => SmtKind::Reference {
            referred_kind: Box::new(type_arg_to_smt_kind(referred_type.as_ref(), type_graph)),
        },
        ExecTypeArg::TypeParameter { actual_type, .. } => {
            type_arg_to_smt_kind(actual_type.as_ref(), type_graph)
        }
    }
}
