// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use std::{
    cmp::Ordering,
    collections::HashMap,
    ffi::{CStr, CString},
    fmt,
    os::raw::c_uint,
    ptr::null_mut,
};

use crate::deps_z3::*;

/// Possible results from the sat solver
pub enum SmtResult {
    SAT,
    UNSAT,
    UNKNOWN,
}

#[derive(Clone, Debug)]
pub struct SmtStructInfo {
    sort: Z3_sort,
    constructor: Z3_func_decl,
    field_kinds: Vec<SmtKind>,
    field_getters: Vec<Z3_func_decl>,
}

/// A context manager for all smt-related stuff
#[derive(Debug)]
pub struct SmtCtxt {
    /// A wrapper over Z3_context
    ctxt: Z3_context,
    /// A map of pre-defined structs
    struct_map: HashMap<String, SmtStructInfo>,
    /// Whether to simplify terms automatically
    conf_auto_simplify: bool,
}
// TODO: make SmtCtxt, SmtKind, SmtExpr all pub(crate)

impl SmtCtxt {
    pub fn new(conf_auto_simplify: bool) -> Self {
        let ctxt = unsafe {
            let cfg = Z3_mk_config();
            let ctx = Z3_mk_context(cfg);
            Z3_del_config(cfg);
            ctx
        };

        Self {
            ctxt,
            struct_map: HashMap::new(),
            conf_auto_simplify,
        }
    }

    // preparation for smt struct types
    pub fn create_smt_struct(
        &mut self,
        struct_name: String,
        struct_fields: Vec<(String, SmtKind)>,
    ) {
        // prepare fields
        let num_fields = struct_fields.len();
        let mut field_names: Vec<Z3_symbol> = vec![];
        let mut field_kinds: Vec<SmtKind> = vec![];
        let mut field_sorts: Vec<Z3_sort> = vec![];
        for (field_name, field_kind) in struct_fields.iter() {
            // derive field name
            let c_str = CString::new(field_name.as_str()).unwrap();
            let symbol = unsafe { Z3_mk_string_symbol(self.ctxt, c_str.as_ptr()) };
            field_names.push(symbol);

            // derive field sort
            field_sorts.push(field_kind.to_z3_sort(self));

            // record field kind
            field_kinds.push(field_kind.clone());
        }

        // prepare receivers
        let mut constructor: Z3_func_decl = null_mut();
        let mut field_getters: Vec<Z3_func_decl> = vec![null_mut(); num_fields];

        // make the tuple sort
        let c_str = CString::new(struct_name.as_str()).unwrap();
        let symbol = unsafe { Z3_mk_string_symbol(self.ctxt, c_str.as_ptr()) };
        let struct_sort = unsafe {
            Z3_mk_tuple_sort(
                self.ctxt,
                symbol,
                num_fields as c_uint,
                field_names.as_ptr(),
                field_sorts.as_ptr(),
                &mut constructor,
                field_getters.get_mut(0).unwrap(),
            )
        };

        // make the struct information pack
        let struct_info = SmtStructInfo {
            sort: struct_sort,
            constructor,
            field_kinds,
            field_getters,
        };
        let exists = self.struct_map.insert(struct_name, struct_info);
        debug_assert!(exists.is_none());
    }

    // context check
    pub fn smt_ctxt_matches(&self, ctxt: &SmtCtxt) -> bool {
        self.ctxt == ctxt.ctxt
    }

    // create bools
    pub fn bool_const(&self, val: bool) -> SmtExpr {
        let ast = if val {
            unsafe { Z3_mk_true(self.ctxt) }
        } else {
            unsafe { Z3_mk_false(self.ctxt) }
        };
        SmtExpr {
            ast,
            ctxt: self,
            kind: SmtKind::Bool,
        }
    }

    pub fn bool_var(&self, var: &str) -> SmtExpr {
        let kind = SmtKind::Bool;
        let c_str = CString::new(var).unwrap();
        let ast = unsafe {
            let symbol = Z3_mk_string_symbol(self.ctxt, c_str.as_ptr());
            Z3_mk_const(self.ctxt, symbol, kind.to_z3_sort(self))
        };
        SmtExpr {
            ast,
            ctxt: self,
            kind,
        }
    }

    // create bitvecs
    pub fn bitvec_const<T: ToString>(&self, val: T, signed: bool, width: u16) -> SmtExpr {
        let kind = SmtKind::Bitvec { signed, width };
        let str_repr = CString::new(val.to_string()).unwrap();
        let ast = unsafe { Z3_mk_numeral(self.ctxt, str_repr.as_ptr(), kind.to_z3_sort(self)) };
        SmtExpr {
            ast,
            ctxt: self,
            kind,
        }
    }

    pub fn bitvec_const_u8(&self, val: u8) -> SmtExpr {
        self.bitvec_const(val, false, 8)
    }

    pub fn bitvec_const_u64(&self, val: u64) -> SmtExpr {
        self.bitvec_const(val, false, 64)
    }

    pub fn bitvec_const_u128(&self, val: u128) -> SmtExpr {
        self.bitvec_const(val, false, 128)
    }

    pub fn bitvec_var(&self, var: &str, signed: bool, width: u16) -> SmtExpr {
        let kind = SmtKind::Bitvec { signed, width };
        let c_str = CString::new(var).unwrap();
        let ast = unsafe {
            let symbol = Z3_mk_string_symbol(self.ctxt, c_str.as_ptr());
            Z3_mk_const(self.ctxt, symbol, kind.to_z3_sort(self))
        };
        SmtExpr {
            ast,
            ctxt: self,
            kind,
        }
    }

    pub fn bitvec_var_u8(&self, var: &str) -> SmtExpr {
        self.bitvec_var(var, false, 8)
    }

    pub fn bitvec_var_u64(&self, var: &str) -> SmtExpr {
        self.bitvec_var(var, false, 64)
    }

    pub fn bitvec_var_u128(&self, var: &str) -> SmtExpr {
        self.bitvec_var(var, false, 128)
    }

    // create vectors (i.e., sequences)

    /// Create a vector with pre-defined contents (and hence, length). Although the function is
    /// named const, the contents are essentially smt expressions and thus, may include variables
    pub fn vector_const(&self, element_kind: &SmtKind, vals: &[&SmtExpr]) -> SmtExpr {
        debug_assert!(vals.iter().all(|expr| expr.kind == *element_kind));

        let kind = SmtKind::Vector {
            element_kind: Box::new(element_kind.clone()),
        };
        let unit_exprs: Vec<Z3_ast> = vals
            .iter()
            .map(|expr| unsafe { Z3_mk_seq_unit(self.ctxt, expr.ast) })
            .collect();
        let ast =
            unsafe { Z3_mk_seq_concat(self.ctxt, unit_exprs.len() as c_uint, unit_exprs.as_ptr()) };
        SmtExpr {
            ast,
            ctxt: self,
            kind,
        }
    }

    /// Create a vector with variable content and length
    pub fn vector_var(&self, element_kind: &SmtKind, var: &str) -> SmtExpr {
        let kind = SmtKind::Vector {
            element_kind: Box::new(element_kind.clone()),
        };
        let c_str = CString::new(var).unwrap();
        let ast = unsafe {
            let symbol = Z3_mk_string_symbol(self.ctxt, c_str.as_ptr());
            Z3_mk_const(self.ctxt, symbol, kind.to_z3_sort(self))
        };
        SmtExpr {
            ast,
            ctxt: self,
            kind,
        }
    }

    /// Create a struct with pre-defined contents. Similar to vector_const, although this function
    /// is named const, the contents are essentially smt expressions and may include variables
    pub fn struct_const(&self, struct_kind: &SmtKind, fields: &[&SmtExpr]) -> SmtExpr {
        // get struct name
        let struct_name = match struct_kind {
            SmtKind::Struct { struct_name } => struct_name,
            _ => {
                panic!("Invalid kind for struct construction");
            }
        };
        let struct_info = self.struct_map.get(struct_name).unwrap();

        // check type consistency
        let num_fields = fields.len();
        debug_assert_eq!(num_fields, struct_info.field_getters.len());

        // prepare arguments
        let fields_ast: Vec<Z3_ast> = fields.iter().map(|expr| expr.ast).collect();
        let ast = unsafe {
            Z3_mk_app(
                self.ctxt,
                struct_info.constructor,
                num_fields as c_uint,
                fields_ast.as_ptr(),
            )
        };

        // post-processing
        let kind = SmtKind::Struct {
            struct_name: struct_name.to_owned(),
        };
        let ast = self.postprocess(ast, &kind);
        SmtExpr {
            ast,
            ctxt: self,
            kind,
        }
    }

    /// Struct variable
    pub fn struct_var(&self, struct_kind: &SmtKind, var: &str) -> SmtExpr {
        let c_str = CString::new(var).unwrap();
        let ast = unsafe {
            let symbol = Z3_mk_string_symbol(self.ctxt, c_str.as_ptr());
            Z3_mk_const(self.ctxt, symbol, struct_kind.to_z3_sort(self))
        };
        SmtExpr {
            ast,
            ctxt: self,
            kind: struct_kind.clone(),
        }
    }

    // simplification
    fn simplify(&self, ast: Z3_ast, _kind: &SmtKind) -> Z3_ast {
        // TODO: in theory, we could have dedicated simplification procedures depending on the kind
        // of the ast. But for now, let's just use the default simplification procedure in Z3
        unsafe { Z3_simplify(self.ctxt, ast) }
    }

    // post-processing for an ast out of some operation
    fn postprocess(&self, ast: Z3_ast, kind: &SmtKind) -> Z3_ast {
        if self.conf_auto_simplify {
            self.simplify(ast, kind)
        } else {
            ast
        }
    }

    // sat solving
    pub fn solve(&self, constraints: &[&SmtExpr]) -> SmtResult {
        let asts: Vec<Z3_ast> = constraints.iter().map(|expr| expr.ast).collect();
        let result = unsafe {
            let solver = Z3_mk_solver(self.ctxt);
            Z3_solver_check_assumptions(self.ctxt, solver, asts.len() as c_uint, asts.as_ptr())
        };

        // convert to enum
        if result == Z3_lbool_Z3_L_TRUE {
            SmtResult::SAT
        } else if result == Z3_lbool_Z3_L_FALSE {
            SmtResult::UNSAT
        } else {
            debug_assert_eq!(result, Z3_lbool_Z3_L_UNDEF);
            SmtResult::UNKNOWN
        }
    }

    // TODO: this is not reasonable, but for simplicity...
    pub fn is_feasible_assume_solvable(&self, constraints: &[&SmtExpr]) -> Result<bool> {
        match self.solve(constraints) {
            SmtResult::SAT => Ok(true),
            SmtResult::UNSAT => Ok(false),
            SmtResult::UNKNOWN => {
                bail!("SMT solver returns an unknown result");
            }
        }
    }
}

impl Drop for SmtCtxt {
    fn drop(&mut self) {
        unsafe {
            Z3_del_context(self.ctxt);
        }
    }
}

/// Make the type of SmtExpr explicit
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SmtKind {
    Bool,
    Bitvec { signed: bool, width: u16 },
    Vector { element_kind: Box<SmtKind> },
    Struct { struct_name: String },
    // TODO: the reference type is for experiment only
    Reference { referred_kind: Box<SmtKind> },
}

impl SmtKind {
    // z3 linkage
    fn to_z3_sort(&self, ctxt: &SmtCtxt) -> Z3_sort {
        match self {
            SmtKind::Bool => unsafe { Z3_mk_bool_sort(ctxt.ctxt) },
            SmtKind::Bitvec { width, .. } => unsafe { Z3_mk_bv_sort(ctxt.ctxt, *width as c_uint) },
            SmtKind::Vector { element_kind } => unsafe {
                Z3_mk_seq_sort(ctxt.ctxt, element_kind.to_z3_sort(ctxt))
            },
            SmtKind::Struct { struct_name } => ctxt.struct_map.get(struct_name).unwrap().sort,
            SmtKind::Reference { referred_kind } => unsafe {
                Z3_mk_array_sort(
                    ctxt.ctxt,
                    Z3_mk_int_sort(ctxt.ctxt),
                    referred_kind.to_z3_sort(ctxt),
                )
            },
        }
    }

    // shortcuts
    pub fn bitvec_u8() -> Self {
        SmtKind::Bitvec {
            signed: false,
            width: 8,
        }
    }

    pub fn bitvec_u64() -> Self {
        SmtKind::Bitvec {
            signed: false,
            width: 64,
        }
    }

    pub fn bitvec_u128() -> Self {
        SmtKind::Bitvec {
            signed: false,
            width: 128,
        }
    }
}

/// A wrapper over Z3_ast
#[derive(Clone, Debug)]
pub struct SmtExpr<'smt> {
    ast: Z3_ast,
    ctxt: &'smt SmtCtxt,
    kind: SmtKind,
}

impl fmt::Display for SmtExpr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let sort_repr = unsafe {
            CStr::from_ptr(Z3_sort_to_string(
                self.ctxt.ctxt,
                self.kind.to_z3_sort(self.ctxt),
            ))
            .to_owned()
        }
        .into_string()
        .unwrap();
        let expr_repr =
            unsafe { CStr::from_ptr(Z3_ast_to_string(self.ctxt.ctxt, self.ast)).to_owned() }
                .into_string()
                .unwrap();
        write!(f, "[{}] {}", sort_repr, expr_repr)
    }
}

macro_rules! smt_unary_op_bool {
    ($func:tt, $expr:ident) => {{
        $expr.check_unary_op_bool();

        let ctxt = $expr.ctxt;
        let ast = unsafe { $func(ctxt.ctxt, $expr.ast) };

        let kind = SmtKind::Bool;
        let ast = ctxt.postprocess(ast, &kind);
        SmtExpr { ast, ctxt, kind }
    }};
}

macro_rules! smt_binary_op_bool {
    ($func:tt, $lhs:ident, $rhs:ident) => {{
        $lhs.check_binary_op_bool($rhs);

        let ctxt = $lhs.ctxt;
        let terms: [Z3_ast; 2] = [$lhs.ast, $rhs.ast];
        let ast = unsafe { $func(ctxt.ctxt, 2, terms.as_ptr()) };

        let kind = SmtKind::Bool;
        let ast = ctxt.postprocess(ast, &kind);
        SmtExpr { ast, ctxt, kind }
    }};
}

macro_rules! smt_binary_op_bitvec_to_bitvec {
    ($func:tt, $lhs:ident, $rhs:ident) => {{
        $lhs.check_binary_op_bitvec($rhs);

        let ctxt = $lhs.ctxt;
        let ast = unsafe { $func(ctxt.ctxt, $lhs.ast, $rhs.ast) };

        let kind = $lhs.kind.clone();
        let ast = ctxt.postprocess(ast, &kind);
        SmtExpr { ast, ctxt, kind }
    }};
}

macro_rules! smt_binary_op_bitvec_to_bitvec_sign_split {
    ($func_s:tt, $func_u:tt, $lhs:ident, $rhs:ident) => {{
        $lhs.check_binary_op_bitvec($rhs);

        let ctxt = $lhs.ctxt;
        let ast = if matches!($lhs.kind, SmtKind::Bitvec { signed, .. } if signed) {
            unsafe { $func_s(ctxt.ctxt, $lhs.ast, $rhs.ast) }
        } else {
            unsafe { $func_u(ctxt.ctxt, $lhs.ast, $rhs.ast) }
        };

        let kind = $lhs.kind.clone();
        let ast = ctxt.postprocess(ast, &kind);
        SmtExpr { ast, ctxt, kind }
    }};
}

macro_rules! smt_binary_op_bitvec_to_bool_sign_split {
    ($func_s:tt, $func_u:tt, $lhs:ident, $rhs:ident) => {{
        $lhs.check_binary_op_bitvec($rhs);

        let ctxt = $lhs.ctxt;
        let ast = if matches!($lhs.kind, SmtKind::Bitvec { signed, .. } if signed) {
            unsafe { $func_s(ctxt.ctxt, $lhs.ast, $rhs.ast) }
        } else {
            unsafe { $func_u(ctxt.ctxt, $lhs.ast, $rhs.ast) }
        };

        let kind = SmtKind::Bool;
        let ast = ctxt.postprocess(ast, &kind);
        SmtExpr { ast, ctxt, kind }
    }};
}

macro_rules! smt_binary_op_generic_to_bool {
    ($func:tt, $lhs:ident, $rhs:ident) => {{
        $lhs.check_binary_op($rhs);

        let ctxt = $lhs.ctxt;
        let ast = unsafe { $func(ctxt.ctxt, $lhs.ast, $rhs.ast) };

        let kind = SmtKind::Bool;
        let ast = ctxt.postprocess(ast, &kind);
        SmtExpr { ast, ctxt, kind }
    }};
}

macro_rules! smt_binary_op_generic_to_bool_by_term {
    ($func:tt, $lhs:ident, $rhs:ident) => {{
        $lhs.check_binary_op($rhs);

        let ctxt = $lhs.ctxt;
        let terms: [Z3_ast; 2] = [$lhs.ast, $rhs.ast];
        let ast = unsafe { $func(ctxt.ctxt, 2, terms.as_ptr()) };

        let kind = SmtKind::Bool;
        let ast = ctxt.postprocess(ast, &kind);
        SmtExpr { ast, ctxt, kind }
    }};
}

impl<'smt> SmtExpr<'smt> {
    // checking
    fn check_unary_op_bool(&self) {
        debug_assert!(matches!(self.kind, SmtKind::Bool));
    }

    fn check_unary_op_bitvec(&self) {
        debug_assert!(matches!(self.kind, SmtKind::Bitvec { .. }));
    }

    fn check_binary_op(&self, rhs: &Self) {
        debug_assert!(self.ctxt.smt_ctxt_matches(rhs.ctxt));
        debug_assert_eq!(self.kind, rhs.kind);
    }

    fn check_binary_op_bool(&self, rhs: &Self) {
        self.check_binary_op(rhs);
        debug_assert!(matches!(self.kind, SmtKind::Bool));
    }

    fn check_binary_op_bitvec(&self, rhs: &Self) {
        self.check_binary_op(rhs);
        debug_assert!(matches!(self.kind, SmtKind::Bitvec { .. }));
    }

    // bool logic operators
    pub fn not(&self) -> Self {
        smt_unary_op_bool!(Z3_mk_not, self)
    }

    pub fn and(&self, rhs: &Self) -> Self {
        smt_binary_op_bool!(Z3_mk_and, self, rhs)
    }

    pub fn or(&self, rhs: &Self) -> Self {
        smt_binary_op_bool!(Z3_mk_or, self, rhs)
    }

    // bitvec arith operators
    pub fn add(&self, rhs: &Self) -> Self {
        smt_binary_op_bitvec_to_bitvec!(Z3_mk_bvadd, self, rhs)
    }

    pub fn sub(&self, rhs: &Self) -> Self {
        smt_binary_op_bitvec_to_bitvec!(Z3_mk_bvsub, self, rhs)
    }

    pub fn mul(&self, rhs: &Self) -> Self {
        smt_binary_op_bitvec_to_bitvec!(Z3_mk_bvmul, self, rhs)
    }

    pub fn div(&self, rhs: &Self) -> Self {
        smt_binary_op_bitvec_to_bitvec_sign_split!(Z3_mk_bvsdiv, Z3_mk_bvudiv, self, rhs)
    }

    pub fn rem(&self, rhs: &Self) -> Self {
        smt_binary_op_bitvec_to_bitvec_sign_split!(Z3_mk_bvsmod, Z3_mk_bvurem, self, rhs)
    }

    // bitvec casting operators
    fn cast(&self, into_signed: bool, into_width: u16) -> Self {
        self.check_unary_op_bitvec();

        let ctxt = self.ctxt;
        let ast = match self.kind {
            SmtKind::Bitvec { width, .. } => match width.cmp(&into_width) {
                Ordering::Greater => unsafe {
                    Z3_mk_extract(ctxt.ctxt, (into_width - 1) as c_uint, 0, self.ast)
                },
                Ordering::Less => {
                    if into_signed {
                        unsafe {
                            Z3_mk_sign_ext(ctxt.ctxt, (into_width - width) as c_uint, self.ast)
                        }
                    } else {
                        unsafe {
                            Z3_mk_zero_ext(ctxt.ctxt, (into_width - width) as c_uint, self.ast)
                        }
                    }
                }
                Ordering::Equal => self.ast,
            },
            _ => panic!("Cast is only applicable to bitvec"),
        };

        let kind = SmtKind::Bitvec {
            signed: into_signed,
            width: into_width,
        };
        let ast = ctxt.postprocess(ast, &kind);
        SmtExpr { ast, ctxt, kind }
    }

    pub fn cast_u8(&self) -> Self {
        self.cast(false, 8)
    }

    pub fn cast_u64(&self) -> Self {
        self.cast(false, 64)
    }

    pub fn cast_u128(&self) -> Self {
        self.cast(false, 128)
    }

    // bitvec bitwise operators
    pub fn bit_and(&self, rhs: &Self) -> Self {
        smt_binary_op_bitvec_to_bitvec!(Z3_mk_bvand, self, rhs)
    }

    pub fn bit_or(&self, rhs: &Self) -> Self {
        smt_binary_op_bitvec_to_bitvec!(Z3_mk_bvor, self, rhs)
    }

    pub fn bit_xor(&self, rhs: &Self) -> Self {
        smt_binary_op_bitvec_to_bitvec!(Z3_mk_bvxor, self, rhs)
    }

    pub fn shl(&self, rhs: &Self) -> Self {
        smt_binary_op_bitvec_to_bitvec!(Z3_mk_bvshl, self, rhs)
    }

    pub fn shr(&self, rhs: &Self) -> Self {
        smt_binary_op_bitvec_to_bitvec_sign_split!(Z3_mk_bvashr, Z3_mk_bvlshr, self, rhs)
    }

    // bitvec comparison operators
    pub fn gt(&self, rhs: &Self) -> Self {
        smt_binary_op_bitvec_to_bool_sign_split!(Z3_mk_bvsgt, Z3_mk_bvugt, self, rhs)
    }

    pub fn ge(&self, rhs: &Self) -> Self {
        smt_binary_op_bitvec_to_bool_sign_split!(Z3_mk_bvsge, Z3_mk_bvuge, self, rhs)
    }

    pub fn le(&self, rhs: &Self) -> Self {
        smt_binary_op_bitvec_to_bool_sign_split!(Z3_mk_bvsle, Z3_mk_bvule, self, rhs)
    }

    pub fn lt(&self, rhs: &Self) -> Self {
        smt_binary_op_bitvec_to_bool_sign_split!(Z3_mk_bvslt, Z3_mk_bvult, self, rhs)
    }

    // equality operator (for both bool and bitvec)
    pub fn eq(&self, rhs: &Self) -> Self {
        smt_binary_op_generic_to_bool!(Z3_mk_eq, self, rhs)
    }

    pub fn ne(&self, rhs: &Self) -> Self {
        smt_binary_op_generic_to_bool_by_term!(Z3_mk_distinct, self, rhs)
    }

    // struct operations
    pub fn unpack(&self) -> Vec<Self> {
        let ctxt = self.ctxt;

        // get struct info
        let struct_info = if let SmtKind::Struct { struct_name } = &self.kind {
            ctxt.struct_map.get(struct_name).unwrap()
        } else {
            panic!("Only structs can be unpacked");
        };

        // prepare arguments
        let struct_ast: [Z3_ast; 1] = [self.ast];
        let asts: Vec<Z3_ast> = struct_info
            .field_getters
            .iter()
            .map(|getter| unsafe { Z3_mk_app(ctxt.ctxt, *getter, 1, struct_ast.as_ptr()) })
            .collect();

        // post-processing
        let asts: Vec<Z3_ast> = asts
            .into_iter()
            .enumerate()
            .map(|(i, ast)| ctxt.postprocess(ast, struct_info.field_kinds.get(i).unwrap()))
            .collect();

        // done
        asts.into_iter()
            .enumerate()
            .map(|(i, ast)| SmtExpr {
                ast,
                ctxt,
                kind: struct_info.field_kinds.get(i).unwrap().clone(),
            })
            .collect()
    }
}

// unit testing for the smtlib
#[cfg(test)]
mod tests {
    use super::*;

    fn make_ctxt(conf_auto_simplify: bool) -> SmtCtxt {
        let mut ctxt = SmtCtxt::new(conf_auto_simplify);

        // populate with two struct types
        ctxt.create_smt_struct(
            String::from("dummy"),
            vec![
                (String::from("val_u64"), SmtKind::bitvec_u64()),
                (
                    String::from("val_vec_u8"),
                    SmtKind::Vector {
                        element_kind: Box::new(SmtKind::bitvec_u8()),
                    },
                ),
            ],
        );
        let struct_kind_dummy = SmtKind::Struct {
            struct_name: String::from("dummy"),
        };

        ctxt.create_smt_struct(
            String::from("nested"),
            vec![
                (String::from("val_dummy"), struct_kind_dummy.clone()),
                (
                    String::from("val_vec_dummy"),
                    SmtKind::Vector {
                        element_kind: Box::new(struct_kind_dummy),
                    },
                ),
            ],
        );

        // done
        ctxt
    }

    fn ctxt_variants() -> Vec<SmtCtxt> {
        vec![make_ctxt(true), make_ctxt(false)]
    }

    macro_rules! prove {
        ($ctxt:ident, $pat_true:pat, $pat_false:pat, $pred:expr) => {
            assert!(matches!(
                $ctxt.solve(&[$pred]),
                $pat_true
            ));
            assert!(matches!(
                $ctxt.solve(&[&$pred.not()]),
                $pat_false
            ));
        };
        ($ctxt: ident, $pat_true:pat, $pat_false:pat, $pred:expr, $( $cond:expr ),+) => {
            assert!(matches!(
                $ctxt.solve(&[$pred, $( $cond ),+]),
                $pat_true
            ));
            assert!(matches!(
                $ctxt.solve(&[
                    &[$( $cond ),+]
                        .iter()
                        .fold($pred.clone(), |acc, cur| {acc.and(cur)})
                        .not()
                ]),
                $pat_false
            ));
        };
    }

    macro_rules! prove_true {
        ($ctxt:ident, $pred:expr) => {
            prove!($ctxt, SmtResult::SAT, SmtResult::UNSAT, $pred)
        };
        ($ctxt: ident, $pred:expr, $( $cond:expr ),+) => {
            prove!($ctxt, SmtResult::SAT, SmtResult::UNSAT, $pred, $( $cond ),+)
        };
    }

    macro_rules! prove_false {
        ($ctxt:ident, $pred:expr) => {
            prove!($ctxt, SmtResult::UNSAT, SmtResult::SAT, $pred)
        };
        ($ctxt: ident, $pred:expr, $( $cond:expr ),+) => {
            prove!($ctxt, SmtResult::UNSAT, SmtResult::SAT, $pred, $( $cond ),+)
        };
    }

    macro_rules! prove_maybe {
        ($ctxt:ident, $pred:expr) => {
            prove!($ctxt, SmtResult::SAT, SmtResult::SAT, $pred)
        };
        ($ctxt: ident, $pred:expr, $( $cond:expr ),+) => {
            prove!($ctxt, SmtResult::SAT, SmtResult::SAT, $pred, $( $cond ),+)
        };
    }

    macro_rules! prove_eq {
        ($ctxt:ident, $lhs:expr, $rhs:expr) => {
            prove_true!($ctxt, &$lhs.eq($rhs));
        };
    }

    macro_rules! prove_ne {
        ($ctxt:ident, $lhs:expr, $rhs:expr) => {
            prove_true!($ctxt, &$lhs.ne($rhs));
        };
    }

    macro_rules! prove_qn {
        ($ctxt:ident, $lhs:expr, $rhs:expr) => {
            prove_maybe!($ctxt, &$lhs.eq($rhs));
            prove_maybe!($ctxt, &$lhs.ne($rhs));
        };
    }

    #[test]
    fn test_bool() {
        for ctxt in ctxt_variants().iter() {
            // a true constant
            let expr_t = ctxt.bool_const(true);
            prove_true!(ctxt, &expr_t);

            // a false constant
            let expr_f = ctxt.bool_const(false);
            prove_false!(ctxt, &expr_f);

            // a variable
            let expr_x = ctxt.bool_var("x");
            prove_maybe!(ctxt, &expr_x);

            // NOT
            prove_false!(ctxt, &expr_t.not());
            prove_true!(ctxt, &expr_f.not());
            prove_maybe!(ctxt, &expr_x.not());

            // AND
            prove_true!(ctxt, &expr_t.and(&expr_t));
            prove_false!(ctxt, &expr_t.and(&expr_f));
            prove_false!(ctxt, &expr_f.and(&expr_t));
            prove_false!(ctxt, &expr_f.and(&expr_f));
            prove_maybe!(ctxt, &expr_t.and(&expr_x));
            prove_false!(ctxt, &expr_f.and(&expr_x));

            // OR
            prove_true!(ctxt, &expr_t.or(&expr_t));
            prove_true!(ctxt, &expr_t.or(&expr_f));
            prove_true!(ctxt, &expr_f.or(&expr_t));
            prove_false!(ctxt, &expr_f.or(&expr_f));
            prove_true!(ctxt, &expr_t.or(&expr_x));
            prove_maybe!(ctxt, &expr_f.or(&expr_x));
        }
    }

    #[test]
    fn test_bitvec() {
        // since Move has unsigned integers only, we focus on the
        // test of unsigned integer as well
        for ctxt in ctxt_variants().iter() {
            // constants
            let expr_u8_0 = ctxt.bitvec_const_u8(0);
            let expr_u8_1 = ctxt.bitvec_const_u8(1);
            let expr_u8_255 = ctxt.bitvec_const_u8(255);

            // variable
            let expr_u8_x = ctxt.bitvec_var_u8("x");
            prove_qn!(ctxt, &expr_u8_x, &expr_u8_0);

            // ADD
            prove_eq!(ctxt, &expr_u8_0.add(&expr_u8_0), &expr_u8_0);
            prove_eq!(ctxt, &expr_u8_0.add(&expr_u8_1), &expr_u8_1);
            prove_eq!(ctxt, &expr_u8_0.add(&expr_u8_x), &expr_u8_x);
            prove_ne!(ctxt, &expr_u8_1.add(&expr_u8_x), &expr_u8_x); // may overflow
            prove_ne!(ctxt, &expr_u8_255.add(&expr_u8_x), &expr_u8_x); // may overflow

            // SUB
            prove_eq!(ctxt, &expr_u8_0.sub(&expr_u8_0), &expr_u8_0);
            prove_eq!(ctxt, &expr_u8_0.sub(&expr_u8_1), &expr_u8_255);
            prove_qn!(ctxt, &expr_u8_0.sub(&expr_u8_x), &expr_u8_x);
            prove_ne!(ctxt, &expr_u8_1.sub(&expr_u8_x), &expr_u8_x); // may overflow
            prove_ne!(ctxt, &expr_u8_255.add(&expr_u8_x), &expr_u8_x); // may overflow

            // MUL
            prove_eq!(ctxt, &expr_u8_0.mul(&expr_u8_0), &expr_u8_0);
            prove_eq!(ctxt, &expr_u8_0.mul(&expr_u8_1), &expr_u8_0);
            prove_eq!(ctxt, &expr_u8_0.mul(&expr_u8_x), &expr_u8_0);
            prove_eq!(ctxt, &expr_u8_1.mul(&expr_u8_x), &expr_u8_x); // may overflow
            prove_qn!(ctxt, &expr_u8_255.mul(&expr_u8_x), &expr_u8_x); // may overflow

            // DIV
            prove_ne!(ctxt, &expr_u8_0.div(&expr_u8_0), &expr_u8_0); // div by zero
            prove_eq!(ctxt, &expr_u8_0.div(&expr_u8_1), &expr_u8_0);
            prove_qn!(ctxt, &expr_u8_0.div(&expr_u8_x), &expr_u8_0); // may div by zero
            prove_qn!(ctxt, &expr_u8_1.div(&expr_u8_x), &expr_u8_x); // may div by zero
            prove_ne!(ctxt, &expr_u8_255.div(&expr_u8_x), &expr_u8_x); // may div by zero

            // MOD
            prove_eq!(ctxt, &expr_u8_0.rem(&expr_u8_0), &expr_u8_0); // div by zero
            prove_eq!(ctxt, &expr_u8_0.rem(&expr_u8_1), &expr_u8_0);
            prove_eq!(ctxt, &expr_u8_0.rem(&expr_u8_x), &expr_u8_0); // may div by zero
            prove_ne!(ctxt, &expr_u8_1.rem(&expr_u8_x), &expr_u8_x); // may div by zero
            prove_ne!(ctxt, &expr_u8_255.rem(&expr_u8_x), &expr_u8_x); // may div by zero

            // BIT_AND
            prove_eq!(ctxt, &expr_u8_0.bit_and(&expr_u8_0), &expr_u8_0);
            prove_eq!(ctxt, &expr_u8_0.bit_and(&expr_u8_1), &expr_u8_0);
            prove_eq!(ctxt, &expr_u8_0.bit_and(&expr_u8_x), &expr_u8_0);
            prove_qn!(ctxt, &expr_u8_1.bit_and(&expr_u8_x), &expr_u8_x);
            prove_eq!(ctxt, &expr_u8_255.bit_and(&expr_u8_x), &expr_u8_x);

            // BIT_OR
            prove_eq!(ctxt, &expr_u8_0.bit_or(&expr_u8_0), &expr_u8_0);
            prove_eq!(ctxt, &expr_u8_0.bit_or(&expr_u8_1), &expr_u8_1);
            prove_eq!(ctxt, &expr_u8_0.bit_or(&expr_u8_x), &expr_u8_x);
            prove_qn!(ctxt, &expr_u8_1.bit_or(&expr_u8_x), &expr_u8_x);
            prove_eq!(ctxt, &expr_u8_255.bit_or(&expr_u8_x), &expr_u8_255);

            // BIT_XOR
            prove_eq!(ctxt, &expr_u8_0.bit_or(&expr_u8_0), &expr_u8_0);
            prove_eq!(ctxt, &expr_u8_0.bit_or(&expr_u8_1), &expr_u8_1);
            prove_eq!(ctxt, &expr_u8_0.bit_or(&expr_u8_x), &expr_u8_x);
            prove_qn!(ctxt, &expr_u8_1.bit_or(&expr_u8_x), &expr_u8_x);
            prove_qn!(ctxt, &expr_u8_255.bit_or(&expr_u8_x), &expr_u8_x);

            // SHL
            prove_eq!(ctxt, &expr_u8_0.shl(&expr_u8_0), &expr_u8_0);
            prove_eq!(ctxt, &expr_u8_0.shl(&expr_u8_1), &expr_u8_0);
            prove_qn!(ctxt, &expr_u8_0.shl(&expr_u8_x), &expr_u8_x);
            prove_ne!(ctxt, &expr_u8_1.shl(&expr_u8_x), &expr_u8_x);
            prove_ne!(ctxt, &expr_u8_255.shl(&expr_u8_x), &expr_u8_x);

            // SHR
            prove_eq!(ctxt, &expr_u8_0.shr(&expr_u8_0), &expr_u8_0);
            prove_eq!(ctxt, &expr_u8_0.shr(&expr_u8_1), &expr_u8_0);
            prove_eq!(ctxt, &expr_u8_0.shr(&expr_u8_x), &expr_u8_0);
            prove_ne!(ctxt, &expr_u8_1.shr(&expr_u8_x), &expr_u8_x);
            prove_ne!(ctxt, &expr_u8_255.shr(&expr_u8_x), &expr_u8_x);

            // GT
            prove_false!(ctxt, &expr_u8_0.gt(&expr_u8_0));
            prove_false!(ctxt, &expr_u8_0.gt(&expr_u8_1));
            prove_false!(ctxt, &expr_u8_0.gt(&expr_u8_x));
            prove_maybe!(ctxt, &expr_u8_1.gt(&expr_u8_x));
            prove_maybe!(ctxt, &expr_u8_255.gt(&expr_u8_x));

            // GE
            prove_true!(ctxt, &expr_u8_0.ge(&expr_u8_0));
            prove_false!(ctxt, &expr_u8_0.ge(&expr_u8_1));
            prove_maybe!(ctxt, &expr_u8_0.ge(&expr_u8_x));
            prove_maybe!(ctxt, &expr_u8_1.ge(&expr_u8_x));
            prove_true!(ctxt, &expr_u8_255.ge(&expr_u8_x));

            // LE
            prove_true!(ctxt, &expr_u8_0.le(&expr_u8_0));
            prove_true!(ctxt, &expr_u8_0.le(&expr_u8_1));
            prove_true!(ctxt, &expr_u8_0.le(&expr_u8_x));
            prove_maybe!(ctxt, &expr_u8_1.le(&expr_u8_x));
            prove_maybe!(ctxt, &expr_u8_255.le(&expr_u8_x));

            // LT
            prove_false!(ctxt, &expr_u8_0.lt(&expr_u8_0));
            prove_true!(ctxt, &expr_u8_0.lt(&expr_u8_1));
            prove_maybe!(ctxt, &expr_u8_0.lt(&expr_u8_x));
            prove_maybe!(ctxt, &expr_u8_1.lt(&expr_u8_x));
            prove_false!(ctxt, &expr_u8_255.lt(&expr_u8_x));

            // CAST
            prove_eq!(ctxt, &expr_u8_x.cast_u8(), &expr_u8_x);
            prove_eq!(ctxt, &expr_u8_x.cast_u64().cast_u8(), &expr_u8_x);
            prove_eq!(ctxt, &expr_u8_x.cast_u128().cast_u8(), &expr_u8_x);
        }
    }

    #[test]
    fn test_vector() {
        for ctxt in ctxt_variants().iter() {
            // constants
            let expr_u8_0 = ctxt.bitvec_const_u8(0);
            let expr_u8_1 = ctxt.bitvec_const_u8(1);
            let expr_vec_u8_00_01 =
                ctxt.vector_const(&SmtKind::bitvec_u8(), &[&expr_u8_0, &expr_u8_1]);
            prove_eq!(ctxt, &expr_vec_u8_00_01, &expr_vec_u8_00_01);

            // variable
            let expr_vec_u8_x = ctxt.vector_var(&SmtKind::bitvec_u8(), "x");
            prove_eq!(ctxt, &expr_vec_u8_x, &expr_vec_u8_x);

            // EQ || NE
            prove_qn!(ctxt, &expr_vec_u8_00_01, &expr_vec_u8_x);
        }
    }

    #[test]
    fn test_struct() {
        for ctxt in ctxt_variants().iter() {
            // dummy struct type
            let struct_kind_dummy = SmtKind::Struct {
                struct_name: String::from("dummy"),
            };

            // constants
            let expr_u64_x = ctxt.bitvec_var_u64("x");

            let expr_u8_y1 = ctxt.bitvec_var_u8("y1");
            let expr_u8_y2 = ctxt.bitvec_var_u8("y2");
            let expr_vec_u8_y1_y2 =
                ctxt.vector_const(&SmtKind::bitvec_u8(), &[&expr_u8_y1, &expr_u8_y2]);

            // pack
            let expr_struct_dummy_x_y1y2 =
                ctxt.struct_const(&struct_kind_dummy, &[&expr_u64_x, &expr_vec_u8_y1_y2]);
            prove_eq!(ctxt, &expr_struct_dummy_x_y1y2, &expr_struct_dummy_x_y1y2);

            // unpack
            let expr_struct_dummy_fields = expr_struct_dummy_x_y1y2.unpack();
            debug_assert_eq!(expr_struct_dummy_fields.len(), 2);

            // check
            prove_eq!(ctxt, expr_struct_dummy_fields.get(0).unwrap(), &expr_u64_x);
            prove_eq!(
                ctxt,
                expr_struct_dummy_fields.get(1).unwrap(),
                &expr_vec_u8_y1_y2
            );

            // variable
            let expr_struct_dummy_z = ctxt.struct_var(&struct_kind_dummy, "z");

            // EQ || NE
            prove_qn!(ctxt, &expr_struct_dummy_x_y1y2, &expr_struct_dummy_z);
        }
    }
}
