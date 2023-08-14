//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::analysis;
use crate::analysis::{ControlFlowGraph, DominatorTree};
use crate::ir::*;
use crate::pass::*;
use crate::utility::SaHashSet;
use std::cmp::Ordering;
use std::iter;

/// An IR validity verification pass.
///
/// This scans the entire module, and will do nothing if the module is valid. If
/// the module isn't valid, it will abort with an error.
pub struct VerifyModulePass;

impl ModuleTransformPass for VerifyModulePass {
    fn run(&mut self, module: &mut Module, _: &mut ModuleAnalysisManager) -> PreservedAnalyses {
        verify_module_panic(module);

        PreservedAnalyses::all()
    }
}

/// Verifies that an entire module is valid SIR.
///
/// This checks that the SSA properties are upheld (dominance mainly), that
/// every block has a terminator, that every call is to a valid function, etc.
///
/// If it isn't, this function returns a list of errors and the associated debug-info
/// of the IR that caused it.
///
/// # Note
/// Since this function returns the [`DebugInfo`] associated with the erroneous IR, it
/// may be a good idea to turn the IR into a textual file first and then parse/verify it.
pub fn verify_module(module: &Module) -> Result<(), Vec<(String, DebugInfo)>> {
    let mut verifier = Verifier {
        module,
        errors: Vec::default(),
        domtree: None,
        prev_defined: SaHashSet::default(),
        return_ty: None,
    };

    verifier.walk();

    if verifier.errors.is_empty() {
        Ok(())
    } else {
        Err(verifier.errors)
    }
}

/// This is [`verify_module`], except that it writes out any errors
/// and then panics on failure.
pub fn verify_module_panic(module: &Module) {
    if let Err(e) = verify_module(module) {
        println!();
        analysis::print_module(module);
        println!();

        for (error, spot) in e {
            let (line, col) = (spot.line(), spot.col());

            println!("{line}:{col}: {error}");
        }

        panic!();
    }
}

macro_rules! verify_assert {
    ($self:expr, $info:expr, $cond:expr, $explanation:expr) => {
        if !($cond) {
            $self.errors.push((($explanation).to_string(), $info));
        }
    };
}

macro_rules! verify_assert_eq {
    ($self:expr, $info:expr, $lhs:expr, $rhs:expr, $explanation:expr) => {
        verify_assert!($self, $info, $lhs == $rhs, $explanation)
    };
}

macro_rules! verify_assert_ne {
    ($self:expr, $info:expr, $lhs:expr, $rhs:expr, $explanation:expr) => {
        verify_assert!($self, $info, $lhs != $rhs, $explanation)
    };
}

macro_rules! verify_integral_binop {
    ($self:expr, $inst:expr, $name:literal, $data:expr, $def:expr) => {{
        let (lhs, rhs) = ($def.dfg.ty($data.lhs()), $def.dfg.ty($data.rhs()));

        verify_assert!(
            $self,
            $def.dfg.inst_debug($inst),
            lhs.is_int(),
            concat!("`", $name, "` operands must be of int type")
        );

        verify_assert!(
            $self,
            $def.dfg.inst_debug($inst),
            rhs.is_int(),
            concat!("`", $name, "` operands must be of int type")
        );

        verify_assert_eq!(
            $self,
            $def.dfg.inst_debug($inst),
            lhs,
            rhs,
            concat!("`", $name, "` operands must be the same type")
        );
    }};
}

macro_rules! verify_float_binop {
    ($self:expr, $inst:expr, $name:literal, $data:expr, $def:expr) => {{
        let (lhs, rhs) = ($def.dfg.ty($data.lhs()), $def.dfg.ty($data.rhs()));

        verify_assert!(
            $self,
            $def.dfg.inst_debug($inst),
            lhs.is_float(),
            concat!("`", $name, "` operands must be of float type")
        );

        verify_assert!(
            $self,
            $def.dfg.inst_debug($inst),
            rhs.is_float(),
            concat!("`", $name, "` operands must be of float type")
        );

        verify_assert_eq!(
            $self,
            $def.dfg.inst_debug($inst),
            lhs,
            rhs,
            concat!("`", $name, "` operands must be the same type")
        );
    }};
}

macro_rules! verify_cast {
    ($self:expr, $inst:expr, $name:literal, $data:expr, $def:expr, $into:ident, $from:ident) => {{
        let input_ty = $def.dfg.ty($data.operand());
        let output_ty = $data.result_ty().unwrap();

        verify_assert!(
            $self,
            $def.dfg.inst_debug($inst),
            input_ty.$from(),
            concat!("`", $name, "` operands must be of correct type")
        );
        verify_assert!(
            $self,
            $def.dfg.inst_debug($inst),
            output_ty.$into(),
            concat!("`", $name, "` output type is wrong")
        );
    }};
}

struct Verifier<'m> {
    module: &'m Module,
    domtree: Option<DominatorTree>,
    prev_defined: SaHashSet<Inst>,
    return_ty: Option<Type>,
    errors: Vec<(String, DebugInfo)>,
}

impl<'m> Verifier<'m> {
    fn verify_call_params(
        &mut self,
        debug: DebugInfo,
        sig: &Signature,
        params: impl Iterator<Item = Type> + ExactSizeIterator,
        mut args: impl Iterator<Item = Type> + ExactSizeIterator,
    ) {
        let param_len = params.len();
        let args_len = args.len();

        if sig.vararg() {
            for (i, ty) in params.enumerate() {
                let next = match args.next() {
                    Some(next) => next,
                    None => {
                        verify_assert!(
                            self,
                            debug,
                            false,
                            format!("expected {param_len} arguments but got {args_len}")
                        );

                        break;
                    }
                };

                // while parsing args for function with signature 'i32 (ptr)', unexpected parameter 'i32 %1'
                verify_assert_eq!(
                    self,
                    debug,
                    ty,
                    next,
                    "arguments must match the type of the parameter in a function call"
                );
            }

            // we can have more arguments, its fine. this is the variadic case
        } else {
            verify_assert!(
                self,
                debug,
                params.eq(args),
                "arguments passed must match function parameter's types"
            );
        }
    }

    fn verify_branch_target(
        &mut self,
        inst: Inst,
        target: &BlockWithParams,
        def: &FunctionDefinition,
    ) {
        verify_assert!(
            self,
            def.dfg.inst_debug(inst),
            def.dfg.is_block_inserted(target.block()),
            "can't branch to non-existent block"
        );
        verify_assert!(
            self,
            def.dfg.inst_debug(inst),
            def.layout.is_block_inserted(target.block()),
            "can't branch to block outside of layout"
        );

        let args = target.args();
        let target = def.dfg.block(target.block());
        let params = target.params();

        verify_assert_eq!(
            self,
            def.dfg.inst_debug(inst),
            args.len(),
            params.len(),
            "branch target has wrong number of block arguments"
        );

        for (arg, param) in args.iter().zip(params) {
            verify_assert_eq!(
                self,
                def.dfg.inst_debug(inst),
                def.dfg.ty(*arg),
                def.dfg.ty(*param),
                "`br` arg and parameter must have the same type"
            );
        }
    }
}

impl<'m> SIRVisitor<'m> for Verifier<'m> {
    fn module(&self) -> &'m Module {
        self.module
    }

    fn visit_func(&mut self, func: Func) {
        let function = self.module().function(func);

        self.return_ty = function.signature().return_ty();
        self.prev_defined.clear();

        if let Some((ty, attributes)) = function.signature().return_complete() {
            if attributes != RetAttributes::NONE {
                verify_assert!(
                    self,
                    DebugInfo::fake(),
                    ty.is_ptr(),
                    format!(
                        "function '{}' can only have return attributes on `ptr` return values",
                        function.name()
                    )
                );
            }
        }

        if let Some(def) = function.definition() {
            if let Some(bb) = def.layout.entry_block() {
                let sig = function.signature();
                let bb_params = def.dfg.block(bb).params();
                let sig_params = sig.params();

                verify_assert_eq!(
                    self,
                    DebugInfo::fake(),
                    bb_params.len(),
                    sig_params.len(),
                    format!("entry block for function '{}' must have same number of parameters as function signature", function.name())
                );

                for (&bb_param, &(sig_param, attributes)) in
                    iter::zip(bb_params.iter(), sig_params.iter())
                {
                    if attributes != ParamAttributes::NONE {
                        verify_assert!(
                            self,
                            DebugInfo::fake(),
                            sig_param.is_ptr(),
                            format!("function '{}' can only have parameter attributes on `ptr` parameters", function.name())
                        );
                    }

                    verify_assert_eq!(
                        self,
                        def.dfg.debug(bb_param),
                        def.dfg.ty(bb_param),
                        sig_param,
                        "entry block parameter does not match in type to function signature"
                    );
                }

                let cfg = ControlFlowGraph::compute(function);
                let domtree = DominatorTree::compute(function, &cfg);

                self.domtree.replace(domtree);

                verify_assert_eq!(
                    self,
                    DebugInfo::fake(),
                    cfg.n_predecessors(bb),
                    0,
                    format!(
                        "entry block for function '{}' must not have any predecessors",
                        function.name()
                    )
                );

                let reachable: Vec<Block> =
                    self.domtree.as_ref().unwrap().reverse_postorder().collect();

                for block in reachable {
                    self.visit_block(block, def);
                }
            }
        }
    }

    fn visit_block(&mut self, block: Block, def: &FunctionDefinition) {
        if let Some(inst) = def.layout.block_last_inst(block) {
            let targets = def.dfg.branch_info(inst);

            verify_assert!(
                self,
                def.dfg.inst_debug(inst),
                matches!(targets, Some(_)),
                "last instruction in reachable block should be a terminator"
            );

            self.dispatch_insts(block, def);
        }
    }

    fn visit_inst(&mut self, inst: Inst, def: &FunctionDefinition) {
        let bb = def.layout.inst_block(inst);

        // the same instruction shouldn't ever be seen twice, it should only
        // exist exactly once in a given layout
        verify_assert!(
            self,
            def.dfg.inst_debug(inst),
            self.prev_defined.insert(inst),
            "cannot have the same `Inst` object twice in a given layout"
        );

        for operand in def.dfg.inst_data(inst).operands() {
            let value_def = def.dfg.value_def(*operand);
            let defined_in = match value_def {
                ValueDef::Inst(i) => {
                    verify_assert_ne!(
                        self,
                        def.dfg.inst_debug(inst),
                        i,
                        inst,
                        "instruction cannot use itself as operand"
                    );

                    if !def.layout.is_inst_inserted(i) {
                        verify_assert!(
                            self,
                            def.dfg.inst_debug(inst),
                            def.layout.is_inst_inserted(i),
                            "instruction cannot use result of non-inserted instruction"
                        );
                        return;
                    }

                    def.layout.inst_block(i)
                }
                ValueDef::Param(bb, _) => bb,
            };

            // definition block has to dominate the use block, this could be the same block.
            verify_assert!(
                self,
                def.dfg.inst_debug(inst),
                self.domtree.as_ref().unwrap().dominates(bb, defined_in),
                "definition's block must dominate use's block"
            );

            // if it is the same block, we need to make sure that the operand
            // is actually defined **before** the use in layout order.
            if bb == defined_in {
                match value_def {
                    ValueDef::Inst(i) => {
                        verify_assert_eq!(
                            self,
                            def.dfg.inst_debug(inst),
                            def.layout.loc_compare(i, inst),
                            Ordering::Less,
                            "definition must be before uses in the same basic block"
                        )
                    }
                    ValueDef::Param(_, _) => {
                        // nothing to do here, block params all exist before the block starts
                    }
                }
            }
        }

        self.dispatch_inst(inst, def.dfg.inst_data(inst), def);
    }

    fn visit_call(&mut self, inst: Inst, data: &CallInst, def: &FunctionDefinition) {
        let function = self.module().function(data.callee());
        let sig = function.signature();
        let dbg = def.dfg.inst_debug(inst);

        verify_assert_eq!(
            self,
            dbg,
            sig,
            def.dfg.signature(data.sig()),
            "in `call`, signature of callee function must match signature given to inst"
        );

        // arguments given to function must map
        let func_params_it = sig.params().iter().map(|(ty, _)| *ty);
        let args_it = data.args().iter().map(|val| def.dfg.ty(*val));

        self.verify_call_params(def.dfg.inst_debug(inst), sig, func_params_it, args_it);

        match def.dfg.inst_to_result(inst) {
            Some(_) => {
                verify_assert_ne!(
                    self,
                    dbg,
                    sig.return_ty(),
                    None,
                    "`call` cannot call void and have a result"
                );
            }
            None => {
                verify_assert_eq!(
                    self,
                    dbg,
                    sig.return_ty(),
                    None,
                    "`call` cannot return value and not have a result"
                );
            }
        }
    }

    fn visit_indirectcall(
        &mut self,
        inst: Inst,
        data: &IndirectCallInst,
        def: &FunctionDefinition,
    ) {
        let sig = def.dfg.signature(data.sig());
        let dbg = def.dfg.inst_debug(inst);

        verify_assert_eq!(
            self,
            dbg,
            def.dfg.ty(data.callee()),
            Type::ptr(),
            "can only call `ptr` values with `indirectcall`"
        );

        // arguments given to function must map
        let func_params_it = sig.params().iter().map(|(ty, _)| *ty);
        let args_it = data.args().iter().map(|val| def.dfg.ty(*val));

        self.verify_call_params(def.dfg.inst_debug(inst), sig, func_params_it, args_it);

        match def.dfg.inst_to_result(inst) {
            Some(_) => {
                verify_assert_ne!(
                    self,
                    dbg,
                    sig.return_ty(),
                    None,
                    "`indirectcall` cannot call void and have a result"
                );
            }
            None => {
                verify_assert_eq!(
                    self,
                    dbg,
                    sig.return_ty(),
                    None,
                    "`indirectcall` cannot return value and not have a result"
                );
            }
        }
    }

    fn visit_icmp(&mut self, inst: Inst, data: &ICmpInst, def: &FunctionDefinition) {
        let (lhs, rhs) = (def.dfg.ty(data.lhs()), def.dfg.ty(data.rhs()));

        verify_assert!(
            self,
            def.dfg.inst_debug(inst),
            lhs.is_bool_or_int() || lhs.is_ptr(),
            "can only `icmp` on integral types and pointers"
        );
        verify_assert!(
            self,
            def.dfg.inst_debug(inst),
            rhs.is_bool_or_int() || rhs.is_ptr(),
            "can only `icmp` on integral types and pointers"
        );
        verify_assert_eq!(
            self,
            def.dfg.inst_debug(inst),
            lhs,
            rhs,
            "can only `icmp` on integral types and pointers"
        );
    }

    fn visit_fcmp(&mut self, inst: Inst, data: &FCmpInst, def: &FunctionDefinition) {
        let (lhs, rhs) = (def.dfg.ty(data.lhs()), def.dfg.ty(data.rhs()));

        verify_assert!(
            self,
            def.dfg.inst_debug(inst),
            lhs.is_float(),
            "can only `fcmp` on integral types"
        );
        verify_assert!(
            self,
            def.dfg.inst_debug(inst),
            rhs.is_float(),
            "can only `fcmp` on integral types"
        );
        verify_assert_eq!(
            self,
            def.dfg.inst_debug(inst),
            lhs,
            rhs,
            "operands to `fcmp` must be the same type"
        );
    }

    fn visit_sel(&mut self, inst: Inst, data: &SelInst, def: &FunctionDefinition) {
        let (cond, lhs, rhs) = (
            def.dfg.ty(data.condition()),
            def.dfg.ty(data.if_true()),
            def.dfg.ty(data.if_false()),
        );

        verify_assert!(
            self,
            def.dfg.inst_debug(inst),
            cond.is_bool(),
            "can only use `bool` as condition for `sel` "
        );
        verify_assert_eq!(
            self,
            def.dfg.inst_debug(inst),
            lhs,
            rhs,
            "operands to `sel` must be the same type"
        );
    }

    fn visit_br(&mut self, inst: Inst, data: &BrInst, def: &FunctionDefinition) {
        self.verify_branch_target(inst, data.target(), def);
    }

    fn visit_condbr(&mut self, inst: Inst, data: &CondBrInst, def: &FunctionDefinition) {
        self.verify_branch_target(inst, data.true_branch(), def);
        self.verify_branch_target(inst, data.false_branch(), def);
    }

    fn visit_unreachable(&mut self, _: Inst, _: &UnreachableInst, _: &FunctionDefinition) {}

    fn visit_ret(&mut self, inst: Inst, data: &RetInst, def: &FunctionDefinition) {
        verify_assert_eq!(
            self,
            def.dfg.inst_debug(inst),
            self.return_ty,
            data.value().map(|val| def.dfg.ty(val)),
            "`ret` must return the correct type"
        );
    }

    fn visit_and(&mut self, inst: Inst, data: &CommutativeArithInst, def: &FunctionDefinition) {
        let (lhs, rhs) = (def.dfg.ty(data.lhs()), def.dfg.ty(data.rhs()));

        verify_assert!(
            self,
            def.dfg.inst_debug(inst),
            lhs.is_bool_or_int(),
            "`and` operands must be of int/bool type"
        );
        verify_assert!(
            self,
            def.dfg.inst_debug(inst),
            rhs.is_bool_or_int(),
            "`and` operands must be of int/bool type"
        );
        verify_assert_eq!(
            self,
            def.dfg.inst_debug(inst),
            lhs,
            rhs,
            "`and` operands must be the same type"
        );
    }

    fn visit_or(&mut self, inst: Inst, data: &CommutativeArithInst, def: &FunctionDefinition) {
        let (lhs, rhs) = (def.dfg.ty(data.lhs()), def.dfg.ty(data.rhs()));

        verify_assert!(
            self,
            def.dfg.inst_debug(inst),
            lhs.is_bool_or_int(),
            "`or` operands must be of int/bool type"
        );
        verify_assert!(
            self,
            def.dfg.inst_debug(inst),
            rhs.is_bool_or_int(),
            "`or` operands must be of int/bool type"
        );
        verify_assert_eq!(
            self,
            def.dfg.inst_debug(inst),
            lhs,
            rhs,
            "`or` operands must be the same type"
        );
    }

    fn visit_xor(&mut self, inst: Inst, data: &CommutativeArithInst, def: &FunctionDefinition) {
        let (lhs, rhs) = (def.dfg.ty(data.lhs()), def.dfg.ty(data.rhs()));

        verify_assert!(
            self,
            def.dfg.inst_debug(inst),
            lhs.is_bool_or_int(),
            "`xor` operands must be of int/bool type"
        );
        verify_assert!(
            self,
            def.dfg.inst_debug(inst),
            rhs.is_bool_or_int(),
            "`xor` operands must be of int/bool type"
        );
        verify_assert_eq!(
            self,
            def.dfg.inst_debug(inst),
            lhs,
            rhs,
            "`xor` operands must be the same type"
        );
    }

    fn visit_shl(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition) {
        verify_integral_binop!(self, inst, "shl", data, def);
    }

    fn visit_ashr(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition) {
        verify_integral_binop!(self, inst, "ashr", data, def);
    }

    fn visit_lshr(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition) {
        verify_integral_binop!(self, inst, "lshr", data, def);
    }

    fn visit_iadd(&mut self, inst: Inst, data: &CommutativeArithInst, def: &FunctionDefinition) {
        verify_integral_binop!(self, inst, "iadd", data, def);
    }

    fn visit_isub(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition) {
        verify_integral_binop!(self, inst, "isub", data, def);
    }

    fn visit_imul(&mut self, inst: Inst, data: &CommutativeArithInst, def: &FunctionDefinition) {
        verify_integral_binop!(self, inst, "imul", data, def);
    }

    fn visit_sdiv(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition) {
        verify_integral_binop!(self, inst, "sdiv", data, def);
    }

    fn visit_udiv(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition) {
        verify_integral_binop!(self, inst, "udiv", data, def);
    }

    fn visit_srem(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition) {
        verify_integral_binop!(self, inst, "srem", data, def);
    }

    fn visit_urem(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition) {
        verify_integral_binop!(self, inst, "_", data, def);
    }

    fn visit_fneg(&mut self, inst: Inst, data: &FloatUnaryInst, def: &FunctionDefinition) {
        let v0 = def.dfg.ty(data.operand());

        verify_assert!(
            self,
            def.dfg.inst_debug(inst),
            v0.is_float(),
            "`fneg` can only operate on floating-point types"
        );
    }

    fn visit_fadd(&mut self, inst: Inst, data: &CommutativeArithInst, def: &FunctionDefinition) {
        verify_float_binop!(self, inst, "fadd", data, def);
    }

    fn visit_fsub(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition) {
        verify_float_binop!(self, inst, "fsub", data, def);
    }

    fn visit_fmul(&mut self, inst: Inst, data: &CommutativeArithInst, def: &FunctionDefinition) {
        verify_float_binop!(self, inst, "fmul", data, def);
    }

    fn visit_fdiv(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition) {
        verify_float_binop!(self, inst, "fdiv", data, def);
    }

    fn visit_frem(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition) {
        verify_float_binop!(self, inst, "frem", data, def);
    }

    fn visit_alloca(&mut self, _: Inst, _: &AllocaInst, _: &FunctionDefinition) {}

    fn visit_load(&mut self, inst: Inst, data: &LoadInst, def: &FunctionDefinition) {
        let ptr = def.dfg.ty(data.pointer());

        verify_assert_eq!(
            self,
            def.dfg.inst_debug(inst),
            ptr,
            Type::ptr(),
            "can only `load` from a pointer"
        );
    }

    fn visit_store(&mut self, inst: Inst, data: &StoreInst, def: &FunctionDefinition) {
        let ptr = def.dfg.ty(data.pointer());

        verify_assert_eq!(
            self,
            def.dfg.inst_debug(inst),
            ptr,
            Type::ptr(),
            "can only `store` to a pointer"
        );
    }

    fn visit_offset(&mut self, inst: Inst, data: &OffsetInst, def: &FunctionDefinition) {
        let ptr = def.dfg.ty(data.base());
        let offset = def.dfg.ty(data.offset());

        verify_assert!(
            self,
            def.dfg.inst_debug(inst),
            offset.is_int(),
            "`offset` must have integral pointer offset"
        );
        verify_assert_eq!(
            self,
            def.dfg.inst_debug(inst),
            ptr,
            Type::ptr(),
            "`offset` can only calculate an offset with a `ptr` base"
        );
    }

    fn visit_extract(&mut self, inst: Inst, data: &ExtractInst, def: &FunctionDefinition) {
        let agg_ty = def.dfg.ty(data.aggregate());

        verify_assert!(
            self,
            def.dfg.inst_debug(inst),
            agg_ty.is_array() || agg_ty.is_struct(),
            "can only `extract` from array or structure"
        );

        let pool = self.module().context().types();

        match agg_ty.unpack() {
            UType::Struct(record) => {
                let members = record.members(&pool);

                verify_assert!(
                    self,
                    def.dfg.inst_debug(inst),
                    (data.index() as usize) < members.len(),
                    "cannot `extract` beyond bounds of aggregate"
                );

                verify_assert_eq!(
                    self,
                    def.dfg.inst_debug(inst),
                    members[data.index() as usize],
                    data.result_ty().unwrap(),
                    "`extract` result type inaccurate"
                );
            }
            UType::Array(arr) => {
                let elem = arr.element(&pool);
                let len = arr.len(&pool);

                verify_assert!(
                    self,
                    def.dfg.inst_debug(inst),
                    data.index() < len,
                    "cannot `extract` beyond bounds of aggregate"
                );

                verify_assert_eq!(
                    self,
                    def.dfg.inst_debug(inst),
                    elem,
                    data.result_ty().unwrap(),
                    "`extract` result type inaccurate"
                );
            }
            _ => unreachable!(),
        }
    }

    fn visit_insert(&mut self, inst: Inst, data: &InsertInst, def: &FunctionDefinition) {
        let agg_ty = def.dfg.ty(data.aggregate());
        let insert_ty = def.dfg.ty(data.value());

        verify_assert!(
            self,
            def.dfg.inst_debug(inst),
            agg_ty.is_array() || agg_ty.is_struct(),
            "can only `insert` to array or structure"
        );

        verify_assert_eq!(
            self,
            def.dfg.inst_debug(inst),
            agg_ty,
            data.result_ty().unwrap(),
            "`insert` result type incorrect"
        );

        let pool = self.module().context().types();

        match agg_ty.unpack() {
            UType::Struct(record) => {
                let members = record.members(&pool);

                verify_assert!(
                    self,
                    def.dfg.inst_debug(inst),
                    (data.index() as usize) < members.len(),
                    "cannot `insert` beyond bounds of aggregate"
                );

                verify_assert_eq!(
                    self,
                    def.dfg.inst_debug(inst),
                    members[data.index() as usize],
                    insert_ty,
                    "`insert` operand is wrong type for aggregate slot"
                );
            }
            UType::Array(arr) => {
                let elem = arr.element(&pool);
                let len = arr.len(&pool);

                verify_assert!(
                    self,
                    def.dfg.inst_debug(inst),
                    data.index() < len,
                    "cannot `insert` beyond bounds of aggregate"
                );

                verify_assert_eq!(
                    self,
                    def.dfg.inst_debug(inst),
                    elem,
                    insert_ty,
                    "`insert` operand is wrong type for aggregate slot"
                );
            }
            _ => unreachable!(),
        }
    }

    fn visit_elemptr(&mut self, inst: Inst, data: &ElemPtrInst, def: &FunctionDefinition) {
        let agg_ty = data.aggregate_ty();

        verify_assert!(
            self,
            def.dfg.inst_debug(inst),
            agg_ty.is_array() || agg_ty.is_struct(),
            "can only `elemptr` to array or structure"
        );

        verify_assert_eq!(
            self,
            def.dfg.inst_debug(inst),
            Type::ptr(),
            def.dfg.ty(data.base()),
            "`elemptr` operand type incorrect"
        );

        let pool = self.module().type_pool();

        match agg_ty.unpack() {
            UType::Struct(record) => {
                let members = record.members(&pool);

                verify_assert!(
                    self,
                    def.dfg.inst_debug(inst),
                    (data.index() as usize) < members.len(),
                    "cannot `elemptr` beyond bounds of aggregate"
                );
            }
            UType::Array(arr) => {
                let len = arr.len(&pool);

                verify_assert!(
                    self,
                    def.dfg.inst_debug(inst),
                    data.index() < len,
                    "cannot `elemptr` beyond bounds of aggregate"
                );
            }
            _ => unreachable!(),
        }
    }

    fn visit_sext(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition) {
        let into = data.result_ty().unwrap();
        let from = def.dfg.ty(data.operand());

        verify_assert!(
            self,
            def.dfg.inst_debug(inst),
            into.is_int(),
            "`sext` output must be int"
        );
        verify_assert!(
            self,
            def.dfg.inst_debug(inst),
            from.is_int(),
            "`sext` input must be int"
        );
        verify_assert!(
            self,
            def.dfg.inst_debug(inst),
            into.as_int().unwrap().width() > from.as_int().unwrap().width(),
            "`sext` cannot convert to smaller or equal size int"
        );
    }

    fn visit_zext(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition) {
        let into = data.result_ty().unwrap();
        let from = def.dfg.ty(data.operand());

        verify_assert!(
            self,
            def.dfg.inst_debug(inst),
            into.is_int(),
            "`zext` output must be int"
        );
        verify_assert!(
            self,
            def.dfg.inst_debug(inst),
            from.is_int(),
            "`zext` input must be int"
        );
        verify_assert!(
            self,
            def.dfg.inst_debug(inst),
            into.as_int().unwrap().width() > from.as_int().unwrap().width(),
            "`zext` cannot convert to smaller or equal size int"
        );
    }

    fn visit_trunc(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition) {
        let into = data.result_ty().unwrap();
        let from = def.dfg.ty(data.operand());

        verify_assert!(
            self,
            def.dfg.inst_debug(inst),
            into.is_int(),
            "`trunc` output must be int"
        );

        verify_assert!(
            self,
            def.dfg.inst_debug(inst),
            from.is_int(),
            "`trunc` input must be int"
        );

        verify_assert!(
            self,
            def.dfg.inst_debug(inst),
            into.as_int().unwrap().width() < from.as_int().unwrap().width(),
            "`trunc` cannot convert to larger or equal size int"
        );
    }

    fn visit_itob(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition) {
        verify_cast!(self, inst, "itob", data, def, is_bool, is_int);
    }

    fn visit_btoi(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition) {
        verify_cast!(self, inst, "btoi", data, def, is_int, is_bool);
    }

    fn visit_sitof(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition) {
        verify_cast!(self, inst, "sitof", data, def, is_float, is_int);
    }

    fn visit_uitof(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition) {
        verify_cast!(self, inst, "uitof", data, def, is_float, is_int);
    }

    fn visit_ftosi(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition) {
        verify_cast!(self, inst, "ftosi", data, def, is_int, is_float);
    }

    fn visit_ftoui(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition) {
        verify_cast!(self, inst, "ftoui", data, def, is_int, is_float);
    }

    fn visit_fext(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition) {
        let into = data.result_ty().unwrap();
        let from = def.dfg.ty(data.operand());

        verify_assert!(
            self,
            def.dfg.inst_debug(inst),
            into.is_float_of_format(FloatFormat::Double),
            "`fext` output must be `f64`"
        );

        verify_assert!(
            self,
            def.dfg.inst_debug(inst),
            from.is_float_of_format(FloatFormat::Single),
            "`fext` input must be `f32`"
        );
    }

    fn visit_ftrunc(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition) {
        let into = data.result_ty().unwrap();
        let from = def.dfg.ty(data.operand());

        verify_assert!(
            self,
            def.dfg.inst_debug(inst),
            into.is_float_of_format(FloatFormat::Single),
            "`ftrunc` output must be `f32`"
        );

        verify_assert!(
            self,
            def.dfg.inst_debug(inst),
            from.is_float_of_format(FloatFormat::Double),
            "`ftrunc` input must be `f64`"
        );
    }

    fn visit_itop(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition) {
        verify_cast!(self, inst, "itop", data, def, is_ptr, is_int);
    }

    fn visit_ptoi(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition) {
        verify_cast!(self, inst, "ptoi", data, def, is_int, is_ptr);
    }

    fn visit_iconst(&mut self, inst: Inst, data: &IConstInst, def: &FunctionDefinition) {
        verify_assert!(
            self,
            def.dfg.inst_debug(inst),
            data.result_ty().unwrap().is_int(),
            "type of `iconst` must be integral"
        );

        verify_assert_eq!(
            self,
            def.dfg.inst_debug(inst),
            data.value(),
            data.given_value(),
            "`iconst` value is too large to fit in constant of that type"
        );
    }

    fn visit_fconst(&mut self, inst: Inst, data: &FConstInst, def: &FunctionDefinition) {
        verify_assert!(
            self,
            def.dfg.inst_debug(inst),
            data.result_ty().unwrap().is_float(),
            "type of `fconst` must be integral"
        );
    }

    fn visit_bconst(&mut self, _: Inst, _: &BConstInst, _: &FunctionDefinition) {}

    fn visit_undef(&mut self, _: Inst, _: &UndefConstInst, _: &FunctionDefinition) {}

    fn visit_null(&mut self, _: Inst, _: &NullConstInst, _: &FunctionDefinition) {}

    fn visit_stackslot(&mut self, inst: Inst, stackslot: &StackSlotInst, def: &FunctionDefinition) {
        verify_assert!(
            self,
            def.dfg.inst_debug(inst),
            def.dfg.is_stack_slot_inserted(stackslot.slot()),
            "stack slot must be valid"
        );
    }

    fn visit_globaladdr(&mut self, _: Inst, _: &GlobalAddrInst, _: &FunctionDefinition) {
        todo!()
    }
}
