//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::arena::SecondaryMap;
use crate::ir::*;
use crate::pass::{ModuleAnalysisManager, ModuleAnalysisPass};
use crate::utility::{Str, StringPool};
use std::any::TypeId;
use std::ops::Range;
use std::sync::RwLockReadGuard;

/// A simple SIR -> text pass that takes in an entire module, turns it into
/// textual SIR, and then maps each IR entity to a range of text referring to it.
///
/// This can be used for debug/test passes that need to produce human-readable SIR.
#[derive(Debug, Clone)]
pub struct ModuleWriter {
    whole: String,
    val_ranges: SecondaryMap<Value, Range<usize>>,
    inst_ranges: SecondaryMap<Inst, Range<usize>>,
    block_ranges: SecondaryMap<Block, Range<usize>>,
    func_ranges: SecondaryMap<Func, Range<usize>>,
}

impl ModuleWriter {
    fn from(module: &Module) -> Self {
        let mut writer_impl = WriterImpl {
            module,
            pool_guard: module.context().types(),
            string_guard: module.context().strings(),
            state: ModuleWriter {
                whole: String::default(),
                val_ranges: SecondaryMap::default(),
                inst_ranges: SecondaryMap::default(),
                block_ranges: SecondaryMap::default(),
                func_ranges: SecondaryMap::default(),
            },
            values: SecondaryMap::default(),
            next: 0,
        };

        writer_impl.walk();

        writer_impl.state
    }

    /// Stringifies a SIR type. Unlike the rest of this module, this type does not necessarily
    /// have to have been used in the module that this was constructed from.
    pub fn ty(&self, ctx: &TypePool, ty: Type) -> String {
        stringify_ty(ctx, ty)
    }

    /// Provides the name of a value. This is the `%_` syntax.
    pub fn val(&self, value: Value) -> &str {
        &self.whole[self.val_ranges[value].clone()]
    }

    /// Stringifies an entire instruction. This includes the result if the
    /// instruction actually has one.
    pub fn inst(&self, inst: Inst) -> &str {
        &self.whole[self.inst_ranges[inst].clone()]
    }

    /// Stringifies a whole block. This includes the block label, any block
    /// parameters, and every instruction in the block.
    pub fn block(&self, bb: Block) -> &str {
        &self.whole[self.block_ranges[bb].clone()]
    }

    /// Stringifies a whole function. This includes every block, and the function prototype.
    pub fn func(&self, func: Func) -> &str {
        &self.whole[self.func_ranges[func].clone()]
    }

    /// Returns the entire module as a string.
    pub fn module(&self) -> &str {
        &self.whole
    }
}

/// Prints an entire module to `stdout`.
///
/// Wrapper for when setting up a pass/analysis manager and running the writer
/// pass is too much.
pub fn print_module(module: &Module) {
    println!("{}", ModuleWriter::from(module).module());
}

/// Writes an entire module to a [`String`].
pub fn stringify_module(module: &Module) -> String {
    ModuleWriter::from(module).module().to_owned()
}

/// This is an analysis that provides a [`ModuleWriter`] to any code that wants it.
///
/// This analysis needs to be run in the standard way for a correct [`ModuleWriter`]
/// to be produced, the result yielded by the analysis can then be queried as desired.
///
/// Note that this analysis is not intended to be run in the hot path of the compiler, it
/// maintains a lock on the type pool while running.
pub struct ModuleStringifyAnalysis;

impl ModuleAnalysisPass for ModuleStringifyAnalysis {
    type Result = ModuleWriter;

    fn expects_preserved(&self) -> &'static [TypeId] {
        &[]
    }

    fn run(&mut self, module: &Module, _: &ModuleAnalysisManager) -> Self::Result {
        ModuleWriter::from(module)
    }
}

pub(crate) fn stringify_ty(ctx: &TypePool, ty: Type) -> String {
    match ty.unpack() {
        UType::Bool(_) => "bool".to_owned(),
        UType::Ptr(_) => "ptr".to_owned(),
        UType::Int(i) => format!("i{}", i.width()),
        UType::Float(f) => {
            let real = if f.format() == FloatFormat::Single {
                "f32"
            } else {
                "f64"
            };

            real.to_owned()
        }
        UType::Array(arr) => {
            format!(
                "[{}; {}]",
                stringify_ty(ctx, arr.element(ctx)),
                arr.len(ctx)
            )
        }
        UType::Struct(structure) => {
            let members = structure.members(ctx);

            if members.is_empty() {
                return "{}".to_owned();
            }

            let mut result = "{ ".to_owned();

            for field in structure.members(ctx) {
                result += &format!("{}, ", stringify_ty(ctx, *field));
            }

            if result.ends_with(", ") {
                result.truncate(result.len() - ", ".len());
            }

            result + " }"
        }
    }
}

pub(crate) fn stringify_return_ty(ctx: &TypePool, ty: Option<Type>) -> String {
    match ty {
        Some(ty) => stringify_ty(ctx, ty),
        None => "void".to_owned(),
    }
}

fn write_sig_params(buf: &mut String, ctx: &TypePool, sig: &Signature) {
    *buf += "(";

    let mut it = sig.params().iter().peekable();

    while let Some((ty, _)) = it.next() {
        *buf += &stringify_ty(ctx, *ty);

        if it.peek().is_some() {
            *buf += ", ";
        } else if sig.vararg() {
            *buf += ", ...";
        }
    }

    *buf += ")"
}

pub(crate) fn stringify_signature_params(ctx: &TypePool, sig: &Signature) -> String {
    let mut buf = String::default();

    write_sig_params(&mut buf, ctx, sig);

    buf
}

pub(crate) fn stringify_signature(ctx: &TypePool, sig: &Signature) -> String {
    let mut buf = stringify_return_ty(ctx, sig.return_ty());

    buf += " ";

    write_sig_params(&mut buf, ctx, sig);

    buf
}

pub(crate) fn stringify_abi(abi: CallConv) -> &'static str {
    match abi {
        CallConv::C => "ccc",
        CallConv::Fast => "fastcc",
    }
}

impl ValueName {
    fn into_string(self, pool: &StringPool) -> String {
        match self {
            ValueName::Num(x) => format!("%{x}"),
            ValueName::Name(s) => format!("%{}", &pool[s]),
        }
    }
}

#[derive(Copy, Clone)]
enum ValueName {
    Num(u32),
    Name(Str),
}

struct WriterImpl<'m> {
    module: &'m Module,
    pool_guard: RwLockReadGuard<'m, TypePool>,
    string_guard: RwLockReadGuard<'m, StringPool>,
    state: ModuleWriter,
    values: SecondaryMap<Value, ValueName>,
    next: u32,
}

impl<'m> WriterImpl<'m> {
    fn ty(&self, ty: Type) -> String {
        stringify_ty(&self.pool_guard, ty)
    }

    fn ty_void(&self, ty: Option<Type>) -> String {
        stringify_return_ty(&self.pool_guard, ty)
    }

    fn param_tys(&self, sig: &Signature) -> String {
        stringify_signature_params(&self.pool_guard, sig)
    }

    fn func_name(&self, func: Func) -> String {
        format!("@{}", self.module().function(func).name())
    }

    fn result(&mut self, inst: Inst, def: &FunctionDefinition) {
        if let Some(val) = def.dfg.inst_to_result(inst) {
            let name = self.name(val, def);
            let begin = self.state.whole.len();

            self.state.whole += &format!("{name} = ");
            self.state
                .val_ranges
                .insert(val, begin..(begin + name.len()));
        }
    }

    fn commutative_arith(
        &mut self,
        name: &'static str,
        inst: Inst,
        data: &CommutativeArithInst,
        def: &FunctionDefinition,
    ) {
        self.result(inst, def);

        let ty = self.ty(data.result_ty().unwrap());
        let lhs = self.name(data.lhs(), def);
        let rhs = self.name(data.rhs(), def);

        self.state.whole += &format!("{name} {ty} {lhs}, {rhs}");
    }

    fn arith(
        &mut self,
        name: &'static str,
        inst: Inst,
        data: &ArithInst,
        def: &FunctionDefinition,
    ) {
        self.result(inst, def);

        let ty = self.ty(data.result_ty().unwrap());
        let lhs = self.name(data.lhs(), def);
        let rhs = self.name(data.rhs(), def);

        self.state.whole += &format!("{name} {ty} {lhs}, {rhs}");
    }

    fn cast(&mut self, name: &'static str, inst: Inst, data: &CastInst, def: &FunctionDefinition) {
        self.result(inst, def);

        let into = self.ty(data.result_ty().unwrap());
        let from = self.name_ty(data.operand(), def);

        self.state.whole += &format!("{name} {into}, {from}");
    }

    fn args(&mut self, vals: &[Value], def: &FunctionDefinition) -> String {
        let mut result = String::default();
        let mut it = vals.iter().copied().peekable();

        while let Some(param) = it.next() {
            result += &self.name_ty(param, def);

            if it.peek().is_some() {
                result += ", ";
            }
        }

        result
    }

    fn block_target(&mut self, block: &BlockWithParams, def: &FunctionDefinition) -> String {
        let bb = block.block();
        let pool = self.module().context().strings();
        let name = pool.get(def.dfg.block(bb).name()).unwrap();

        if block.args().is_empty() {
            name.to_owned()
        } else {
            let args = self.args(block.args(), def);

            format!("{name}({args})")
        }
    }

    fn name_ty(&mut self, val: Value, def: &FunctionDefinition) -> String {
        let ty = self.ty(def.dfg.ty(val));
        let val = self.name(val, def);

        format!("{ty} {val}")
    }

    fn name(&mut self, val: Value, def: &FunctionDefinition) -> String {
        let name = match self.values.get(val) {
            Some(name) => *name,
            None => self.insert_name(val, def),
        };

        name.into_string(&self.string_guard)
    }

    fn insert_name(&mut self, val: Value, def: &FunctionDefinition) -> ValueName {
        let new = match def.dfg.debug(val).name() {
            Some(s) => ValueName::Name(s),
            None => {
                self.next += 1;
                ValueName::Num(self.next - 1)
            }
        };

        self.values.insert(val, new);

        new
    }
}

impl<'m> SIRVisitor<'m> for WriterImpl<'m> {
    fn module(&self) -> &'m Module {
        self.module
    }

    fn walk(&mut self) {
        let mut it = self.module().functions().peekable();

        // if we have any functions at all, print first one without leading \n
        if let Some(func) = it.next() {
            self.visit_func(func);
        }

        // for any remaining functions, print newlines to split them up
        // then print the function
        for func in it {
            self.state.whole += "\n";

            self.visit_func(func);
        }
    }

    fn visit_func(&mut self, func: Func) {
        let begin = self.state.whole.len();

        {
            let f = self.module().function(func);
            let sig = f.signature();
            let ty = self.ty_void(sig.return_ty());
            let name = self.func_name(func);
            let params = self.param_tys(sig);

            // 'fn T @name(tys) '
            self.state.whole += &format!("fn {ty} {name}{params}");

            // '{fastcc|sysv|win64|ccc} '
            match sig.calling_conv() {
                CallConv::C => {}
                abi => self.state.whole += &format!("{} ", stringify_abi(abi)),
            }

            // body
            if let Some(def) = f.definition() {
                self.state.whole += " {\n";

                for block in def.layout.blocks() {
                    self.visit_block(block, def);

                    // add a gap to make it easier to read
                    self.state.whole += "\n";
                }

                // remove last gap so the } is immediately after
                self.state
                    .whole
                    .truncate(self.state.whole.len() - "\n".len());

                // blocks print a newline after every inst, including last one
                self.state.whole += "}";
            }

            self.state.whole += "\n";
        }

        let end = self.state.whole.len();

        self.state.func_ranges.insert(func, begin..end);
    }

    fn visit_block(&mut self, block: Block, def: &FunctionDefinition) {
        let begin = self.state.whole.len();

        {
            let bb = def.dfg.block(block);

            self.state.whole += self.string_guard.get(bb.name()).unwrap();

            if !bb.params().is_empty() {
                self.state.whole += "(";

                //
                // the reason we don't use self.args is because these are **new** value names,
                // so we need to add them to val_ranges.
                //
                // we can't do that inside of self.args because it returns a string by design,
                // it doesn't directly mutate self.state.whole
                //
                let mut it = bb.params().iter().copied().peekable();

                while let Some(param) = it.next() {
                    let begin = self.state.whole.len();

                    {
                        let pair = self.name_ty(param, def);
                        self.state.whole += &pair;
                    }

                    let end = self.state.whole.len();

                    self.state.val_ranges.insert(param, begin..end);

                    if it.peek().is_some() {
                        self.state.whole += ", ";
                    }
                }

                self.state.whole += ")";
            }

            self.state.whole += ":\n";
            self.dispatch_insts(block, def);
        }

        let end = self.state.whole.len();

        self.state.block_ranges.insert(block, begin..end);
    }

    fn visit_inst(&mut self, inst: Inst, def: &FunctionDefinition) {
        let begin = self.state.whole.len();

        {
            self.state.whole += "  ";
            self.dispatch_inst(inst, def.dfg.data(inst), def);
            self.state.whole += "\n";
        }

        let end = self.state.whole.len();

        self.state.inst_ranges.insert(inst, begin..end);
    }

    fn visit_call(&mut self, inst: Inst, data: &CallInst, def: &FunctionDefinition) {
        self.result(inst, def);

        let ret = self.ty_void(data.result_ty());
        let name = self.func_name(data.callee());
        let args = self.args(data.args(), def);

        self.state.whole += &format!("call {ret} {name}({args})",);
    }

    fn visit_indirectcall(
        &mut self,
        inst: Inst,
        data: &IndirectCallInst,
        def: &FunctionDefinition,
    ) {
        self.result(inst, def);

        let ret = self.ty_void(data.result_ty());
        let signature = def.dfg.signature(data.sig());
        let sig = stringify_signature_params(&self.pool_guard, signature);
        let callee = self.name_ty(data.callee(), def);
        let args = self.args(data.args(), def);

        self.state.whole += &format!("indirectcall {ret} {sig}, {callee}({args})");
    }

    fn visit_icmp(&mut self, inst: Inst, data: &ICmpInst, def: &FunctionDefinition) {
        self.result(inst, def);

        let opc = match data.op() {
            ICmpOp::EQ => "eq",
            ICmpOp::NE => "ne",
            ICmpOp::SGT => "sgt",
            ICmpOp::SLT => "slt",
            ICmpOp::SGE => "sge",
            ICmpOp::SLE => "sle",
            ICmpOp::UGT => "ugt",
            ICmpOp::ULT => "ult",
            ICmpOp::UGE => "uge",
            ICmpOp::ULE => "ule",
        };

        let ty = stringify_ty(&self.pool_guard, def.dfg.ty(data.lhs()));
        let lhs = self.name(data.lhs(), def);
        let rhs = self.name(data.rhs(), def);

        self.state.whole += &format!("icmp {opc} {ty} {lhs}, {rhs}",);
    }

    fn visit_fcmp(&mut self, inst: Inst, data: &FCmpInst, def: &FunctionDefinition) {
        self.result(inst, def);

        let opc = match data.op() {
            FCmpOp::UNO => "uno",
            FCmpOp::ORD => "ord",
            FCmpOp::OEQ => "oeq",
            FCmpOp::ONE => "one",
            FCmpOp::OGT => "ogt",
            FCmpOp::OLT => "olt",
            FCmpOp::OGE => "oge",
            FCmpOp::OLE => "ole",
            FCmpOp::UEQ => "ueq",
            FCmpOp::UNE => "une",
            FCmpOp::UGT => "ugt",
            FCmpOp::ULT => "ult",
            FCmpOp::UGE => "uge",
            FCmpOp::ULE => "ule",
        };

        let ty = stringify_ty(&self.pool_guard, def.dfg.ty(data.lhs()));
        let lhs = self.name(data.lhs(), def);
        let rhs = self.name(data.rhs(), def);

        self.state.whole += &format!("fcmp {opc} {ty} {lhs}, {rhs}",);
    }

    fn visit_sel(&mut self, inst: Inst, data: &SelInst, def: &FunctionDefinition) {
        self.result(inst, def);

        let ty = stringify_ty(&self.pool_guard, def.dfg.ty(data.if_true()));
        let cond = self.name(data.condition(), def);
        let lhs = self.name(data.if_true(), def);
        let rhs = self.name(data.if_false(), def);

        self.state.whole += &format!("sel {ty}, bool {cond}, {lhs}, {rhs}",);
    }

    fn visit_br(&mut self, _: Inst, data: &BrInst, def: &FunctionDefinition) {
        let target = self.block_target(data.target(), def);

        self.state.whole += &format!("br {target}");
    }

    fn visit_condbr(&mut self, _: Inst, data: &CondBrInst, def: &FunctionDefinition) {
        let cond = self.name(data.condition(), def);
        let if_true = self.block_target(data.true_branch(), def);
        let if_false = self.block_target(data.false_branch(), def);

        self.state.whole += &format!("condbr bool {cond}, {if_true}, {if_false}");
    }

    fn visit_unreachable(&mut self, _: Inst, _: &UnreachableInst, _: &FunctionDefinition) {
        self.state.whole += "unreachable";
    }

    fn visit_ret(&mut self, _: Inst, data: &RetInst, def: &FunctionDefinition) {
        match data.value() {
            Some(val) => {
                let ty = self.ty(def.dfg.ty(val));
                let val = self.name(val, def);

                self.state.whole += &format!("ret {ty} {val}");
            }
            None => self.state.whole += "ret void",
        }
    }

    fn visit_and(&mut self, inst: Inst, data: &CommutativeArithInst, def: &FunctionDefinition) {
        self.commutative_arith("and", inst, data, def);
    }

    fn visit_or(&mut self, inst: Inst, data: &CommutativeArithInst, def: &FunctionDefinition) {
        self.commutative_arith("or", inst, data, def);
    }

    fn visit_xor(&mut self, inst: Inst, data: &CommutativeArithInst, def: &FunctionDefinition) {
        self.commutative_arith("xor", inst, data, def);
    }

    fn visit_shl(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition) {
        self.arith("shl", inst, data, def);
    }

    fn visit_ashr(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition) {
        self.arith("ashr", inst, data, def);
    }

    fn visit_lshr(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition) {
        self.arith("lshr", inst, data, def);
    }

    fn visit_iadd(&mut self, inst: Inst, data: &CommutativeArithInst, def: &FunctionDefinition) {
        self.commutative_arith("iadd", inst, data, def);
    }

    fn visit_isub(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition) {
        self.arith("isub", inst, data, def);
    }

    fn visit_imul(&mut self, inst: Inst, data: &CommutativeArithInst, def: &FunctionDefinition) {
        self.commutative_arith("imul", inst, data, def);
    }

    fn visit_sdiv(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition) {
        self.arith("sdiv", inst, data, def);
    }

    fn visit_udiv(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition) {
        self.arith("udiv", inst, data, def);
    }

    fn visit_srem(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition) {
        self.arith("srem", inst, data, def);
    }

    fn visit_urem(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition) {
        self.arith("urem", inst, data, def);
    }

    fn visit_fneg(&mut self, inst: Inst, data: &FloatUnaryInst, def: &FunctionDefinition) {
        self.result(inst, def);

        let ty = self.ty(data.result_ty().unwrap());
        let val = self.name(data.operand(), def);

        self.state.whole += &format!("fneg {ty} {val}");
    }

    fn visit_fadd(&mut self, inst: Inst, data: &CommutativeArithInst, def: &FunctionDefinition) {
        self.commutative_arith("fadd", inst, data, def);
    }

    fn visit_fsub(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition) {
        self.arith("fsub", inst, data, def);
    }

    fn visit_fmul(&mut self, inst: Inst, data: &CommutativeArithInst, def: &FunctionDefinition) {
        self.commutative_arith("fmul", inst, data, def);
    }

    fn visit_fdiv(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition) {
        self.arith("fdiv", inst, data, def);
    }

    fn visit_frem(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition) {
        self.arith("frem", inst, data, def);
    }

    fn visit_alloca(&mut self, inst: Inst, data: &AllocaInst, def: &FunctionDefinition) {
        self.result(inst, def);

        let ty = self.ty(data.alloc_ty());

        self.state.whole += &format!("alloca {ty}");
    }

    fn visit_load(&mut self, inst: Inst, data: &LoadInst, def: &FunctionDefinition) {
        self.result(inst, def);

        let ty = self.ty(data.result_ty().unwrap());
        let val = self.name_ty(data.pointer(), def);

        self.state.whole += &format!("load {ty}, {val}");
    }

    fn visit_store(&mut self, _: Inst, data: &StoreInst, def: &FunctionDefinition) {
        let val = self.name_ty(data.stored(), def);
        let ptr = self.name_ty(data.pointer(), def);

        self.state.whole += &format!("store {val}, {ptr}");
    }

    fn visit_offset(&mut self, inst: Inst, data: &OffsetInst, def: &FunctionDefinition) {
        self.result(inst, def);

        let ty = self.ty(data.offset_ty());
        let ty2 = self.ty(def.dfg.ty(data.base()));
        let ty3 = self.ty(def.dfg.ty(data.offset()));
        let ptr = self.name(data.base(), def);
        let offset = self.name(data.offset(), def);

        // we could hard-code ptr here but this is supposed to work even when the IR is broken
        self.state.whole += &format!("offset {ty}, {ty2} {ptr}, {ty3} {offset}");
    }

    fn visit_extract(&mut self, inst: Inst, data: &ExtractInst, def: &FunctionDefinition) {
        self.result(inst, def);

        let ty = self.ty(data.result_ty().unwrap());
        let agg = self.name_ty(data.aggregate(), def);
        let index = data.index();

        self.state.whole += &format!("extract {ty}, {agg}, {index}");
    }

    fn visit_insert(&mut self, inst: Inst, data: &InsertInst, def: &FunctionDefinition) {
        self.result(inst, def);

        let agg = self.name_ty(data.aggregate(), def);
        let val = self.name_ty(data.value(), def);
        let index = data.index();

        self.state.whole += &format!("insert {agg}, {val}, {index}");
    }

    fn visit_elemptr(&mut self, inst: Inst, data: &ElemPtrInst, def: &FunctionDefinition) {
        self.result(inst, def);

        let agg = self.ty(data.aggregate_ty());
        let base = self.name_ty(data.base(), def);
        let index = data.index();

        self.state.whole += &format!("elemptr {agg}, {base}, {index}");
    }

    fn visit_sext(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition) {
        self.cast("sext", inst, data, def);
    }

    fn visit_zext(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition) {
        self.cast("zext", inst, data, def);
    }

    fn visit_trunc(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition) {
        self.cast("trunc", inst, data, def);
    }

    fn visit_itob(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition) {
        self.cast("itob", inst, data, def);
    }

    fn visit_btoi(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition) {
        self.cast("btoi", inst, data, def);
    }

    fn visit_sitof(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition) {
        self.cast("sitof", inst, data, def);
    }

    fn visit_uitof(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition) {
        self.cast("uitof", inst, data, def);
    }

    fn visit_ftosi(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition) {
        self.cast("ftosi", inst, data, def);
    }

    fn visit_ftoui(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition) {
        self.cast("ftoui", inst, data, def);
    }

    fn visit_fext(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition) {
        self.cast("fext", inst, data, def);
    }

    fn visit_ftrunc(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition) {
        self.cast("ftrunc", inst, data, def);
    }

    fn visit_itop(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition) {
        self.cast("itop", inst, data, def);
    }

    fn visit_ptoi(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition) {
        self.cast("ptoi", inst, data, def);
    }

    fn visit_iconst(&mut self, inst: Inst, data: &IConstInst, def: &FunctionDefinition) {
        self.result(inst, def);

        let int_type = data.result_ty().unwrap();
        let int_ty = int_type.unwrap_int();
        let ty = self.ty(data.result_ty().unwrap());

        // if the sign bit is set, format it as a negative
        let value = if data.value() != (!int_ty.sign_bit() & data.value() & int_ty.mask()) {
            match int_ty.width() {
                8 => format!("{}", data.value() as i8),
                16 => format!("{}", data.value() as i16),
                32 => format!("{}", data.value() as i32),
                64 => format!("{}", data.value() as i64),
                _ => unreachable!(),
            }
        } else {
            format!("{}", data.value())
        };

        self.state.whole += &format!("iconst {ty} {value}");
    }

    fn visit_fconst(&mut self, inst: Inst, data: &FConstInst, def: &FunctionDefinition) {
        self.result(inst, def);

        let ty = self.ty(data.result_ty().unwrap());
        let value = data.value();
        let is_nan = match data.result_ty().unwrap().unwrap_float().format() {
            FloatFormat::Single => f32::from_bits(value as u32).is_nan(),
            FloatFormat::Double => f64::from_bits(value).is_nan(),
        };

        let result = if is_nan {
            format!("fconst {ty} NaN")
        } else {
            format!("fconst {ty} 0xfp{value:020X}")
        };

        self.state.whole += &result;
    }

    fn visit_bconst(&mut self, inst: Inst, data: &BConstInst, def: &FunctionDefinition) {
        self.result(inst, def);

        let ty = self.ty(data.result_ty().unwrap());
        let value = data.value();

        self.state.whole += &format!("bconst {ty} {value}");
    }

    fn visit_undef(&mut self, inst: Inst, data: &UndefConstInst, def: &FunctionDefinition) {
        self.result(inst, def);

        let ty = self.ty(data.result_ty().unwrap());

        self.state.whole += &format!("undef {ty}");
    }

    fn visit_null(&mut self, inst: Inst, data: &NullConstInst, def: &FunctionDefinition) {
        self.result(inst, def);

        let ty = self.ty(data.result_ty().unwrap());

        self.state.whole += &format!("null {ty}");
    }

    fn visit_globaladdr(&mut self, inst: Inst, data: &GlobalAddrInst, def: &FunctionDefinition) {
        self.result(inst, def);

        let name = data.name();

        self.state.whole += &format!("globaladdr @{name}");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_write_type() {
        let mut module = Module::new("test");
        let writer = ModuleWriter::from(&module);

        {
            let pool = module.type_pool();

            assert_eq!(writer.ty(&pool, Type::bool()), "bool");
            assert_eq!(writer.ty(&pool, Type::ptr()), "ptr");
            assert_eq!(writer.ty(&pool, Type::i8()), "i8");
            assert_eq!(writer.ty(&pool, Type::i16()), "i16");
            assert_eq!(writer.ty(&pool, Type::i32()), "i32");
            assert_eq!(writer.ty(&pool, Type::i64()), "i64");
            assert_eq!(writer.ty(&pool, Type::f32()), "f32");
            assert_eq!(writer.ty(&pool, Type::f64()), "f64");
        }

        {
            let i8_512 = Type::array(&mut module.type_pool_mut(), Type::i8(), 512);
            assert_eq!(writer.ty(&module.type_pool(), i8_512), "[i8; 512]");

            let i8_512_16 = Type::array(&mut module.type_pool_mut(), i8_512, 16);
            assert_eq!(writer.ty(&module.type_pool(), i8_512_16), "[[i8; 512]; 16]");

            let ptr_0 = Type::array(&mut module.type_pool_mut(), Type::ptr(), 0);
            assert_eq!(writer.ty(&module.type_pool(), ptr_0), "[ptr; 0]");

            let unit = Type::structure(&mut module.type_pool_mut(), &[]);
            let unit_42 = Type::array(&mut module.type_pool_mut(), unit, 42);
            assert_eq!(writer.ty(&module.type_pool(), unit_42), "[{}; 42]");

            let slice = Type::structure(&mut module.type_pool_mut(), &[Type::ptr(), Type::i64()]);
            let slice_64 = Type::array(&mut module.type_pool_mut(), slice, 64);
            let struct_slice_64 = Type::structure(&mut module.type_pool_mut(), &[slice_64]);
            let struct_slice_64_732 =
                Type::array(&mut module.type_pool_mut(), struct_slice_64, 732);
            assert_eq!(
                writer.ty(&module.type_pool(), struct_slice_64_732),
                "[{ [{ ptr, i64 }; 64] }; 732]"
            );
        }

        {
            let unit = Type::structure(&mut module.type_pool_mut(), &[]);
            assert_eq!(writer.ty(&module.type_pool(), unit), "{}");

            let single = Type::structure(&mut module.type_pool_mut(), &[Type::bool()]);
            assert_eq!(writer.ty(&module.type_pool(), single), "{ bool }");

            let double = Type::structure(&mut module.type_pool_mut(), &[Type::f32(), Type::f64()]);
            assert_eq!(writer.ty(&module.type_pool(), double), "{ f32, f64 }");

            let quadruple = Type::structure(
                &mut module.type_pool_mut(),
                &[Type::i16(), Type::i64(), Type::i32(), Type::i8()],
            );
            assert_eq!(
                writer.ty(&module.type_pool(), quadruple),
                "{ i16, i64, i32, i8 }"
            );

            let triple2 = Type::structure(
                &mut module.type_pool_mut(),
                &[Type::f64(), Type::f64(), Type::f64()],
            );
            assert_eq!(writer.ty(&module.type_pool(), triple2), "{ f64, f64, f64 }");
        }
    }

    #[test]
    fn test_write_none() {
        let module = Module::new("test");

        assert_eq!(ModuleWriter::from(&module).module(), "");
    }

    #[test]
    fn test_write_declarations() {
        let mut module = Module::new("test");
        let sig = SigBuilder::new()
            .ret(Some(Type::i32()))
            .param(Type::ptr())
            .build();
        let _ = module.declare_function("puts", sig);

        assert_eq!(ModuleWriter::from(&module).module(), "fn i32 @puts(ptr)\n");

        let sig2 = SigBuilder::new()
            .params(&[Type::i64(), Type::i32()])
            .vararg(true)
            .build();
        let _ = module.declare_function("frobnicator", sig2);

        let expected = r#"fn i32 @puts(ptr)

fn void @frobnicator(i64, i32, ...)
"#;

        assert_eq!(ModuleWriter::from(&module).module(), expected);
    }

    #[test]
    fn test_write_single_block_invalid_empty() {
        let mut module = Module::new("test");
        let sig = SigBuilder::new()
            .ret(Some(Type::i32()))
            .params(&[Type::i32(), Type::ptr()])
            .build();

        {
            // fn i32 @main(i32, ptr) {
            let mut builder = module.define_function("main", sig);

            // entry(i32 %0, ptr %1):
            let entry = builder.create_block("entry");
            builder.append_entry_params(entry, DebugInfo::fake());
            builder.switch_to(entry);

            // }
            let _ = builder.define();
        }

        let expected = r#"fn i32 @main(i32, ptr) {
entry(i32 %0, ptr %1):
}
"#;

        assert_eq!(ModuleWriter::from(&module).module(), expected);
    }

    #[test]
    fn test_write_single_block_invalid_block_params() {
        let mut module = Module::new("test");
        let sig = SigBuilder::new()
            .ret(Some(Type::i32()))
            .param(Type::ptr())
            .vararg(true)
            .build();

        {
            // fn i32 @printf(ptr, ...) {
            let mut builder = module.define_function("printf", sig);

            // entry:
            let entry = builder.create_block("entry");
            builder.switch_to(entry);

            //
            let zero = builder.append().null(Type::i32(), DebugInfo::fake());
            builder.append().ret_val(zero, DebugInfo::fake());

            // }
            let _ = builder.define();
        }

        let expected = r#"fn i32 @printf(ptr, ...) {
entry:
  %0 = null i32
  ret i32 %0
}
"#;

        assert_eq!(ModuleWriter::from(&module).module(), expected);
    }

    #[test]
    fn test_write_single_block_valid() {
        let mut module = Module::new("test");
        let sig = {
            let mut pool = module.type_pool_mut();

            SigBuilder::new()
                .ret(Some(Type::f64()))
                .params(&[Type::structure(
                    &mut pool,
                    &[Type::f64(), Type::f64(), Type::f64()],
                )])
                .build()
        };

        {
            // fn f64 @y({ f64, f64, f64 }) {
            let mut builder = module.define_function("x_coord", sig);

            // entry({ f64, f64, f64} %0):
            let entry = builder.create_block("entry");
            builder.append_entry_params(entry, DebugInfo::fake());
            builder.switch_to(entry);

            // %1 = extract f64, { f64, f64, f64 } %0, 1
            let agg = builder.block_params(entry)[0];
            let extract = builder
                .append()
                .extract(Type::f64(), agg, 1, DebugInfo::fake());
            builder.append().ret_val(extract, DebugInfo::fake());

            // }
            let _ = builder.define();
        }

        let expected = r#"fn f64 @x_coord({ f64, f64, f64 }) {
entry({ f64, f64, f64 } %0):
  %1 = extract f64, { f64, f64, f64 } %0, 1
  ret f64 %1
}
"#;

        assert_eq!(ModuleWriter::from(&module).module(), expected);
    }

    #[test]
    fn test_write_multiple_blocks_invalid_empty() {
        let mut module = Module::new("test");
        let sig = SigBuilder::new().param(Type::bool()).build();

        {
            // fn void @test(bool) {
            let mut builder = module.define_function("test", sig);

            // entry:
            // a:
            // b:
            // c:
            let _ = builder.create_block("entry");
            let _ = builder.create_block("a");
            let _ = builder.create_block("b");
            let _ = builder.create_block("c");

            // }
            let _ = builder.define();
        }

        let expected = r#"fn void @test(bool) {
entry:

a:

b:

c:
}
"#;

        assert_eq!(ModuleWriter::from(&module).module(), expected);
    }

    #[test]
    fn test_write_multiple_blocks_valid_no_branch_params() {
        let mut module = Module::new("test");
        let sig = SigBuilder::new()
            .param(Type::bool())
            .ret(Some(Type::bool()))
            .build();

        {
            // fn void @test(bool) {
            let mut builder = module.define_function("test", sig);

            // entry(bool %0):
            // a:
            // b:
            // c:
            let entry = builder.create_block("entry");
            let a = builder.create_block("a");
            let b = builder.create_block("b");
            let c = builder.create_block("c");

            builder.append_entry_params(entry, DebugInfo::fake());
            builder.switch_to(entry);

            // condbr bool %0, a, b
            let cond = builder.block_params(entry)[0];
            let if_true = BlockWithParams::new(a, &[]);
            let if_false = BlockWithParams::new(b, &[]);

            builder
                .append()
                .condbr(cond, if_true, if_false, DebugInfo::fake());

            let target = BlockWithParams::new(c, &[]);

            // br c
            builder.switch_to(a);
            builder.append().br(target.clone(), DebugInfo::fake());

            // br c
            builder.switch_to(b);
            builder.append().br(target, DebugInfo::fake());

            // ret void
            builder.switch_to(c);
            builder.append().ret_val(cond, DebugInfo::fake());

            // }
            let _ = builder.define();
        }

        let expected = r#"fn bool @test(bool) {
entry(bool %0):
  condbr bool %0, a, b

a:
  br c

b:
  br c

c:
  ret bool %0
}
"#;

        assert_eq!(ModuleWriter::from(&module).module(), expected);
    }

    #[test]
    fn test_write_multiple_blocks_valid_with_branch_params() {
        let mut module = Module::new("test");
        let sig = SigBuilder::new()
            .param(Type::i64())
            .ret(Some(Type::i64()))
            .build();

        {
            let f = DebugInfo::fake();

            // fn i64 @magic(i64) {
            let mut builder = module.define_function("magic", sig);

            // entry(i64 %0):
            let entry = builder.create_block("entry");
            let vals = builder.append_entry_params(entry, f);
            let v0 = vals[0];

            // a(i32 %5):
            let a = builder.create_block("a");
            let v5 = builder.append_block_param(a, Type::i32(), f);

            // b(i32 %7, i32 %8):
            let b = builder.create_block("b");
            let v7 = builder.append_block_param(b, Type::i32(), f);
            let v8 = builder.append_block_param(b, Type::i32(), f);

            // c(i64 %12):
            let c = builder.create_block("c");
            let v12 = builder.append_block_param(c, Type::i64(), f);

            // %1 = trunc i32, %0
            // %2 = iconst i32 275
            // %3 = iconst i64 42
            // %4 = icmp eq i64 %0, %3
            // condbr bool %0, a(i32 %1), b(i32 %1, i32 %2)
            builder.switch_to(entry);
            let v1 = builder.append().trunc(Type::i32(), v0, f);
            let v2 = builder.append().iconst(Type::i32(), 275, f);
            let v3 = builder.append().iconst(Type::i64(), 42, f);
            let v4 = builder.append().icmp_eq(v0, v3, f);

            let if_true = BlockWithParams::new(a, &[v1]);
            let if_false = BlockWithParams::new(b, &[v1, v2]);

            builder.append().condbr(v4, if_true, if_false, f);

            // %6 = sext i64, i32 %5
            // br c(i64 %6)
            builder.switch_to(a);
            let v6 = builder.append().sext(Type::i64(), v5, f);
            let target = BlockWithParams::new(c, &[v6]);
            builder.append().br(target, f);

            // %9 = xor i32 %7, %8
            // %10 = imul i32 %9, %2
            // %11 = zext i64, i32 %10
            // br c(i64 %11)
            builder.switch_to(b);
            let v9 = builder.append().xor(v7, v8, f);
            let v10 = builder.append().imul(v9, v2, f);
            let v11 = builder.append().zext(Type::i64(), v10, f);
            let target = BlockWithParams::new(c, &[v11]);
            builder.append().br(target, f);

            // ret i64 %12
            builder.switch_to(c);
            builder.append().ret_val(v12, f);

            // }
            let _ = builder.define();
        }

        let expected = r#"fn i64 @magic(i64) {
entry(i64 %0):
  %1 = trunc i32, i64 %0
  %2 = iconst i32 275
  %3 = iconst i64 42
  %4 = icmp eq i64 %0, %3
  condbr bool %4, a(i32 %1), b(i32 %1, i32 %2)

a(i32 %5):
  %6 = sext i64, i32 %5
  br c(i64 %6)

b(i32 %7, i32 %8):
  %9 = xor i32 %7, %8
  %10 = imul i32 %9, %2
  %11 = zext i64, i32 %10
  br c(i64 %11)

c(i64 %12):
  ret i64 %12
}
"#;

        assert_eq!(ModuleWriter::from(&module).module(), expected);
    }

    #[test]
    fn test_write_multiple_functions_valid() {
        let mut module = Module::new("test");
        let f = DebugInfo::fake();

        let sig1 = SigBuilder::new()
            .ret(Some(Type::i32()))
            .params(&[Type::i32()])
            .build();

        let sig2 = SigBuilder::new()
            .ret(Some(Type::i32()))
            .params(&[Type::i32(), Type::i32()])
            .build();

        {
            // fn i32 @mul_by_42(i32) {
            let mut builder = module.define_function("mul_by_42", sig1);

            // entry(i32 %0):
            let entry = builder.create_block("entry");
            builder.append_entry_params(entry, f);
            builder.switch_to(entry);

            // %1 = iconst i32 42
            // %2 = imul i32 %0, %1
            // ret i32 %2
            let v0 = builder.block_params(entry)[0];
            let v1 = builder.append().iconst(Type::i32(), 42, f);
            let v2 = builder.append().imul(v0, v1, f);
            builder.append().ret_val(v2, f);

            // }
            let _ = builder.define();
        }

        {
            // fn i32 @add(i32, i32) {
            let mut builder = module.define_function("add", sig2);

            // entry(i32 %0, i32 %1):
            let entry = builder.create_block("entry");
            let params = builder.append_entry_params(entry, f);
            builder.switch_to(entry);

            // %2 = iadd i32 %0, %1
            // ret i32 %2
            let (v0, v1) = (params[0], params[1]);
            let v2 = builder.append().iadd(v0, v1, f);
            builder.append().ret_val(v2, f);

            // }
            let _ = builder.define();
        }

        let expected = r#"fn i32 @mul_by_42(i32) {
entry(i32 %0):
  %1 = iconst i32 42
  %2 = imul i32 %0, %1
  ret i32 %2
}

fn i32 @add(i32, i32) {
entry(i32 %0, i32 %1):
  %2 = iadd i32 %0, %1
  ret i32 %2
}
"#;

        assert_eq!(ModuleWriter::from(&module).module(), expected);
    }

    #[test]
    fn test_write_calls() {
        let mut module = Module::new("test");
        let puts_sig = SigBuilder::new()
            .ret(Some(Type::i32()))
            .params(&[Type::ptr()])
            .build();

        let puts = module.declare_function("puts", puts_sig.clone());

        {
            // fn i32 @puts_wrapper(ptr) {
            let mut builder = module.define_function("puts_wrapper", puts_sig.clone());

            // entry(ptr %0):
            let entry = builder.create_block("entry");
            let params = builder.append_entry_params(entry, DebugInfo::fake());
            let v0 = params[0];

            // %1 = call i32 @puts(ptr %0)
            // ret i32 %1
            builder.switch_to(entry);
            let sig = builder.import_signature(&puts_sig);
            let call = builder.append().call(puts, sig, &[v0], DebugInfo::fake());
            let v1 = builder.inst_to_result(call).unwrap();
            builder.append().ret_val(v1, DebugInfo::fake());

            // }
            let _ = builder.define();
        }

        let expected = r#"fn i32 @puts(ptr)

fn i32 @puts_wrapper(ptr) {
entry(ptr %0):
  %1 = call i32 @puts(ptr %0)
  ret i32 %1
}
"#;

        assert_eq!(ModuleWriter::from(&module).module(), expected);
    }
}
