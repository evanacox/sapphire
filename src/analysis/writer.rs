//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::arena::SecondaryMap;
use crate::ir::*;
use crate::passes::{ModuleAnalysisManager, ModuleAnalysisPass};
use crate::utility::{Str, StringPool};
use std::any::TypeId;
use std::io;
use std::ops::Range;

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

/// This is an analysis that provides a [`ModuleWriter`] to any code that wants it.
///
/// This analysis needs to be run in the standard way for a correct [`ModuleWriter`]
/// to be produced, the result yielded by the analysis can then be queried as desired.
pub struct ModuleStringifyAnalysis {}

impl ModuleAnalysisPass for ModuleStringifyAnalysis {
    type Result = ModuleWriter;

    fn expects_preserved(&self) -> &'static [TypeId] {
        &[]
    }

    fn run(&mut self, module: &Module, _: &ModuleAnalysisManager) -> Self::Result {
        ModuleWriter::from(module)
    }
}

/// This is an analysis that writes out a textual representation of a module
/// to a
///
/// This analysis needs to be run in the standard way for a correct [`ModuleWriter`]
/// to be produced, the result yielded by the analysis can then be queried as desired.
pub struct ModuleWriterAnalysis {
    out: Box<dyn io::Write>,
}

impl ModuleWriterAnalysis {
    /// Creates an instance of the pass with a given writer.
    ///
    /// This writer will be where the module is printed out when the analysis
    /// is run over the IR.
    pub fn with_writer<T: io::Write + 'static>(writer: T) -> Self {
        Self {
            out: Box::new(writer),
        }
    }
}

impl ModuleAnalysisPass for ModuleWriterAnalysis {
    type Result = ();

    fn expects_preserved(&self) -> &'static [TypeId] {
        &[]
    }

    fn run(&mut self, module: &Module, am: &ModuleAnalysisManager) -> Self::Result {
        let writer = am.get::<ModuleStringifyAnalysis>(module);

        self.out
            .write_all(writer.module().as_bytes())
            .expect("unable to write module to writer")
    }
}

pub(crate) fn stringify_ty(ctx: &TypePool, ty: Type) -> String {
    match ty.unpack() {
        UType::Bool(_) => "bool".to_owned(),
        UType::Ptr(_) => "bool".to_owned(),
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
            let mut result = "{ ".to_owned();

            for field in structure.members(ctx) {
                result += &format!("{}, ", stringify_ty(ctx, *field));
            }

            if result.ends_with(", ") {
                result.truncate(", ".len() - ", ".len());
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
            *buf += "...";
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
        CallConv::SysV => "sysv",
        CallConv::Win64 => "win64",
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
    state: ModuleWriter,
    values: SecondaryMap<Value, ValueName>,
    next: u32,
}

impl<'m> WriterImpl<'m> {
    fn ty(&self, ty: Type) -> String {
        stringify_ty(self.module.type_pool(), ty)
    }

    fn ty_void(&self, ty: Option<Type>) -> String {
        stringify_return_ty(self.module.type_pool(), ty)
    }

    fn param_tys(&self, sig: &Signature) -> String {
        stringify_signature_params(self.module.type_pool(), sig)
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
        let name = self.module().resolve_string(def.dfg.block(bb).name());

        if block.args().is_empty() {
            name.to_owned()
        } else {
            let args = self.args(block.args(), def);

            format!("{name}{args}")
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

        name.into_string(self.module().string_pool())
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
        let mut it = self.module().functions();

        // if we have any functions at all, print first one without leading \n
        if let Some(func) = it.next() {
            self.visit_func(func);
        }

        // for any remaining functions, print a newline to split them up
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

            // 'fn T @name(...) '
            self.state.whole += &format!("fn {ty} {name}{params} ");

            // '{fastcc|sysv|win64|ccc} '
            match sig.calling_conv() {
                CallConv::C => {}
                abi => self.state.whole += &format!("{} ", stringify_abi(abi)),
            }

            // body
            if let Some(def) = f.definition() {
                self.state.whole += "{\n";

                self.dispatch_blocks(def);

                // blocks print a newline after every inst, including last one
                self.state.whole += "}\n";
            }
        }

        let end = self.state.whole.len();

        self.state.func_ranges.insert(func, begin..end);
    }

    fn visit_block(&mut self, block: Block, def: &FunctionDefinition) {
        let begin = self.state.whole.len();

        {
            let bb = def.dfg.block(block);

            self.state.whole += self.module().resolve_string(bb.name());

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
        let sig = stringify_signature_params(self.module().type_pool(), signature);
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

        let ty = stringify_ty(self.module().type_pool(), def.dfg.ty(data.lhs()));
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

        let ty = stringify_ty(self.module().type_pool(), def.dfg.ty(data.lhs()));
        let lhs = self.name(data.lhs(), def);
        let rhs = self.name(data.rhs(), def);

        self.state.whole += &format!("fcmp {opc} {ty} {lhs}, {rhs}",);
    }

    fn visit_sel(&mut self, inst: Inst, data: &SelInst, def: &FunctionDefinition) {
        self.result(inst, def);

        let ty = stringify_ty(self.module().type_pool(), def.dfg.ty(data.if_true()));
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

    fn visit_fadd(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition) {
        self.arith("fadd", inst, data, def);
    }

    fn visit_fsub(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition) {
        self.arith("fsub", inst, data, def);
    }

    fn visit_fmul(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition) {
        self.arith("fmul", inst, data, def);
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
        let ptr = self.name(data.base(), def);
        let offset = self.name(data.offset(), def);

        self.state.whole += &format!("offset {ty}, {ptr}, {offset}");
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

        let ty = self.ty(data.result_ty().unwrap());
        let value = data.value();

        self.state.whole += &format!("iconst {ty} {value}");
    }

    fn visit_fconst(&mut self, inst: Inst, data: &FConstInst, def: &FunctionDefinition) {
        self.result(inst, def);

        let ty = self.ty(data.result_ty().unwrap());
        let value = data.value();

        self.state.whole += &format!("fconst {ty} 0xfp{value:020X}");
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
