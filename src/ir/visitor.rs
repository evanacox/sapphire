//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::ir::*;

/// Trait that allows configurable and simple SIR visiting.
///
/// This trait is for use when basically anything in the IR
/// needs to be matched somehow, when there are a few very specific
/// patterns that need to be matched this is not the right API.
pub trait SIRVisitor<'a> {
    /// Gets the module being visited.
    fn module(&self) -> &'a Module;

    /// Dispatcher that does the default walking behavior to every function in the module
    fn dispatch_funcs(&mut self) {
        for func in self.module().functions() {
            self.visit_func(func);
        }
    }

    /// Walks over the module and calls the expected `visit_*` methods
    fn walk(&mut self) {
        self.dispatch_funcs();
    }

    /// Dispatcher that does the default walking behavior, going to every block in
    /// program order.
    fn dispatch_blocks(&mut self, def: &FunctionDefinition) {
        for block in def.layout.blocks() {
            self.visit_block(block, def);
        }
    }

    /// Called whenever an individual function is visited.
    fn visit_func(&mut self, func: Func) {
        let def = match self.module().function(func).definition() {
            Some(def) => def,
            None => return,
        };

        self.dispatch_blocks(def);
    }

    /// Dispatcher that does the default behavior of visiting every instruction
    /// in a given block in program order.
    fn dispatch_insts(&mut self, block: Block, def: &FunctionDefinition) {
        for inst in def.layout.insts_in_block(block) {
            self.visit_inst(inst, def);
        }
    }

    /// Called whenever an individual block is visited.
    fn visit_block(&mut self, block: Block, def: &FunctionDefinition) {
        self.dispatch_insts(block, def);
    }

    /// Dispatcher that does the default behavior of calling the most specific visitor
    /// for each instruction.
    fn dispatch_inst(&mut self, inst: Inst, data: &InstData, def: &FunctionDefinition) {
        match data {
            InstData::Call(i) => self.visit_call(inst, i, def),
            InstData::IndirectCall(i) => self.visit_indirectcall(inst, i, def),
            InstData::ICmp(i) => self.visit_icmp(inst, i, def),
            InstData::FCmp(i) => self.visit_fcmp(inst, i, def),
            InstData::Sel(i) => self.visit_sel(inst, i, def),
            InstData::Br(i) => self.visit_br(inst, i, def),
            InstData::CondBr(i) => self.visit_condbr(inst, i, def),
            InstData::Unreachable(i) => self.visit_unreachable(inst, i, def),
            InstData::Ret(i) => self.visit_ret(inst, i, def),
            InstData::And(i) => self.visit_and(inst, i, def),
            InstData::Or(i) => self.visit_or(inst, i, def),
            InstData::Xor(i) => self.visit_xor(inst, i, def),
            InstData::Shl(i) => self.visit_shl(inst, i, def),
            InstData::AShr(i) => self.visit_ashr(inst, i, def),
            InstData::LShr(i) => self.visit_lshr(inst, i, def),
            InstData::IAdd(i) => self.visit_iadd(inst, i, def),
            InstData::ISub(i) => self.visit_isub(inst, i, def),
            InstData::IMul(i) => self.visit_imul(inst, i, def),
            InstData::SDiv(i) => self.visit_sdiv(inst, i, def),
            InstData::UDiv(i) => self.visit_udiv(inst, i, def),
            InstData::SRem(i) => self.visit_srem(inst, i, def),
            InstData::URem(i) => self.visit_urem(inst, i, def),
            InstData::FNeg(i) => self.visit_fneg(inst, i, def),
            InstData::FAdd(i) => self.visit_fadd(inst, i, def),
            InstData::FSub(i) => self.visit_fsub(inst, i, def),
            InstData::FMul(i) => self.visit_fmul(inst, i, def),
            InstData::FDiv(i) => self.visit_fdiv(inst, i, def),
            InstData::FRem(i) => self.visit_frem(inst, i, def),
            InstData::Alloca(i) => self.visit_alloca(inst, i, def),
            InstData::Load(i) => self.visit_load(inst, i, def),
            InstData::Store(i) => self.visit_store(inst, i, def),
            InstData::Offset(i) => self.visit_offset(inst, i, def),
            InstData::Extract(i) => self.visit_extract(inst, i, def),
            InstData::Insert(i) => self.visit_insert(inst, i, def),
            InstData::ElemPtr(i) => self.visit_elemptr(inst, i, def),
            InstData::Sext(i) => self.visit_sext(inst, i, def),
            InstData::Zext(i) => self.visit_zext(inst, i, def),
            InstData::Trunc(i) => self.visit_trunc(inst, i, def),
            InstData::IToB(i) => self.visit_itob(inst, i, def),
            InstData::BToI(i) => self.visit_btoi(inst, i, def),
            InstData::SIToF(i) => self.visit_sitof(inst, i, def),
            InstData::UIToF(i) => self.visit_uitof(inst, i, def),
            InstData::FToSI(i) => self.visit_ftosi(inst, i, def),
            InstData::FToUI(i) => self.visit_ftoui(inst, i, def),
            InstData::FExt(i) => self.visit_fext(inst, i, def),
            InstData::FTrunc(i) => self.visit_ftrunc(inst, i, def),
            InstData::IToP(i) => self.visit_itop(inst, i, def),
            InstData::PToI(i) => self.visit_ptoi(inst, i, def),
            InstData::IConst(i) => self.visit_iconst(inst, i, def),
            InstData::FConst(i) => self.visit_fconst(inst, i, def),
            InstData::BConst(i) => self.visit_bconst(inst, i, def),
            InstData::Undef(i) => self.visit_undef(inst, i, def),
            InstData::Null(i) => self.visit_null(inst, i, def),
            InstData::GlobalAddr(i) => self.visit_globaladdr(inst, i, def),
        }
    }

    /// Called whenever an individual instruction is visited.
    fn visit_inst(&mut self, inst: Inst, def: &FunctionDefinition) {
        self.dispatch_inst(inst, def.dfg.data(inst), def)
    }

    /// Visits a `call` instruction.
    fn visit_call(&mut self, inst: Inst, data: &CallInst, def: &FunctionDefinition);

    /// Visits an `indirectcall` instruction.
    fn visit_indirectcall(&mut self, inst: Inst, data: &IndirectCallInst, def: &FunctionDefinition);

    /// Visits an `icmp` instruction.
    fn visit_icmp(&mut self, inst: Inst, data: &ICmpInst, def: &FunctionDefinition);

    /// Visits an `fcmp` instruction.
    fn visit_fcmp(&mut self, inst: Inst, data: &FCmpInst, def: &FunctionDefinition);

    /// Visits a `sel` instruction.
    fn visit_sel(&mut self, inst: Inst, data: &SelInst, def: &FunctionDefinition);

    /// Visits a `br` instruction.
    fn visit_br(&mut self, inst: Inst, data: &BrInst, def: &FunctionDefinition);

    /// Visits a `condbr` instruction.
    fn visit_condbr(&mut self, inst: Inst, data: &CondBrInst, def: &FunctionDefinition);

    /// Visits an `unreachable` instruction.
    fn visit_unreachable(&mut self, inst: Inst, data: &UnreachableInst, def: &FunctionDefinition);

    /// Visits a `ret` instruction.
    fn visit_ret(&mut self, inst: Inst, data: &RetInst, def: &FunctionDefinition);

    /// Visits an `and` instruction.
    fn visit_and(&mut self, inst: Inst, data: &CommutativeArithInst, def: &FunctionDefinition);

    /// Visits an `or` instruction.
    fn visit_or(&mut self, inst: Inst, data: &CommutativeArithInst, def: &FunctionDefinition);

    /// Visits an `xor` instruction.
    fn visit_xor(&mut self, inst: Inst, data: &CommutativeArithInst, def: &FunctionDefinition);

    /// Visits a `shl` instruction.
    fn visit_shl(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition);

    /// Visits an `ashr` instruction.
    fn visit_ashr(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition);

    /// Visits a `lshr` instruction.
    fn visit_lshr(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition);

    /// Visits an `iadd` instruction.
    fn visit_iadd(&mut self, inst: Inst, data: &CommutativeArithInst, def: &FunctionDefinition);

    /// Visits an `isub` instruction.
    fn visit_isub(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition);

    /// Visits an `imul` instruction.
    fn visit_imul(&mut self, inst: Inst, data: &CommutativeArithInst, def: &FunctionDefinition);

    /// Visits an `sdiv` instruction.
    fn visit_sdiv(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition);

    /// Visits an `udiv` instruction.
    fn visit_udiv(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition);

    /// Visits a `srem` instruction.
    fn visit_srem(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition);

    /// Visits a `urem` instruction.
    fn visit_urem(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition);

    /// Visits an `fneg` instruction.
    fn visit_fneg(&mut self, inst: Inst, data: &FloatUnaryInst, def: &FunctionDefinition);

    /// Visits an `fadd` instruction.
    fn visit_fadd(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition);

    /// Visits an `fsub` instruction.
    fn visit_fsub(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition);

    /// Visits an `fmul` instruction.
    fn visit_fmul(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition);

    /// Visits an `fdiv` instruction.
    fn visit_fdiv(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition);

    /// Visits an `frem` instruction.
    fn visit_frem(&mut self, inst: Inst, data: &ArithInst, def: &FunctionDefinition);

    /// Visits an `alloca` instruction.
    fn visit_alloca(&mut self, inst: Inst, data: &AllocaInst, def: &FunctionDefinition);

    /// Visits a `load` instruction.
    fn visit_load(&mut self, inst: Inst, data: &LoadInst, def: &FunctionDefinition);

    /// Visits a `store` instruction.
    fn visit_store(&mut self, inst: Inst, data: &StoreInst, def: &FunctionDefinition);

    /// Visits an `offset` instruction.
    fn visit_offset(&mut self, inst: Inst, data: &OffsetInst, def: &FunctionDefinition);

    /// Visits an `extract` instruction.
    fn visit_extract(&mut self, inst: Inst, data: &ExtractInst, def: &FunctionDefinition);

    /// Visits an `insert` instruction.
    fn visit_insert(&mut self, inst: Inst, data: &InsertInst, def: &FunctionDefinition);

    /// Visits an `elemptr` instruction.
    fn visit_elemptr(&mut self, inst: Inst, data: &ElemPtrInst, def: &FunctionDefinition);

    /// Visits a `sext` instruction.
    fn visit_sext(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition);

    /// Visits a `zext` instruction.
    fn visit_zext(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition);

    /// Visits a `trunc` instruction.
    fn visit_trunc(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition);

    /// Visits an `itob` instruction.
    fn visit_itob(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition);

    /// Visits a `btoi` instruction.
    fn visit_btoi(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition);

    /// Visits a `sitof` instruction.
    fn visit_sitof(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition);

    /// Visits a `uitof` instruction.
    fn visit_uitof(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition);

    /// Visits an `ftosi` instruction.
    fn visit_ftosi(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition);

    /// Visits an `ftoui` instruction.
    fn visit_ftoui(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition);

    /// Visits an `fext` instruction.
    fn visit_fext(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition);

    /// Visits an `ftrunc` instruction.
    fn visit_ftrunc(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition);

    /// Visits an `itop` instruction.
    fn visit_itop(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition);

    /// Visits a `ptoi` instruction.
    fn visit_ptoi(&mut self, inst: Inst, data: &CastInst, def: &FunctionDefinition);

    /// Visits an `iconst` instruction.
    fn visit_iconst(&mut self, inst: Inst, data: &IConstInst, def: &FunctionDefinition);

    /// Visits an `fconst` instruction.
    fn visit_fconst(&mut self, inst: Inst, data: &FConstInst, def: &FunctionDefinition);

    /// Visits a `bconst` instruction.
    fn visit_bconst(&mut self, inst: Inst, data: &BConstInst, def: &FunctionDefinition);

    /// Visits an `undef` instruction.
    fn visit_undef(&mut self, inst: Inst, data: &UndefConstInst, def: &FunctionDefinition);

    /// Visits a `null` instruction.
    fn visit_null(&mut self, inst: Inst, data: &NullConstInst, def: &FunctionDefinition);

    /// Visits a `globaladdr` instruction.
    fn visit_globaladdr(&mut self, inst: Inst, data: &GlobalAddrInst, def: &FunctionDefinition);
}

/// A trait for a generic "visit an instruction" type. This is the smallest-scale
/// visitor, as this visitor isn't even aware of the function that a given instruction
/// is in.
pub trait GenericInstVisitor<T> {
    /// Dispatcher that does the default behavior of calling the most specific visitor
    /// for each instruction.
    fn dispatch_inst(&mut self, data: &InstData) -> T {
        match data {
            InstData::Call(i) => self.visit_call(i),
            InstData::IndirectCall(i) => self.visit_indirectcall(i),
            InstData::ICmp(i) => self.visit_icmp(i),
            InstData::FCmp(i) => self.visit_fcmp(i),
            InstData::Sel(i) => self.visit_sel(i),
            InstData::Br(i) => self.visit_br(i),
            InstData::CondBr(i) => self.visit_condbr(i),
            InstData::Unreachable(i) => self.visit_unreachable(i),
            InstData::Ret(i) => self.visit_ret(i),
            InstData::And(i) => self.visit_and(i),
            InstData::Or(i) => self.visit_or(i),
            InstData::Xor(i) => self.visit_xor(i),
            InstData::Shl(i) => self.visit_shl(i),
            InstData::AShr(i) => self.visit_ashr(i),
            InstData::LShr(i) => self.visit_lshr(i),
            InstData::IAdd(i) => self.visit_iadd(i),
            InstData::ISub(i) => self.visit_isub(i),
            InstData::IMul(i) => self.visit_imul(i),
            InstData::SDiv(i) => self.visit_sdiv(i),
            InstData::UDiv(i) => self.visit_udiv(i),
            InstData::SRem(i) => self.visit_srem(i),
            InstData::URem(i) => self.visit_urem(i),
            InstData::FNeg(i) => self.visit_fneg(i),
            InstData::FAdd(i) => self.visit_fadd(i),
            InstData::FSub(i) => self.visit_fsub(i),
            InstData::FMul(i) => self.visit_fmul(i),
            InstData::FDiv(i) => self.visit_fdiv(i),
            InstData::FRem(i) => self.visit_frem(i),
            InstData::Alloca(i) => self.visit_alloca(i),
            InstData::Load(i) => self.visit_load(i),
            InstData::Store(i) => self.visit_store(i),
            InstData::Offset(i) => self.visit_offset(i),
            InstData::Extract(i) => self.visit_extract(i),
            InstData::Insert(i) => self.visit_insert(i),
            InstData::ElemPtr(i) => self.visit_elemptr(i),
            InstData::Sext(i) => self.visit_sext(i),
            InstData::Zext(i) => self.visit_zext(i),
            InstData::Trunc(i) => self.visit_trunc(i),
            InstData::IToB(i) => self.visit_itob(i),
            InstData::BToI(i) => self.visit_btoi(i),
            InstData::SIToF(i) => self.visit_sitof(i),
            InstData::UIToF(i) => self.visit_uitof(i),
            InstData::FToSI(i) => self.visit_ftosi(i),
            InstData::FToUI(i) => self.visit_ftoui(i),
            InstData::FExt(i) => self.visit_fext(i),
            InstData::FTrunc(i) => self.visit_ftrunc(i),
            InstData::IToP(i) => self.visit_itop(i),
            InstData::PToI(i) => self.visit_ptoi(i),
            InstData::IConst(i) => self.visit_iconst(i),
            InstData::FConst(i) => self.visit_fconst(i),
            InstData::BConst(i) => self.visit_bconst(i),
            InstData::Undef(i) => self.visit_undef(i),
            InstData::Null(i) => self.visit_null(i),
            InstData::GlobalAddr(i) => self.visit_globaladdr(i),
        }
    }

    /// Visits a `call` instruction.
    fn visit_call(&mut self, data: &CallInst) -> T;

    /// Visits an `indirectcall` instruction.
    fn visit_indirectcall(&mut self, data: &IndirectCallInst) -> T;

    /// Visits an `icmp` instruction.
    fn visit_icmp(&mut self, data: &ICmpInst) -> T;

    /// Visits an `fcmp` instruction.
    fn visit_fcmp(&mut self, data: &FCmpInst) -> T;

    /// Visits a `sel` instruction.
    fn visit_sel(&mut self, data: &SelInst) -> T;

    /// Visits a `br` instruction.
    fn visit_br(&mut self, data: &BrInst) -> T;

    /// Visits a `condbr` instruction.
    fn visit_condbr(&mut self, data: &CondBrInst) -> T;

    /// Visits an `unreachable` instruction.
    fn visit_unreachable(&mut self, data: &UnreachableInst) -> T;

    /// Visits a `ret` instruction.
    fn visit_ret(&mut self, data: &RetInst) -> T;

    /// Visits an `and` instruction.
    fn visit_and(&mut self, data: &CommutativeArithInst) -> T;

    /// Visits an `or` instruction.
    fn visit_or(&mut self, data: &CommutativeArithInst) -> T;

    /// Visits an `xor` instruction.
    fn visit_xor(&mut self, data: &CommutativeArithInst) -> T;

    /// Visits a `shl` instruction.
    fn visit_shl(&mut self, data: &ArithInst) -> T;

    /// Visits an `ashr` instruction.
    fn visit_ashr(&mut self, data: &ArithInst) -> T;

    /// Visits a `lshr` instruction.
    fn visit_lshr(&mut self, data: &ArithInst) -> T;

    /// Visits an `iadd` instruction.
    fn visit_iadd(&mut self, data: &CommutativeArithInst) -> T;

    /// Visits an `isub` instruction.
    fn visit_isub(&mut self, data: &ArithInst) -> T;

    /// Visits an `imul` instruction.
    fn visit_imul(&mut self, data: &CommutativeArithInst) -> T;

    /// Visits an `sdiv` instruction.
    fn visit_sdiv(&mut self, data: &ArithInst) -> T;

    /// Visits an `udiv` instruction.
    fn visit_udiv(&mut self, data: &ArithInst) -> T;

    /// Visits a `srem` instruction.
    fn visit_srem(&mut self, data: &ArithInst) -> T;

    /// Visits a `urem` instruction.
    fn visit_urem(&mut self, data: &ArithInst) -> T;

    /// Visits an `fneg` instruction.
    fn visit_fneg(&mut self, data: &FloatUnaryInst) -> T;

    /// Visits an `fadd` instruction.
    fn visit_fadd(&mut self, data: &ArithInst) -> T;

    /// Visits an `fsub` instruction.
    fn visit_fsub(&mut self, data: &ArithInst) -> T;

    /// Visits an `fmul` instruction.
    fn visit_fmul(&mut self, data: &ArithInst) -> T;

    /// Visits an `fdiv` instruction.
    fn visit_fdiv(&mut self, data: &ArithInst) -> T;

    /// Visits an `frem` instruction.
    fn visit_frem(&mut self, data: &ArithInst) -> T;

    /// Visits an `alloca` instruction.
    fn visit_alloca(&mut self, data: &AllocaInst) -> T;

    /// Visits a `load` instruction.
    fn visit_load(&mut self, data: &LoadInst) -> T;

    /// Visits a `store` instruction.
    fn visit_store(&mut self, data: &StoreInst) -> T;

    /// Visits an `offset` instruction.
    fn visit_offset(&mut self, data: &OffsetInst) -> T;

    /// Visits an `extract` instruction.
    fn visit_extract(&mut self, data: &ExtractInst) -> T;

    /// Visits an `insert` instruction.
    fn visit_insert(&mut self, data: &InsertInst) -> T;

    /// Visits an `elemptr` instruction.
    fn visit_elemptr(&mut self, data: &ElemPtrInst) -> T;

    /// Visits a `sext` instruction.
    fn visit_sext(&mut self, data: &CastInst) -> T;

    /// Visits a `zext` instruction.
    fn visit_zext(&mut self, data: &CastInst) -> T;

    /// Visits a `trunc` instruction.
    fn visit_trunc(&mut self, data: &CastInst) -> T;

    /// Visits an `itob` instruction.
    fn visit_itob(&mut self, data: &CastInst) -> T;

    /// Visits a `btoi` instruction.
    fn visit_btoi(&mut self, data: &CastInst) -> T;

    /// Visits a `sitof` instruction.
    fn visit_sitof(&mut self, data: &CastInst) -> T;

    /// Visits a `uitof` instruction.
    fn visit_uitof(&mut self, data: &CastInst) -> T;

    /// Visits an `ftosi` instruction.
    fn visit_ftosi(&mut self, data: &CastInst) -> T;

    /// Visits an `ftoui` instruction.
    fn visit_ftoui(&mut self, data: &CastInst) -> T;

    /// Visits an `fext` instruction.
    fn visit_fext(&mut self, data: &CastInst) -> T;

    /// Visits an `ftrunc` instruction.
    fn visit_ftrunc(&mut self, data: &CastInst) -> T;

    /// Visits an `itop` instruction.
    fn visit_itop(&mut self, data: &CastInst) -> T;

    /// Visits a `ptoi` instruction.
    fn visit_ptoi(&mut self, data: &CastInst) -> T;

    /// Visits an `iconst` instruction.
    fn visit_iconst(&mut self, data: &IConstInst) -> T;

    /// Visits an `fconst` instruction.
    fn visit_fconst(&mut self, data: &FConstInst) -> T;

    /// Visits a `bconst` instruction.
    fn visit_bconst(&mut self, data: &BConstInst) -> T;

    /// Visits an `undef` instruction.
    fn visit_undef(&mut self, data: &UndefConstInst) -> T;

    /// Visits a `null` instruction.
    fn visit_null(&mut self, data: &NullConstInst) -> T;

    /// Visits a `globaladdr` instruction.
    fn visit_globaladdr(&mut self, data: &GlobalAddrInst) -> T;
}

/// Trait that allows configurable visiting of a single function with a [`CursorMut`].
///
/// This trait is the alternative to [`SIRVisitor`], this is more useful for function
/// transformations that need to be able to modify the IR while visiting.
pub trait FunctionCursorVisitor<'a, T, C: CursorMut>: Sized + GenericInstVisitor<T> {
    /// Gets the module being visited.
    fn cursor(&mut self) -> &mut C;

    /// Yields the "result" of the visit, if any exists.
    fn result(self) -> T;

    /// Walks over the module and calls the expected `visit_*` methods
    fn walk(mut self) -> T {
        self.dispatch_blocks();

        self.result()
    }

    /// Dispatcher that does the default walking behavior, going to every block in
    /// program order.
    ///
    /// The cursor will be moved to different blocks but this.
    fn dispatch_blocks(&mut self) {
        while let Some(bb) = self.cursor().next_block() {
            self.visit_block(bb);
        }
    }

    /// Dispatcher that does the default behavior of iterating over every
    /// instruction in a given block in program order.
    fn dispatch_insts(&mut self, block: Block) {
        self.cursor().goto_before(block);

        while let Some(inst) = self.cursor().next_inst() {
            let _ = self.visit_inst(inst);
        }
    }

    /// Called whenever an individual block is visited
    fn visit_block(&mut self, block: Block) {
        self.dispatch_insts(block);
    }

    /// Called whenever an individual instruction is visited.
    fn visit_inst(&mut self, inst: Inst) -> T {
        let data = self.cursor().dfg().data(inst).clone();

        self.dispatch_inst(&data)
    }
}
