//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::arena::{ArenaMap, SecondaryMap};
use crate::codegen::{
    Architecture, FixedIntervals, PReg, Reg, StackFrame, VariableLocation, WriteableReg,
};
use crate::dense_arena_key;
use crate::ir::Type;
use crate::utility::{Packable, Str, StringPool};
use smallvec::SmallVec;
use std::fmt::Debug;
use std::hash::Hash;
use std::ops::Range;

/// An abstract representation of a `mov` between two registers
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct RegToRegCopy {
    /// The width (in bytes) of the copy
    pub width: usize,
    /// The destination of the copy
    pub to: WriteableReg,
    /// The source of the copy
    pub from: Reg,
}

/// A collector that can have registers added to it.
///
/// Each register has an associated size (in bytes) that are being used
/// out of it, this is to minimize stack usage
pub type RegCollector<const N: usize> = SmallVec<[(Reg, u32); N]>;

/// Defines the API for a machine instruction.
///
/// Each specific target has a unique set of possible [`MachInst`]s (this is
/// what makes up the unique "MIR" (machine instruction representation) for
/// that target), but they all provide the same basic operations. This enables
/// cross-target code sharing for things like instruction scheduling and
/// register allocation.
pub trait MachInst: Copy + Debug + Hash + Sized {
    /// The related architecture type that defines the architecture
    /// this specific MIR type targets
    type Arch: Architecture;

    /// Pushes every register being used by `self` into `collector`.
    ///
    /// It can be assumed that if the live ranges of these end at this
    /// instruction that they can be used as the destination.
    fn uses<const N: usize>(
        &self,
        frame: &dyn StackFrame<Self::Arch>,
        collector: &mut RegCollector<N>,
    );

    /// Pushes every register being defined by `self` into `collector`.
    fn defs<const N: usize>(
        &self,
        frame: &dyn StackFrame<Self::Arch>,
        collector: &mut RegCollector<N>,
    );

    /// Checks if the instruction is a copy between two registers.
    #[inline]
    fn is_copy(&self) -> bool {
        self.as_copy().is_some()
    }

    /// Checks if the instruction is a copy from the same register being copied to.
    ///
    /// These `%r <- %r` copies are useless and are able to be removed by the rewriter.
    #[inline]
    fn is_nop_copy(&self) -> bool {
        self.as_copy()
            .is_some_and(|copy| copy.to.to_reg() == copy.from)
    }

    /// Returns `self` as a [`RegToRegCopy`] if `self` is a register-to-register copy.
    fn as_copy(&self) -> Option<RegToRegCopy>;

    /// Creates a target-specific copy instruction that copies a value of `width` bytes
    /// between two registers.
    ///
    /// This must return an object where [`Self::is_copy`] returns `true`.
    fn copy(width: usize, src: Reg, dest: WriteableReg) -> Self;

    /// Creates an instruction that loads `from` into `to`.
    fn load(width: usize, from: VariableLocation, to: PReg) -> Self;

    /// Creates an instruction that stores `from` into `to`.
    fn store(width: usize, from: PReg, to: VariableLocation) -> Self;

    /// Checks if the instruction is a return instruction
    fn is_ret(&self) -> bool;

    /// Rewrites an instruction to change all `Reg` references into `PReg`s.
    fn rewrite(self, rewrites: &[(Reg, PReg)]) -> Self;
}

dense_arena_key! {
    /// A reference to a single block of MIR.
    pub struct MIRBlock;
}

/// The different types of external entities that MIR can reference. This is
/// here for emitting purposes, so the symbols that the linker needs to
/// resolve can be listed.
#[repr(u32)]
#[derive(Clone, Copy)]
pub enum Extern {
    /// A function/procedure
    Function,
    /// An object of a specific type
    Object(Type),
}

/// Holds a [`MIRFunction`] along with the associated stack frame information for it.
pub type FuncFramePair<Inst> = (
    MIRFunction<Inst>,
    Box<dyn StackFrame<<Inst as MachInst>::Arch>>,
);

/// Equivalent of a [`Module`](crate::ir::Module) for MIR.
///
/// This simply holds a list of [`MachInst`]s. A [`MIRModule`] may or may not
/// have been register allocated yet, but all instructions are guaranteed to
/// be valid for the target (besides potentially using virtual registers
/// instead of physical ones).  
pub struct MIRModule<Inst: MachInst> {
    symbols: StringPool,
    externals: Vec<(Str, Extern)>,
    functions: Vec<FuncFramePair<Inst>>,
}

impl<Inst: MachInst> MIRModule<Inst> {
    /// Creates a "module" of MIR.
    ///
    /// This requires providing the symbol pool used by all the MIR, a list of external
    /// entities that are used (e.g. external functions)
    pub fn new(
        symbols: StringPool,
        externals: Vec<(Str, Extern)>,
        functions: Vec<FuncFramePair<Inst>>,
    ) -> Self {
        Self {
            symbols,
            externals,
            functions,
        }
    }

    /// Returns all the functions that are in the module, along with their associated frame info
    pub fn functions(&self) -> &[FuncFramePair<Inst>] {
        &self.functions
    }

    /// Returns a mutable reference to all the functions in the module
    pub fn functions_mut(&mut self) -> &mut [FuncFramePair<Inst>] {
        &mut self.functions
    }

    /// Gets all the symbols in the module
    pub fn symbols(&self) -> &StringPool {
        &self.symbols
    }

    /// Gets the list of external symbols referenced in the module
    pub fn externals(&self) -> &[(Str, Extern)] {
        &self.externals
    }
}

/// Defines a "block" in MIR. This is just a range that maps to a sublist in
/// the overall list of instructions in a function.
///
/// The semantic model of this is that it's a half-open interval of
/// the form `[begin, end)`.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct MIRBlockInterval(u32, u32);

impl MIRBlockInterval {
    /// Creates a new [`MIRBlockInterval`].
    pub fn from_indices(begin: u32, end: u32) -> Self {
        Self(begin, end)
    }

    fn as_range(self) -> Range<usize> {
        debug_assert!(!self.is_reserved());

        (self.0 as usize)..(self.1 as usize)
    }
}

impl Packable for MIRBlockInterval {
    fn reserved() -> Self {
        Self(!0, !0)
    }

    fn is_reserved(&self) -> bool {
        self.0 == !0 && self.1 == !0
    }
}

/// A single function in MIR.
///
/// This is a slightly more abstract way of representing the following:
///
/// ```asm
/// function_name:
///   mov ...
///
/// .bb1:
///   add ...
///
/// .bb2:
///   ...  
///
/// .bb3:
///   ...
///   ret
/// ```
///
/// At its core, this is a single linear sequence of MIR, divided into "blocks"
/// that will later be translated into assembly labels / offsets.
///
/// "Blocks" are defined as a sublist of the full list of instructions, they are
/// represented as intervals of indices for the overall list.
pub struct MIRFunction<Inst: MachInst> {
    name: Str,
    insts: Vec<Inst>,
    order: Vec<MIRBlock>,
    fixed: FixedIntervals,
    blocks: ArenaMap<MIRBlock, MIRBlockInterval>,
}

impl<Inst: MachInst> MIRFunction<Inst> {
    pub(in crate::codegen) fn new(
        name: Str,
        insts: Vec<Inst>,
        blocks: ArenaMap<MIRBlock, MIRBlockInterval>,
        order: Vec<MIRBlock>,
        fixed: FixedIntervals,
    ) -> Self {
        Self {
            name,
            insts,
            blocks,
            order,
            fixed,
        }
    }

    /// Returns the list of MIR blocks in the function.
    ///
    /// This is not necessarily in program order, program order is determined
    /// by [`Self::program_order`].
    pub fn blocks(&self) -> impl Iterator<Item = (MIRBlock, MIRBlockInterval)> + '_ {
        self.blocks.iter().map(|(k, v)| (k, *v))
    }

    /// Gets the sequence of instructions that make up a single block.
    #[inline]
    pub fn block(&self, key: MIRBlock) -> &[Inst] {
        &self.insts[self.blocks[key].as_range()]
    }

    /// Returns the program order of the blocks, i.e. the order they need to be in when
    /// they are actually emitted to machine code.
    #[inline]
    pub fn program_order(&self) -> &[MIRBlock] {
        &self.order
    }

    /// Returns the program order of the blocks, i.e. the order they need to be in when
    /// they are actually emitted to machine code.
    ///
    /// This can be mutated, meaning the program order can be changed here. Care must
    /// be taken to ensure that an invalid order isn't created, it is assumed to be
    /// correct (and cannot be checked).
    #[inline]
    pub fn program_order_mut(&mut self) -> &mut [MIRBlock] {
        &mut self.order
    }

    /// Returns the entire function as a linear list of instructions without any control-flow info.
    ///
    /// This is here for passes like LSRA which treat the function as a linear set of instructions
    /// rather than as a CFG.
    #[inline]
    pub fn all_instructions(&self) -> &[Inst] {
        &self.insts
    }

    /// Gets a reference to the name of the function. This can be used at the `symbols`
    /// pool in the full MIR module.
    #[inline]
    pub fn name(&self) -> Str {
        self.name
    }

    /// Rewrites the function with a new list of instructions (and new intervals defining the blocks).
    pub fn rewrite_with(
        &mut self,
        new_insts: Vec<Inst>,
        new_intervals: SecondaryMap<MIRBlock, MIRBlockInterval>,
    ) {
        for (block, interval) in new_intervals {
            self.blocks[block] = interval;
        }

        self.insts = new_insts;
    }

    /// Gets the list of fixed intervals defined by the instruction selector.
    pub fn fixed_intervals(&self) -> &FixedIntervals {
        &self.fixed
    }
}
