//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::arena::ArenaMap;
use crate::codegen::{Architecture, Reg, WriteableReg, ABI};
use crate::dense_arena_key;
use crate::ir::Type;
use crate::utility::{Packable, Str, StringPool};
use smallvec::SmallVec;
use std::fmt::Debug;
use std::marker::PhantomData;
use std::ops::Range;

/// An abstract representation of a `mov` between two registers
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct Move {
    /// The width (in bytes) of the copy
    pub width: usize,
    /// The destination of the copy
    pub to: WriteableReg,
    /// The source of the copy
    pub from: Reg,
}

/// A collector that can have registers added to it.
pub type RegCollector<const N: usize> = SmallVec<[Reg; N]>;

/// Defines the API for a machine instruction.
///
/// Each specific target has a unique set of possible [`MachInst`]s (this is
/// what makes up the unique "MIR" (machine instruction representation) for
/// that target), but they all provide the same basic operations. This enables
/// cross-target code sharing for things like instruction scheduling and
/// register allocation.
pub trait MachInst<Arch: Architecture>: Copy + Debug + Sized {
    /// Pushes every register being used by `self` into `collector`.
    ///
    /// It can be assumed that if the live ranges of these end at this
    /// instruction that they can be used as the destination.
    fn uses<const N: usize, Abi: ABI<Arch, Self>>(
        &self,
        frame: &Abi::Frame,
        collector: &mut RegCollector<N>,
    );

    /// Pushes every register being defined by `self` into `collector`.
    fn defs<const N: usize, Abi: ABI<Arch, Self>>(
        &self,
        frame: &Abi::Frame,
        collector: &mut RegCollector<N>,
    );

    /// Checks if the instruction is a `mov` (or the equivalent for the
    /// target architecture) between two registers, i.e. a copy.
    ///
    /// If it is, it can be coalesced by the copy coalescing pass.
    #[inline]
    fn is_move(&self) -> bool {
        self.as_move().is_some()
    }

    /// Returns `self` as a [`Move`].
    fn as_move(self) -> Option<Move>;

    /// Creates a `mov` instruction that copies a value of `width` bytes.
    ///
    /// This must return an object where [`Self::is_move`] returns `true`.
    fn mov(width: usize, src: Reg, dest: WriteableReg) -> Self;
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

/// Equivalent of a [`Module`](crate::ir::Module) for MIR.
///
/// This simply holds a list of [`MachInst`]s. A [`MIRModule`] may or may not
/// have been register allocated yet, but all instructions are guaranteed to
/// be valid for the target (besides potentially using virtual registers
/// instead of physical ones).  
pub struct MIRModule<Arch, Abi, Inst>
where
    Arch: Architecture,
    Abi: ABI<Arch, Inst>,
    Inst: MachInst<Arch>,
{
    symbols: StringPool,
    externals: Vec<(Str, Extern)>,
    functions: Vec<(MIRFunction<Arch, Inst>, Abi::Frame)>,
}

impl<Arch, Abi, Inst> MIRModule<Arch, Abi, Inst>
where
    Arch: Architecture,
    Abi: ABI<Arch, Inst>,
    Inst: MachInst<Arch>,
{
    /// Creates a "module" of MIR.
    ///
    /// This requires providing the symbol pool used by all the MIR, a list of external
    /// entities that are used (e.g. external functions)
    pub fn new(
        symbols: StringPool,
        externals: Vec<(Str, Extern)>,
        functions: Vec<(MIRFunction<Arch, Inst>, Abi::Frame)>,
    ) -> Self {
        Self {
            symbols,
            externals,
            functions,
        }
    }

    /// Returns all the functions that are in the module, along with their associated frame info
    pub fn functions(&self) -> &[(MIRFunction<Arch, Inst>, Abi::Frame)] {
        &self.functions
    }

    /// Returns a mutable reference to all the functions in the module
    pub fn functions_mut(&mut self) -> &mut [(MIRFunction<Arch, Inst>, Abi::Frame)] {
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
pub struct MIRFunction<Arch, Inst>
where
    Arch: Architecture,
    Inst: MachInst<Arch>,
{
    name: Str,
    insts: Vec<Inst>,
    order: Vec<MIRBlock>,
    blocks: ArenaMap<MIRBlock, MIRBlockInterval>,
    _unused: PhantomData<fn() -> Arch>,
}

impl<Arch, Inst> MIRFunction<Arch, Inst>
where
    Arch: Architecture,
    Inst: MachInst<Arch>,
{
    pub(in crate::codegen) fn new(
        name: Str,
        insts: Vec<Inst>,
        blocks: ArenaMap<MIRBlock, MIRBlockInterval>,
        order: Vec<MIRBlock>,
    ) -> Self {
        Self {
            name,
            insts,
            blocks,
            order,
            _unused: PhantomData::default(),
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
}
