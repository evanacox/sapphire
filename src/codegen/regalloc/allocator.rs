//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::codegen::{
    Architecture, LiveInterval, MIRFunction, PReg, Reg, StackFrame, VariableLocation,
};
use smallvec::{smallvec, SmallVec};

macro_rules! uses {
    ($inst:expr, $fr:expr) => {{
        let mut collector = SmallVec::<[Reg; 16]>::default();
        let (integral_unavailable, float_unavailable) = $fr.registers().unavailable;

        $inst.uses($fr, &mut collector);

        // any uses of unavailable registers are ignored
        collector.retain(|reg| {
            !(reg.is_preg()
                && integral_unavailable.contains(&reg.as_preg().unwrap())
                && float_unavailable.contains(&reg.as_preg().unwrap()))
        });

        collector
    }};
}

macro_rules! defs {
    ($inst:expr, $fr:expr) => {{
        let mut collector = SmallVec::<[Reg; 16]>::default();

        $inst.defs($fr, &mut collector);

        collector
    }};
}

use crate::arena::{ArenaKey, SecondaryMap};
use crate::dense_arena_key;
pub(in crate::codegen::regalloc) use defs;
pub(in crate::codegen::regalloc) use uses;

dense_arena_key! {
    /// A single point in a MIR program.
    ///
    /// This represents an offset from the beginning of the program,
    /// with the assumption being that this points "before" that offset. Ex:
    /// a reload is set to be inserted at `ProgramPoint(0)`, this means the
    /// instruction is to be emitted *before* the instruction at offset `0`.
    pub struct ProgramPoint;
}

impl ProgramPoint {
    /// Creates a [`ProgramPoint`] that points to the location before `i`.
    #[inline]
    pub fn before(i: u32) -> Self {
        Self::key_new(i as usize)
    }

    /// Returns the index that the program point points to.
    ///
    /// Remember that `self` points to the instruction **before** the index returned.
    #[inline]
    pub fn offset_of_next(self) -> u32 {
        self.0
    }
}

/// A nice way to iterate over program points when desired.
///
/// This is intended for use with [`MIRFunction::all_instructions`]
pub struct ProgramPoints<I: Iterator> {
    inner: I,
    next: u32,
}

impl<I: Iterator> Iterator for ProgramPoints<I> {
    type Item = (ProgramPoint, I::Item);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let item = self.inner.next()?;
        let i = self.next;

        self.next += 1;

        Some((ProgramPoint(i), item))
    }
}

/// A nice way to iterate over program points when desired.
///
/// This is intended for use with [`MIRFunction::all_instructions`]
pub trait ProgramPointsIterator<T>: Iterator<Item = T> + Sized {
    /// Returns an iterator that yields program points along with items.
    ///
    /// This is intended for use with [`MIRFunction::all_instructions`]
    fn program_points(self) -> ProgramPoints<Self> {
        ProgramPoints {
            inner: self,
            next: 0,
        }
    }
}

impl<T, I: Iterator<Item = T>> ProgramPointsIterator<T> for I {}

/// Models a single spill or reload generated by the register allocator.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum SpillReload {
    /// A spill, i.e. a `*to = from`
    Spill {
        /// The physical register being spilled to the stack
        from: PReg,
        /// The stack location to spill from
        to: VariableLocation,
    },
    /// A reload, i.e. `to = *from`
    Reload {
        /// The stack location being loaded from
        from: VariableLocation,
        /// The physical register being reloaded into
        to: PReg,
    },
}

/// A list of "fixed" intervals.
///
/// These are live intervals for physical registers, and are used to create "sections"
#[derive(Clone, Debug, Default)]
pub struct FixedIntervals {
    intervals: SecondaryMap<PReg, SmallVec<[LiveInterval; 2]>>,
}

impl FixedIntervals {
    /// Adds an interval to a register's set of fixed intervals.
    #[inline]
    pub fn add_fixed_interval(&mut self, reg: PReg, interval: LiveInterval) {
        if let Some(vec) = self.intervals.get_mut(reg) {
            vec.push(interval);
            vec.sort_unstable();
        } else {
            self.intervals.insert(reg, smallvec![interval]);
        }
    }

    /// Gets the list of fixed intervals for `reg`.
    ///
    /// The list is guaranteed to be sorted in ascending order.
    #[inline]
    pub fn intervals_for(&self, reg: PReg) -> &[LiveInterval] {
        self.intervals
            .get(reg)
            .map(|vec| vec.as_slice())
            .unwrap_or(&[])
    }

    /// Allows iterating over all the fixed intervals.
    pub fn all_intervals(&self) -> impl Iterator<Item = (PReg, &[LiveInterval])> + '_ {
        self.intervals
            .iter()
            .map(|(reg, vec)| (reg, vec.as_slice()))
    }
}

/// Models mapping an instruction to the register allocation it has.
///
/// At the instruction for a given [`ProgramPoint`], each register `(Reg, PReg)`
/// pair means that the usage of `Reg` in the instruction has been allocated to `PReg`.
#[derive(Clone, Debug)]
pub struct RegisterMapping {
    mapping: Vec<SmallVec<[(Reg, PReg); 2]>>,
}

impl RegisterMapping {
    pub(in crate::codegen::regalloc) fn new() -> Self {
        Self {
            mapping: Vec::default(),
        }
    }

    #[inline]
    pub(in crate::codegen::regalloc) fn push(
        &mut self,
        pp: ProgramPoint,
        mapping: SmallVec<[(Reg, PReg); 2]>,
    ) {
        debug_assert_eq!(self.mapping.len(), pp.0 as usize);

        self.mapping.push(mapping)
    }

    /// Gets the register mapping for the instruction after `pp`.
    ///
    /// Every `Reg` is mapped to the `PReg` that it should be re-written to
    /// actually reference in the final program.
    ///
    /// Note that this does map physical registers -> the same physical register
    /// for simplicity's sake in the rewriter.
    #[inline]
    pub fn mapping_at(&self, pp: ProgramPoint) -> &[(Reg, PReg)] {
        &self.mapping[pp.0 as usize]
    }
}

/// A representation of a valid allocation for a MIR program.
pub struct Allocation {
    /// A list of spills/reloads along with the program point
    /// they are to be inserted at.
    pub spills: Vec<(ProgramPoint, SpillReload)>,
    /// For every instruction in the program, maps to a list of VReg -> PReg mappings.
    ///
    /// Note that this does map physical registers -> the same physical register
    /// for simplicity's sake in the rewriter.
    pub mapping: RegisterMapping,
}

/// Models a register allocator that works over MIR.
///
/// The input to a register allocator is expected to be non-allocated MIR
/// code (i.e. code that uses virtual registers, potentially with some
/// pre-allocated operations that are bound to specific physical registers).
///
/// The output is a (representation of) a valid register allocation for the
/// program that can be fed into the [`Rewriter`](crate::codegen::Rewriter), containing
/// a list of spills/reloads to insert, and a mapping of virtual registers
/// to physical registers..
pub trait RegisterAllocator<Arch: Architecture>: Sized {
    /// Computes a valid register allocation for the given "program" (function).
    ///
    /// If the allocator performs any spills, it tells `frame` through [`StackFrame::spill_slot`].
    fn allocate(program: &MIRFunction<Arch::Inst>, frame: &mut dyn StackFrame<Arch>) -> Allocation;
}
