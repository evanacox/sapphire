//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::dense_arena_key;
use crate::ir::{DataFlowGraph, InstData, Layout, ModuleContext, Type};
use smallvec::SmallVec;
use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign};

#[cfg(feature = "enable-serde")]
use serde::{Deserialize, Serialize};

/// Models the different attributes that can be on a given parameter.
#[repr(transparent)]
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct ParamAttributes(u32);

impl ParamAttributes {
    const NOALIAS_FLAG: u32 = 0b1000_0000_0000_0000_0000_0000_0000_0000;
    const NONNULL_FLAG: u32 = 0b0100_0000_0000_0000_0000_0000_0000_0000;
    const BYVAL_N_FLAG: u32 = 0b0010_0000_0000_0000_0000_0000_0000_0000;

    /// No parameter attributes
    pub const NONE: ParamAttributes = ParamAttributes(0);

    /// `noalias`: Only applicable to pointers. Asserts that a pointer does not
    /// alias any other pointers accessible in the program, this is meant for
    /// functions that behave in a `malloc`-like way.
    pub const NOALIAS: ParamAttributes = ParamAttributes(Self::NOALIAS_FLAG);

    /// `nonnull`: simply asserts that the pointer is not `null`.
    pub const NONNULL: ParamAttributes = ParamAttributes(Self::NONNULL_FLAG);

    /// Marks this parameter as being a "by-value" struct pass, this is lowered to what ABIs define
    /// it to be.
    ///
    /// The exact semantics here
    #[inline(always)]
    pub const fn byval(size: usize) -> Self {
        // all lower bits are available for `byval` size
        debug_assert!(size < Self::BYVAL_N_FLAG as usize);

        Self(Self::BYVAL_N_FLAG | (size as u32))
    }

    /// Checks whether the set of attributes includes `byval(n)`
    #[inline(always)]
    pub fn is_byval(self) -> bool {
        (self.0 & Self::BYVAL_N_FLAG) != 0
    }

    /// If `self` includes `byval(n)`, returns what `n` is.
    #[inline(always)]
    pub fn byval_size(self) -> Option<u32> {
        if self.is_byval() {
            Some(self.0 & (Self::BYVAL_N_FLAG - 1))
        } else {
            None
        }
    }

    /// Checks whether the set of attributes includes `noalias`
    #[inline(always)]
    pub fn is_noalias(self) -> bool {
        (self.0 & Self::NOALIAS_FLAG) != 0
    }

    /// Checks whether the set of attributes includes `noalias`
    #[inline(always)]
    pub fn is_nonnull(self) -> bool {
        (self.0 & Self::NONNULL_FLAG) != 0
    }
}

impl BitOr for ParamAttributes {
    type Output = ParamAttributes;

    #[inline(always)]
    fn bitor(self, rhs: Self) -> Self::Output {
        debug_assert_ne!(self.is_byval(), rhs.is_byval());

        Self(self.0 | rhs.0)
    }
}

impl BitOrAssign for ParamAttributes {
    #[inline(always)]
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0;
    }
}

impl BitAnd for ParamAttributes {
    type Output = ParamAttributes;

    #[inline(always)]
    fn bitand(self, rhs: Self) -> Self::Output {
        debug_assert_ne!(self.is_byval(), rhs.is_byval());

        Self(self.0 & rhs.0)
    }
}

impl BitAndAssign for ParamAttributes {
    #[inline(always)]
    fn bitand_assign(&mut self, rhs: Self) {
        self.0 &= rhs.0;
    }
}

/// Denotes possible attributes that can be applied to the return value of a function.
#[repr(transparent)]
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct RetAttributes(u32);

impl RetAttributes {
    const NOALIAS_FLAG: u32 = 0b1000_0000_0000_0000_0000_0000_0000_0000;
    const NONNULL_FLAG: u32 = 0b0100_0000_0000_0000_0000_0000_0000_0000;

    /// No return value attributes
    pub const NONE: RetAttributes = RetAttributes(0);

    /// `noalias`: Only applicable to pointers. Asserts that a pointer does not
    /// alias any other pointers accessible in the program, this is meant for
    /// functions that behave in a `malloc`-like way.
    pub const NOALIAS: RetAttributes = RetAttributes(Self::NOALIAS_FLAG);

    /// `nonnull`: simply asserts that the pointer is not `null`.
    pub const NONNULL: RetAttributes = RetAttributes(Self::NONNULL_FLAG);

    /// Checks whether the set of attributes includes `noalias`
    #[inline(always)]
    pub fn is_noalias(self) -> bool {
        (self.0 & Self::NOALIAS_FLAG) != 0
    }

    /// Checks whether the set of attributes includes `noalias`
    #[inline(always)]
    pub fn is_nonnull(self) -> bool {
        (self.0 & Self::NONNULL_FLAG) != 0
    }
}

impl BitOr for RetAttributes {
    type Output = RetAttributes;

    #[inline(always)]
    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0 | rhs.0)
    }
}

impl BitOrAssign for RetAttributes {
    #[inline(always)]
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0;
    }
}

impl BitAnd for RetAttributes {
    type Output = RetAttributes;

    #[inline(always)]
    fn bitand(self, rhs: Self) -> Self::Output {
        Self(self.0 & rhs.0)
    }
}

impl BitAndAssign for RetAttributes {
    #[inline(always)]
    fn bitand_assign(&mut self, rhs: Self) {
        self.0 &= rhs.0;
    }
}

/// Models metadata about the function necessary for later codegen.
///
/// This is kept up-to-date through the DFG
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct FunctionMetadata {
    /// Whether the function contains an `alloca` instruction in any (possibly dead) path.
    ///
    /// If it does, this forces the stack frame management code to work differently.
    pub has_alloca: bool,
    /// Whether the function calls any other functions, directly or
    /// indirectly.
    pub is_leaf: bool,
}

/// Models which calling convention a given function should be emitted
/// to follow.
#[repr(u8)]
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub enum CallConv {
    /// The default C convention for the given target platform.
    C,
    /// System-V (only valid when targeting x86-64)
    SysV,
    /// Windows x64 (only valid when targeting x86-64)
    Win64,
}

dense_arena_key! {
    /// The reference type for [`Signature`]s. They are keys into a table
    /// stored inside the [`DataFlowGraph`] of the function that they are used in.
    ///
    /// Note that this means that a `Sig` is only valid in its own function.
    pub struct Sig;
}

/// Holds all of the information necessary to call a function.
///
/// These are held in the [`DataFlowGraph`] alongside everything else
/// in a function, and are referenced through [`Sig`]s.
#[derive(Debug, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct Signature {
    params: SmallVec<[(Type, ParamAttributes); 2]>,
    ret: Option<(Type, RetAttributes)>,
    call_conv: CallConv,
    vararg: bool,
}

impl Signature {
    pub(crate) fn new(
        params: SmallVec<[(Type, ParamAttributes); 2]>,
        ret: Option<(Type, RetAttributes)>,
        call_conv: CallConv,
        vararg: bool,
    ) -> Self {
        Self {
            params,
            ret,
            call_conv,
            vararg,
        }
    }

    /// Gets the return type of the function signature.
    ///
    /// Note that `None` represents `void`, i.e. a function that doesn't
    /// actually return anything.
    #[inline]
    pub fn return_ty(&self) -> Option<Type> {
        self.ret.map(|(ty, _)| ty)
    }

    /// Gets the list of attributes on the return value of the function.
    #[inline]
    pub fn return_attributes(&self) -> Option<RetAttributes> {
        self.ret.map(|(_, attributes)| attributes)
    }

    /// Gets everything related to the return value.
    #[inline]
    pub fn return_complete(&self) -> Option<(Type, RetAttributes)> {
        self.ret
    }

    /// Gets the list of parameters and their associated attributes for the function.
    #[inline]
    pub fn params(&self) -> &[(Type, ParamAttributes)] {
        &self.params
    }

    /// Gets the function's calling convention
    #[inline]
    pub fn calling_conv(&self) -> CallConv {
        self.call_conv
    }

    /// Checks if the signature is for a vararg (`...`) function. This can change
    /// how parameters are passed and how the type-checker should work.
    #[inline]
    pub fn vararg(&self) -> bool {
        self.vararg
    }

    /// Checks if the signature refers to a `void` function.
    #[inline]
    pub fn is_void(&self) -> bool {
        self.return_ty().is_none()
    }
}

dense_arena_key! {
    /// The reference type for a [`Function`]. These can be looked up
    /// at the [`Module`](crate::ir::Module) level.
    pub struct Func;
}

/// The definition of a function.
///
/// This provides the storage for data in the function, and the
/// layout information that actually makes up a meaningful chunk of IR.
#[derive(Debug, Clone, Default)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct FunctionDefinition {
    /// The "data-flow graph" (DFG) of the function. This is effectively
    /// the storage for every entity (instruction, value, block, etc.) that
    /// is used inside the function.
    ///
    /// This also contains data-flow information, it can tell you the
    /// data dependencies between each value.
    pub dfg: DataFlowGraph,
    /// The layout of a function. This maps all the data in the DFG into
    /// a structure that actually makes up a function, it models the relationships
    /// *between* entities from the DFG.
    ///
    /// This contains the lists that make up basic blocks, and the block ordering.
    pub layout: Layout,
}

/// Models a single function in the IR.
///
/// Contains a list of basic blocks and a list of parameters (included
/// in the signature), and a name.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct Function {
    name: String,
    sig: Signature,
    func: Func,
    context: ModuleContext,
    definition: Option<FunctionDefinition>,
}

impl Function {
    /// Creates an empty function with a given name and signature.
    ///
    /// This is equivalent to "declaring" a function, as a declared function is
    /// just a function without a body.
    pub fn new(name: String, sig: Signature, func: Func, ctx: ModuleContext) -> Self {
        Self {
            name,
            sig,
            func,
            context: ctx,
            definition: None,
        }
    }

    /// Gets the signature of the function.
    #[inline]
    pub fn signature(&self) -> &Signature {
        &self.sig
    }

    /// Gets the return type of the function. If the function
    /// is a `void` function, [`None`] is returned.
    #[inline]
    pub fn return_ty(&self) -> Option<Type> {
        self.signature().return_ty()
    }

    /// Checks if the function is a declaration, i.e. whether or not
    /// it actually has a definition
    #[inline]
    pub fn is_decl(&self) -> bool {
        self.definition.is_none()
    }

    /// Gets the function definition if it exists.
    #[inline]
    pub fn definition(&self) -> Option<&FunctionDefinition> {
        self.definition.as_ref()
    }

    /// Gets the function definition if it exists.
    #[inline]
    pub fn definition_mut(&mut self) -> Option<&mut FunctionDefinition> {
        self.definition.as_mut()
    }

    /// Gets the name of the function without `@`.
    #[inline]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Gets a [`Func`] that refers to `self`. This can be used when a [`Module`]
    /// is not available to get [`Func`]s from.
    ///
    /// [`Module`]: crate::ir::Module
    #[inline]
    pub fn func(&self) -> Func {
        self.func
    }

    /// Gets the module context associated with the module that contains
    /// this function, allowing the type and string pools to be accessed directly.
    #[inline]
    pub fn ctx(&self) -> &ModuleContext {
        &self.context
    }

    /// Computes the function's metadata. If there isn't a definition, returns `None`.
    ///
    /// The metadata is computed in a relatively efficient way, not the naive "walk the
    /// entire function looking for patterns" method.
    pub fn compute_metadata(&self) -> Option<FunctionMetadata> {
        let def = self.definition.as_ref()?;
        let mut has_alloca = false;
        let mut is_leaf = true;

        for &inst in def.dfg.all_metadata_affecting_insts() {
            if def.layout.is_inst_inserted(inst) {
                match def.dfg.inst_data(inst) {
                    InstData::Alloca(_) => has_alloca = true,
                    InstData::Call(_) | InstData::IndirectCall(_) => is_leaf = false,
                    _ => {}
                }
            }
        }

        Some(FunctionMetadata {
            has_alloca,
            is_leaf,
        })
    }

    pub(in crate::ir) fn replace_definition(&mut self, def: FunctionDefinition) {
        self.definition.replace(def);
    }
}
