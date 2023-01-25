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
use crate::ir::{DataFlowGraph, Layout, ModuleContext, Type};
use crate::utility::PackedOption;
use bitflags::bitflags;
use smallvec::SmallVec;

#[cfg(feature = "enable-serde")]
use serde::{Deserialize, Serialize};

bitflags! {
    /// Models the different attributes that can be on a given parameter.
    #[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
    pub struct ParamAttributes: u32 {
        /// `noalias`: Only applicable to pointers. Asserts that a pointer does not
        /// alias any other pointers accessible by the function. Note that
        /// a `noalias` pointer *can* have aliases at the call site, this only
        /// asserts that the function itself cannot access the pointer through any other means.
        const NOALIAS = 1;
        /// `nonnull`: simply asserts that the pointer is not `null`.
        const NONNULL = 2;
        /// `dereferenceable`: asserts that dereferencing the pointer will not
        /// trap or cause any side-effects besides loading the memory, and that
        /// it is thus safe to load from speculatively.
        const DEREFERENCEABLE = 4;
    }
}

bitflags! {
    /// Models the different attributes that can be on a given return value.
    #[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
    pub struct RetAttributes: u32 {
        /// `noalias`: Only applicable to pointers. Asserts that a pointer does not
        /// alias any other pointers accessible in the program, this is meant for
        /// functions that behave in a `malloc`-like way.
        const NOALIAS = 1;
        /// `nonnull`: simply asserts that the pointer is not `null`.
        const NONNULL = 2;
        /// `dereferenceable`: asserts that dereferencing the pointer will not
        /// trap or cause any side-effects besides loading the memory, and that
        /// it is thus safe to load from speculatively.
        const DEREFERENCEABLE = 4;
    }
}

/// Models which calling convention a given function should be emitted
/// to follow.
#[repr(u8)]
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub enum CallConv {
    /// The default C convention for the given target platform.
    C,
    /// The System-V calling convention for the target architecture.
    SysV,
    /// The Windows calling convention for the target
    Win64,
    /// Similar to `fastcc` on LLVM, makes calls fast
    Fast,
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
    ret: (PackedOption<Type>, RetAttributes),
    call_conv: CallConv,
    vararg: bool,
}

impl Signature {
    pub(crate) fn new(
        params: SmallVec<[(Type, ParamAttributes); 2]>,
        ret: (Option<Type>, RetAttributes),
        call_conv: CallConv,
        vararg: bool,
    ) -> Self {
        Self {
            params,
            ret: (ret.0.into(), ret.1),
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
        self.ret.0.expand()
    }

    /// Gets the list of attributes on the return value of the function.
    #[inline]
    pub fn return_attributes(&self) -> RetAttributes {
        self.ret.1
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

    pub(in crate::ir) fn replace_definition(&mut self, def: FunctionDefinition) {
        self.definition.replace(def);
    }
}
