//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::ir::{DataFlowGraph, Type};
use bitflags::bitflags;
use slotmap::new_key_type;
use smallvec::SmallVec;

#[cfg(feature = "enable-serde")]
use serde::{Deserialize, Serialize};

bitflags! {
    /// Models the different attributes that can be on a given parameter.
    #[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
    struct ParamAttributes: u64 {
        /// `noalias`: Only applicable to pointers. Asserts that a pointer does not
        /// alias any other pointers accessible by the function. Note that
        /// a `noalias` pointer *can* have aliases at the call site, this only
        /// asserts that the function itself cannot access the pointer through any other means.
        const Noalias = 1;
        /// `nonnull`: simply asserts that the pointer is not `null`.
        const Nonnull = 2;
        /// `dereferenceable`: asserts that dereferencing the pointer will not
        /// trap or cause any side-effects besides loading the memory, and that
        /// it is thus safe to load from speculatively.
        const Dereferenceable = 4;
    }
}

bitflags! {
    /// Models the different attributes that can be on a given return value.
    #[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
    struct RetAttributes: u64 {
        /// `noalias`: Only applicable to pointers. Asserts that a pointer does not
        /// alias any other pointers accessible in the program, this is meant for
        /// functions that behave in a `malloc`-like way.
        const Noalias = 1;
        /// `nonnull`: simply asserts that the pointer is not `null`.
        const Nonnull = 2;
        /// `dereferenceable`: asserts that dereferencing the pointer will not
        /// trap or cause any side-effects besides loading the memory, and that
        /// it is thus safe to load from speculatively.
        const Dereferenceable = 4;
    }
}

/// Models which calling convention a given function should be emitted
/// to follow.
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub enum CallConv {
    /// The default C convention for the given target platform.
    C,
    /// The System-V calling convention for the target architecture.
    SysV,
}

new_key_type! {
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
    ret: (Option<Type>, RetAttributes),
    call_conv: CallConv,
}

impl Signature {
    /// Gets the return type of the function signature.
    ///
    /// Note that `None` represents `void`, i.e. a function that doesn't
    /// actually return anything.
    pub fn return_ty(&self) -> Option<Type> {
        self.ret.0
    }
}

new_key_type! {
    /// The reference type for a [`Function`]. These can be looked up
    /// at the [`Module`] level.
    pub struct Func;
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct Function {
    name: String,
    sig: Signature,
    dfg: DataFlowGraph,
}

impl Function {
    pub fn signature(&self) -> &Signature {
        &self.sig
    }

    pub fn return_ty(&self) -> Option<Type> {
        self.signature().return_ty()
    }
}
