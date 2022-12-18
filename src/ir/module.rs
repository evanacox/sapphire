//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::ir::{Func, Function, TypeContext};
use slotmap::SlotMap;

#[cfg(feature = "enable-serde")]
use serde::{Deserialize, Serialize};

/// Contains all the data necessary for a single module of SIR.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct Module {
    types: TypeContext,
    functions: SlotMap<Func, Function>,
}

impl Module {
    /// Resolves a [`Func`] into a real function with a real signature
    /// and (possibly) a real body.
    pub fn function(&self, func: Func) -> &Function {
        &self.functions[func]
    }
}
