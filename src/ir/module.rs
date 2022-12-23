//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::arena::ArenaMap;
use crate::ir::{Func, Function, TypeContext};

#[cfg(feature = "enable-serde")]
use serde::{Deserialize, Serialize};

/// Contains all the data necessary for a single module of SIR.
///
/// This models all of the information that would be represented inside of
/// a textual module of SIR.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct Module {
    types: TypeContext,
    functions: ArenaMap<Func, Function>,
}

impl Module {
    /// Resolves a [`Func`] into a real function with a real signature
    /// and (possibly) a real body.
    pub fn function(&self, func: Func) -> &Function {
        &self.functions[func]
    }

    /// Gets the type context associated with the module.
    pub fn type_ctx(&self) -> &TypeContext {
        &self.types
    }
}
