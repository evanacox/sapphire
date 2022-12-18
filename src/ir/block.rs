//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::ir::{Inst, Value};
use slotmap::new_key_type;

#[cfg(feature = "enable-serde")]
use serde::{Deserialize, Serialize};
use smallvec::SmallVec;

new_key_type! {
    pub struct Block;
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct BasicBlock {
    body: SmallVec<[Inst; 2]>,
    params: SmallVec<[Value; 2]>,
}
