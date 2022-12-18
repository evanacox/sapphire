//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use slotmap::new_key_type;
use static_assertions::assert_eq_size;

#[cfg(feature = "enable-serde")]
use serde::{Deserialize, Serialize};

new_key_type! {
    pub struct ConstRef;
}

pub struct ConstantPool {
    //
}

pub enum Constant {
    Int(u64),
    Float(u64),
    Array(ConstRef),
    Struct(ConstRef),
}

assert_eq_size!(Constant, (usize, usize));
