//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::runners::optimization_runner::*;
use crate::subtest::Subtest;
use sapphire::transforms::Mem2RegPass;

runner_for_opt!(mem2reg, FunctionToModulePassAdapter::adapt(Mem2RegPass));

pub const fn mem2reg_subtest() -> Subtest {
    Subtest::new("mem2reg", mem2reg)
}
