//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::arena::SecondaryMap;
use crate::codegen::{Architecture, MIRBlock, MIRFunction, MachInst, Reg};
use smallvec::SmallVec;

/// Models the live range information necessary for the register allocators.
///
/// This computes the `LiveIn` and `LiveOut`
pub struct Liveness {
    live_in: SecondaryMap<MIRBlock, SmallVec<[Reg; 5]>>,
    live_out: SecondaryMap<MIRBlock, SmallVec<[Reg; 5]>>,
}

impl Liveness {
    pub(super) fn compute<Arch, Inst>(mir: MIRFunction<Arch, Inst>) -> Self
    where
        Arch: Architecture,
        Inst: MachInst<Arch>,
    {
        todo!()
    }
}
