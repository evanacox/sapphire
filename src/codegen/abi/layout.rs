//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::codegen::TypeLayout;
use crate::ir::{Type, TypePool};

pub(crate) const STANDARD_64_BIT_LAYOUT: [TypeLayout; 8] = [
    TypeLayout::new(1, 1),
    TypeLayout::new(8, 8),
    TypeLayout::new(1, 1),
    TypeLayout::new(2, 2),
    TypeLayout::new(4, 4),
    TypeLayout::new(8, 8),
    TypeLayout::new(4, 4),
    TypeLayout::new(8, 8),
];

enum Inner {
    Array(TypeLayout, usize),
    // vec of (layout of field, offset of field)
    Struct(Vec<(TypeLayout, usize)>),
}

/// Models the more complex layout information
pub struct AggregateLayout {
    inner: Inner,
}

impl AggregateLayout {
    /// Calculates the layout information for a given aggregate type.
    pub fn from_aggregate(_ty: Type, _pool: &TypePool) -> Self {
        todo!()
    }

    /// Calculates the offset, in bytes, to get to the `member`-th member
    /// of a value of the aggregate type.
    ///
    /// This is basically `offsetof` in C, except for SIR structures.
    pub fn offset(&self, _member: usize) -> usize {
        todo!()
    }

    /// Returns the amount of padding that directly follows the `member`-th
    /// member of the aggregate type.
    pub fn padding(&self, _member: usize) -> usize {
        todo!()
    }
}
