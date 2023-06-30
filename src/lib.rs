//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

#![allow(dead_code)]
#![deny(
    unreachable_pub,
    missing_docs,
    missing_abi,
    rust_2018_idioms,
    rustdoc::broken_intra_doc_links,
    rustdoc::private_intra_doc_links
)]
#![allow(unused_variables)]

//! # Sapphire
//!
//! These are the basic APIs for building, manipulating and emitting SIR.

mod reader;

pub mod analysis;
pub mod arena;
pub mod cli;
pub mod codegen;
pub mod ir;
pub mod pass;
pub mod transforms;
pub mod utility;
pub mod vm;

pub use reader::parse_sir;
