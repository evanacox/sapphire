//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::ir::{BasicBlock, Block, Func, Module};
use crate::reader2::{Lex, Token};
use crate::utility::SaHashMap;

/// Parses a string containing Sapphire IR.
pub struct Parser<'a> {
    lex: Lex<'a>,
    module: Module,
    bb_tokens: SaHashMap<(Func, Block), Vec<Token<'a>>>,
}

impl<'a> Parser<'a> {
    /// Creates a parser for a [`Module`] named `name`.
    ///
    /// `source` will be parsed into the module when [`Self::parse`] is called.
    pub fn new(name: &'a str, source: &'a str) -> Self {
        Self {
            lex: Lex::new(source),
            module: Module::new(name),
            bb_tokens: SaHashMap::default(),
        }
    }

    /// Parses the file, and if there are no errors returns a [`Module`]
    pub fn parse(mut self) -> Option<Module> {
        todo!()
    }
}
