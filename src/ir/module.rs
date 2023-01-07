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
use crate::ir::{Func, FuncBuilder, Function, Signature, TypePool};
use crate::utility::{Str, StringPool};
use ahash::AHashMap;
use std::collections::HashMap;

#[cfg(feature = "enable-serde")]
use serde::{Deserialize, Serialize};

/// Used to identify different [`Module`] instances efficiently.
///
/// Every [`Module`] has some data allocated on the heap that is guaranteed
/// to not move around, the address of this data can be used to distinguish
/// between modules.
///
/// Note that this is not a way of telling if modules are *equivalent*,
/// this is a way of identifying the *same module*.
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct ModuleIdentity(usize);

/// Contains all the data necessary for a single module of SIR.
///
/// This models all of the information that would be represented inside of
/// a textual module of SIR.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct Module {
    identity: Box<u8>,
    name_ref: Str,
    types: TypePool,
    strings: StringPool,
    functions: ArenaMap<Func, Function>,
    names: HashMap<String, Func, ahash::RandomState>,
}

impl Module {
    /// Creates a new, empty module with a given name.
    ///
    /// This name is expected to be unique across different [`Module`]s, but it doesn't
    /// *have* to be for the correctness of any transforms.
    pub fn new(name: &str) -> Self {
        let mut pool = StringPool::default();
        let name_ref = pool.insert(name);

        Self {
            identity: Box::new(0),
            name_ref,
            types: TypePool::default(),
            strings: pool,
            functions: ArenaMap::default(),
            names: AHashMap::default().into(),
        }
    }

    /// Resolves a [`Func`] into a real function object.
    pub fn function(&self, func: Func) -> &Function {
        &self.functions[func]
    }

    /// Resolves a [`Func`] into a real function object.
    pub fn function_mut(&mut self, func: Func) -> &mut Function {
        &mut self.functions[func]
    }

    /// Finds a [`Func`] with a given name. If the function has not been added to
    /// the module, `None` is returned.
    pub fn find_function_by_name(&self, func: &str) -> Option<Func> {
        self.names.get(func).copied()
    }

    /// Declares and then defines a new function.
    pub fn define_function(&mut self, name: &str, sig: Signature) -> FuncBuilder<'_> {
        let f = self.declare_function(name, sig);

        self.define_existing_function(f)
    }

    /// Declares a function without providing it a definition. It can be defined
    /// later with [`Self::define_existing_function`], or it can be left
    /// as-is if the function is opaque.
    pub fn declare_function(&mut self, name: &str, sig: Signature) -> Func {
        debug_assert!(matches!(self.find_function_by_name(&name), None));

        let name = name.to_owned();
        let new = Function::new(name.clone(), sig, self.functions.next_key());
        let func = self.functions.insert(new);

        self.names.insert(name, func);

        func
    }

    /// Returns a [`FuncBuilder`] that will create a body for a previously-declared
    /// function.
    ///
    /// If the function already has a body, using the builder will completely
    /// replace the previous body.
    pub fn define_existing_function(&mut self, func: Func) -> FuncBuilder<'_> {
        FuncBuilder::new(self, func)
    }

    /// Returns an iterator over all of the functions in the module.
    pub fn functions(&self) -> impl Iterator<Item = Func> {
        self.functions.keys()
    }

    /// Gets the [`TypePool`] in use for all the functions inside of a module.
    pub fn type_pool(&self) -> &TypePool {
        &self.types
    }

    /// Gets the [`TypePool`] in use for all the functions inside of a module.
    pub fn type_pool_mut(&mut self) -> &mut TypePool {
        &mut self.types
    }

    /// Gets the [`TypePool`] in use for all the functions inside of a module.
    pub fn string_pool(&self) -> &StringPool {
        &self.strings
    }

    /// Gets the [`TypePool`] in use for all the functions inside of a module.
    pub fn string_pool_mut(&mut self) -> &mut StringPool {
        &mut self.strings
    }

    /// Convenience method for `self.string_pool_mut().insert(str)`.
    pub fn insert_string(&mut self, string: &str) -> Str {
        self.strings.insert(string)
    }

    /// Convenience method for `self.string_pool_mut()[str]`.
    pub fn resolve_string(&self, str: Str) -> &str {
        &self.strings[str]
    }

    /// Gets the user-given name of the module.
    pub fn name(&self) -> &str {
        self.resolve_string(self.name_ref)
    }

    /// Gets a [`ModuleIdentity`] that refers to the object.
    pub fn identity(&self) -> ModuleIdentity {
        ModuleIdentity(self.identity.as_ref() as *const _ as usize)
    }
}
