//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
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
use std::sync::{Arc, RwLock, RwLockReadGuard, RwLockWriteGuard};

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

#[derive(Debug)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
struct InnerModuleContext {
    types: RwLock<TypePool>,
    strings: RwLock<StringPool>,
}

impl InnerModuleContext {
    fn with_strings(pool: StringPool) -> Self {
        Self {
            types: RwLock::default(),
            strings: RwLock::new(pool),
        }
    }
}

impl Clone for InnerModuleContext {
    fn clone(&self) -> Self {
        let types = self.types.read().unwrap();
        let strings = self.strings.read().unwrap();

        Self {
            types: RwLock::new(types.clone()),
            strings: RwLock::new(strings.clone()),
        }
    }
}

/// Models shared ownership of the state that is shared between all entities in a module.
///
/// This state contains all of the types and all of the strings in a given module,
/// and since different passes may need to access/mutate that data (possibly simultaneously),
/// this type exists.
///
/// Internally, this is an [`Arc`] referring to [`RwLock`]s that hold a [`TypePool`]
/// and a [`StringPool`].
#[derive(Debug, Clone)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct ModuleContext {
    data: Arc<InnerModuleContext>,
}

impl ModuleContext {
    fn with_strings(pool: StringPool) -> Self {
        Self {
            data: Arc::new(InnerModuleContext::with_strings(pool)),
        }
    }

    /// Returns a guard that allows the type pool to be read.
    ///
    /// Since the underlying lock is a [`RwLock`], this is usually going to be
    /// able to lock immediately.
    pub fn types(&self) -> RwLockReadGuard<'_, TypePool> {
        self.data.types.read().expect("lock was poisoned")
    }

    /// Returns a guard that allows the type pool to be written to.
    ///
    /// Since the underlying lock is a [`RwLock`], this can cause any other
    /// threads waiting to read to stall. Make sure that the guard is only
    /// held for the minimum amount necessary, i.e. try to avoid making multiple
    /// calls to this and instead batch writes where possible.
    pub fn types_mut(&self) -> RwLockWriteGuard<'_, TypePool> {
        self.data.types.write().expect("lock was poisoned")
    }

    /// Returns a guard that allows the string pool to be read.
    ///
    /// Since the underlying lock is a [`RwLock`], this is usually going to be
    /// able to lock immediately.
    pub fn strings(&self) -> RwLockReadGuard<'_, StringPool> {
        self.data.strings.read().expect("lock was poisoned")
    }

    /// Returns a guard that allows the string pool to be written to.
    ///
    /// Since the underlying lock is a [`RwLock`], this can cause any other
    /// threads waiting to read to stall. Make sure that the guard is only
    /// held for the minimum amount necessary, i.e. try to avoid making multiple
    /// calls to this and instead batch writes where possible.
    pub fn strings_mut(&self) -> RwLockWriteGuard<'_, StringPool> {
        self.data.strings.write().expect("lock was poisoned")
    }
}

/// Contains all the data necessary for a single module of SIR.
///
/// This models all of the information that would be represented inside of
/// a textual module of SIR.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct Module {
    identity: Box<u8>,
    name_ref: Str,
    context: ModuleContext,
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
            context: ModuleContext::with_strings(pool),
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
        debug_assert!(matches!(self.find_function_by_name(name), None));

        let name = name.to_owned();
        let ctx = self.context.clone();
        let new = Function::new(name.clone(), sig, self.functions.next_key(), ctx);
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

    /// Gets the [`ModuleContext`] owned by this module. This can be cloned as necessary.
    pub fn context(&self) -> &ModuleContext {
        &self.context
    }

    /// Convenience method for quickly inserting a string into the module
    /// and getting a [`Str`] that refers to it.
    pub fn insert_string(&self, string: &str) -> Str {
        self.context.strings_mut().insert(string)
    }

    /// Shorthand for getting the [`TypePool`] for a given module.
    pub fn type_pool_mut(&mut self) -> RwLockWriteGuard<'_, TypePool> {
        self.context.data.types.write().expect("lock was poisoned")
    }

    /// Shorthand for getting the [`TypePool`] for a given module.
    pub fn type_pool(&self) -> RwLockReadGuard<'_, TypePool> {
        self.context.data.types.read().expect("lock was poisoned")
    }

    /// Gets a [`ModuleIdentity`] that refers to the object.
    pub fn identity(&self) -> ModuleIdentity {
        ModuleIdentity(self.identity.as_ref() as *const _ as usize)
    }
}
