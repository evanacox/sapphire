//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::arena::{ArenaMap, SecondaryMap};
use crate::dense_arena_key;
use crate::ir::{Func, Function, Module, ModuleIdentity};
use ahash::AHashMap;
use smallvec::{smallvec, SmallVec};
use std::any::{Any, TypeId};
use std::cell::{Ref, RefCell};
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};
use std::hash::Hash;
use std::ops::Deref;
use std::{fmt, mem};

struct All;

/// Models the set of analyses that a given transformation pass
/// preserves.
///
/// This is not a contract that is checked, it is expected the the transform knows what
/// analyses it can preserve. If it reports incorrectly, this can lead to mis-compilations
/// or panics inside the compiler.
#[derive(Debug)]
pub struct PreservedAnalyses {
    // sorted so we can binary_search for `contains`
    preserved: SmallVec<[TypeId; 2]>,
}

impl PreservedAnalyses {
    /// Returns a [`PreservedAnalyses`] that marks every analysis as preserved.
    pub fn all() -> Self {
        Self {
            preserved: smallvec![TypeId::of::<All>()],
        }
    }

    /// Returns a [`PreservedAnalyses`] that marks every analysis as invalidated.
    pub fn none() -> Self {
        Self {
            preserved: smallvec![],
        }
    }

    /// Checks if *all* analyses are preserved by a given transformation. If this
    /// is true, the transformation effectively reports to have not changed
    /// *anything* in the IR.
    ///
    /// This cannot be obtained in any way except [`Self::all`].
    pub fn preserves_all(&self) -> bool {
        self.preserved.len() == 1 && self.preserved[0] == TypeId::of::<All>()
    }

    /// Reports that an analysis is preserved by the current transformation.
    pub fn preserve<T: Any>(&mut self) {
        self.insert(TypeId::of::<T>())
    }

    /// Gets the intersection of two sets of preserved analyses, returning
    /// the analyses that are preserved both by `self` and by `other`.
    pub fn intersect(self, other: PreservedAnalyses) -> PreservedAnalyses {
        if self.preserves_all() {
            return other;
        }

        let mut new = PreservedAnalyses::none();
        let intersection = self.preserved.into_iter().filter(|id| other.contains(*id));

        for id in intersection {
            new.insert(id)
        }

        new
    }

    /// Checks if an analysis is preserved. If all are preserved
    /// or an analysis with an equivalent [`TypeId`] has been preserved
    /// with [`Self::preserve`], this returns `true`.
    pub fn is_preserved(&self, id: TypeId) -> bool {
        self.preserves_all() || self.contains(id)
    }

    fn contains(&self, id: TypeId) -> bool {
        self.preserved.binary_search(&id).is_ok()
    }

    fn insert(&mut self, id: TypeId) {
        if let Err(pos) = self.preserved.binary_search(&id) {
            self.preserved.insert(pos, id);
        }
    }
}

dense_arena_key! {
    struct Pass;
}

trait IRAnalysisPass<IR>: Any {
    type Traits: StorageTraits<IR = IR>;
    type Result: Any;

    fn expects_preserved(&self) -> &'static [TypeId];

    fn run(&mut self, ir: &IR, am: &AnalysisManager<Self::Traits>) -> Self::Result;
}

struct IRAnalysisWrapper<T> {
    inner: T,
}

impl<T, IR> IRAnalysisPass<IR> for IRAnalysisWrapper<T>
where
    T: IRAnalysisPass<IR>,
{
    type Traits = T::Traits;
    type Result = Box<dyn Any>;

    fn expects_preserved(&self) -> &'static [TypeId] {
        self.inner.expects_preserved()
    }

    fn run(
        &mut self,
        ir: &<Self::Traits as StorageTraits>::IR,
        am: &AnalysisManager<Self::Traits>,
    ) -> Self::Result {
        Box::new(self.inner.run(ir, am))
    }
}

type BoxedPass<Traits> =
    Box<dyn IRAnalysisPass<<Traits as StorageTraits>::IR, Traits = Traits, Result = Box<dyn Any>>>;

trait StorageTraits: 'static {
    type Key: Hash + Eq;
    type IR;

    fn key_from(ir: &Self::IR, pass: Pass) -> Self::Key;
}

struct FunctionStorageTraits;

impl StorageTraits for FunctionStorageTraits {
    type Key = (Func, Pass);
    type IR = Function;

    fn key_from(ir: &Self::IR, pass: Pass) -> Self::Key {
        (ir.func(), pass)
    }
}

struct ModuleStorageTraits;

impl StorageTraits for ModuleStorageTraits {
    type Key = (ModuleIdentity, Pass);
    type IR = Module;

    fn key_from(ir: &Self::IR, pass: Pass) -> Self::Key {
        (ir.identity(), pass)
    }
}

type MaybePassResult = RefCell<Option<Box<dyn Any>>>;

struct AnalysisManager<Traits: StorageTraits> {
    passes: ArenaMap<Pass, RefCell<BoxedPass<Traits>>>,
    pass_to_id: SecondaryMap<Pass, TypeId>,
    id_to_pass: HashMap<TypeId, Pass, ahash::RandomState>,
    results: HashMap<Traits::Key, MaybePassResult, ahash::RandomState>,
}

impl<Traits: StorageTraits> AnalysisManager<Traits> {
    /// Creates an empty manager with no passes registered.
    fn new() -> Self {
        Self {
            passes: ArenaMap::default(),
            results: AHashMap::default().into(),
            pass_to_id: SecondaryMap::default(),
            id_to_pass: AHashMap::default().into(),
        }
    }

    /// Registers an analysis pass with the manager. The pass is not run until it is
    /// later requested through [`Self::get`].
    fn add_pass<T: IRAnalysisPass<Traits::IR, Traits = Traits>>(&mut self, pass: T) {
        let id = TypeId::of::<T>();

        // initially, every pass is invalid. there's a possibility none of them
        // will even be ran, so there's no point to running them eagerly.
        //
        // "invalid" means it's not in `self.results`.
        let pass = self
            .passes
            .insert(RefCell::new(Box::new(IRAnalysisWrapper { inner: pass })));

        // map id -> pass and pass -> id
        self.id_to_pass.insert(id, pass);
        self.pass_to_id.insert(pass, id);
    }

    /// Invalidates all the passes that were not explicitly preserved by `preserved`.
    ///
    /// This does not trigger any passes to be re-run, it merely marks them as invalid
    /// which will cause a re-run if they are later requested through [`Self::get`].
    fn invalidate(&mut self, ir: &Traits::IR, preserved: PreservedAnalyses) {
        for (key, pass) in self.passes.iter() {
            let pass = pass.borrow();

            #[cfg(debug_assertions)]
            {
                for p in pass.expects_preserved() {
                    debug_assert!(preserved.is_preserved(*p));
                }
            }

            if !preserved.is_preserved(self.pass_to_id[key]) {
                let result_key = Traits::key_from(ir, key);
                let slot = self
                    .results
                    .get_mut(&result_key)
                    .expect("didn't call `Self::initialize` for ir unit");

                // if the key is already invalid in the map, nothing happens.
                // if it was valid and there is a result in the map, we remove it.
                slot.get_mut().take();
            }
        }
    }

    /// Lazily gets the result of an analysis. If the analysis has been invalidated,
    /// the result is re-computed, cached, and then returned.
    fn get<T: IRAnalysisPass<Traits::IR, Traits = Traits>>(
        &self,
        ir: &Traits::IR,
    ) -> Ref<'_, T::Result> {
        let id = TypeId::of::<T>();
        let key = self
            .id_to_pass
            .get(&id)
            .copied()
            .expect("trying to get analysis that hasn't been registered");

        // if we've already computed the value and it's valid, just return
        // that instead of recomputing. otherwise, recompute, cache, and return it.
        match self.pass_result_for::<T>(ir, key) {
            Some(result) => result,
            None => {
                let result = {
                    let mut pass = self.passes[key].borrow_mut();

                    pass.run(ir, self)
                };

                self.update::<T>(ir, key, result)
            }
        }
    }

    fn initialize(&mut self, ir: &Traits::IR, pass: Pass) {
        let key = Traits::key_from(ir, pass);

        self.results
            .entry(key)
            .or_insert_with(|| RefCell::new(None));
    }

    fn update<T: IRAnalysisPass<Traits::IR, Traits = Traits>>(
        &self,
        ir: &Traits::IR,
        pass: Pass,
        result: Box<dyn Any>,
    ) -> Ref<'_, T::Result> {
        let key = Traits::key_from(ir, pass);
        let slot = &self.results[&key];

        slot.borrow_mut().replace(result);

        Ref::map(slot.borrow(), |inner: &Option<Box<dyn Any>>| {
            // we know that unwrapping `inner` is safe, we just inserted in the prev line.
            // we then downcast the `dyn Any` into `T::Result`
            inner.as_ref().unwrap().downcast_ref().unwrap()
        })
    }

    fn pass_result_for<T: IRAnalysisPass<Traits::IR, Traits = Traits>>(
        &self,
        ir: &Traits::IR,
        pass: Pass,
    ) -> Option<Ref<'_, T::Result>> {
        let key = Traits::key_from(ir, pass);
        let slot = self.results[&key].borrow();

        // `map`s api forces us to borrow and that breaks the `Ref::map` which needs to take `slot`
        // by value. unless we want to add a clone, borrow checker doesn't know how to deal with it
        // the nice way
        #[allow(clippy::manual_map)]
        match slot.deref() {
            Some(_) => Some(Ref::map(slot, |inner| {
                inner.as_ref().unwrap().downcast_ref().unwrap()
            })),
            None => None,
        }
    }
}

impl<Traits: StorageTraits> Debug for AnalysisManager<Traits> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut m = f.debug_set();

        for (key, _) in self.passes.iter() {
            m.entry(&key);
        }

        m.finish()
    }
}

/// An analysis pass that runs over an entire module.
pub trait ModuleAnalysisPass: Any {
    /// The result type of a given analysis.
    type Result;

    /// Allows analyses to declare dependence on other analyses.
    ///
    /// This directly implies that if T is preserved, all analyses referred
    /// to by T::expects_preserved are also assumed to be preserved.
    ///
    /// This is checked in debug mode.
    fn expects_preserved(&self) -> &'static [TypeId];

    /// Performs the analysis and returns a computed result. This should not be an impure
    /// operation, running the analysis twice on the same input should produce the same result.
    fn run(&mut self, module: &Module, am: &ModuleAnalysisManager) -> Self::Result;
}

/// An analysis that runs over an entire function.
pub trait FunctionAnalysisPass: Any {
    /// The result type of a given analysis.
    type Result;

    /// Allows analyses to declare dependence on other analyses.
    ///
    /// This directly implies that if T is preserved, all analyses referred
    /// to by T::expects_preserved are also assumed to be preserved.
    ///
    /// This is checked in debug mode.
    fn expects_preserved(&self) -> &'static [TypeId];

    /// Performs the analysis and returns a computed result. This should not be an impure
    /// operation, running the analysis twice on the same input should produce the same result.
    fn run(&mut self, func: &Function, am: &FunctionAnalysisManager) -> Self::Result;
}

impl<T> IRAnalysisPass<Function> for T
where
    T: FunctionAnalysisPass,
{
    type Traits = FunctionStorageTraits;
    type Result = T::Result;

    #[inline]
    fn expects_preserved(&self) -> &'static [TypeId] {
        <T as FunctionAnalysisPass>::expects_preserved(self)
    }

    #[inline]
    fn run(&mut self, ir: &Function, am: &AnalysisManager<Self::Traits>) -> Self::Result {
        // this is safe, `FunctionAnalysisManager` is a layout-compatible wrapper. we can treat
        // one of these as-if it was a `FunctionAnalysisManager` for the sake of running the pass
        <T as FunctionAnalysisPass>::run(self, ir, unsafe { mem::transmute(am) })
    }
}

impl<T> IRAnalysisPass<Module> for T
where
    T: ModuleAnalysisPass,
{
    type Traits = ModuleStorageTraits;
    type Result = T::Result;

    #[inline]
    fn expects_preserved(&self) -> &'static [TypeId] {
        <T as ModuleAnalysisPass>::expects_preserved(self)
    }

    #[inline]
    fn run(&mut self, ir: &Module, am: &AnalysisManager<Self::Traits>) -> Self::Result {
        // this is safe, `FunctionAnalysisManager` is a layout-compatible wrapper. we can treat
        // one of these as-if it was a `FunctionAnalysisManager` for the sake of running the pass
        <T as ModuleAnalysisPass>::run(self, ir, unsafe { mem::transmute(am) })
    }
}

/// A lazy analysis manager for a single function in SIR.
///
/// Analysis passes are registered through [`Self::add_pass`], and then can be later requested
/// through [`Self::get`]. These are lazily recomputed as they are invalidated and requested
/// through different passes.
///
/// When a pass wants the result of an analysis, it uses [`Self::get`] which will either
/// return the computed result, or if the analysis is "invalid" it will compute the result,
/// cache it, and then return it.
///
/// When a pass completes, it returns a list of preserved analyses ([`PreservedAnalyses`]),
/// those are then passed to this, which marks the analyses that are not preserved as invalid.
#[derive(Debug)]
#[repr(transparent)]
pub struct FunctionAnalysisManager(AnalysisManager<FunctionStorageTraits>);

impl FunctionAnalysisManager {
    /// Creates a new [`FunctionAnalysisManager`].
    ///
    /// This manager has no analyses registered, they need to be added with [`Self::add_pass`]
    /// before they can be used by transform passes.
    #[inline]
    pub fn new() -> Self {
        Self(AnalysisManager::new())
    }

    /// Registers a function analysis pass. The pass is not run, but the
    /// state for it to be used later is set up inside the manager.
    ///
    /// You cannot use `T` in any of the other methods in this type without
    /// having called this one with the same `T` first, or else you'll get a panic.
    pub fn add_pass<T: FunctionAnalysisPass>(&mut self, pass: T) {
        self.0.add_pass(pass)
    }

    /// Lazily gets the result of an analysis. If the analysis has been invalidated,
    /// the result is re-computed, cached, and then returned.
    pub fn get<T: FunctionAnalysisPass>(&self, ir: &Function) -> Ref<'_, T::Result> {
        self.0.get::<T>(ir)
    }
}

impl Default for FunctionAnalysisManager {
    fn default() -> Self {
        Self::new()
    }
}

/// A lazy analysis manager for a module of SIR.
///
/// Analysis passes are registered through [`Self::add_pass`], and then can be later requested
/// through [`Self::get`]. These are lazily recomputed as they are invalidated and requested
/// through different passes.
///
/// When a pass wants the result of an analysis, it uses [`Self::get`] which will either
/// return the computed result, or if the analysis is "invalid" it will compute the result,
/// cache it, and then return it.
///
/// When a pass completes, it returns a list of preserved analyses ([`PreservedAnalyses`]),
/// those are then passed to this, which marks the analyses that are not preserved as invalid.
#[derive(Debug)]
#[repr(transparent)]
pub struct ModuleAnalysisManager(AnalysisManager<ModuleStorageTraits>);

impl ModuleAnalysisManager {
    /// Creates a new [`ModuleAnalysisManager`].
    ///
    /// This manager has no analyses registered, they need to be added with [`Self::add_pass`]
    /// before they can be used by transform passes.
    #[inline]
    pub fn new() -> Self {
        Self(AnalysisManager::new())
    }

    /// Registers a module analysis pass. The pass is not run, but the
    /// state for it to be used later is set up inside the manager.
    ///
    /// You cannot use `T` in any of the other methods in this type without
    /// having called this one with the same `T` first, or else you'll get a panic.
    pub fn add_pass<T: ModuleAnalysisPass>(&mut self, pass: T) {
        self.0.add_pass(pass)
    }

    /// Lazily gets the result of an analysis. If the analysis has been invalidated,
    /// the result is re-computed, cached, and then returned.
    pub fn get<T: ModuleAnalysisPass>(&self, ir: &Module) -> Ref<'_, T::Result> {
        self.0.get::<T>(ir)
    }
}

impl Default for ModuleAnalysisManager {
    fn default() -> Self {
        Self::new()
    }
}
