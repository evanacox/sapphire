//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::analysis::{ControlFlowGraphAnalysis, DominatorTreeAnalysis};
use crate::arena::{ArenaMap, SecondaryMap};
use crate::dense_arena_key;
use crate::ir::{Func, Function, Module, ModuleIdentity};
use crate::utility::{SaHashMap, SpinMutex};
use smallvec::{smallvec, SmallVec};
use std::any::{Any, TypeId};
use std::cell::{Ref, RefCell};
use std::fmt::{Debug, Formatter};
use std::hash::Hash;
use std::ops::Deref;
use std::rc::Rc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::{fmt, mem};

struct All;

#[doc(hidden)]
#[macro_export(local_inner_macros)]
macro_rules! __analysis_preserved_count {
    () => (0usize);
    ( $x:tt $($xs:tt)* ) => (1usize + __analysis_preserved_count!($($xs)*));
}

#[doc(hidden)]
pub struct _InitGuard {
    init: SpinMutex,
    is_finished: AtomicBool,
}

impl _InitGuard {
    pub const fn __new() -> Self {
        Self {
            init: SpinMutex::new(),
            is_finished: AtomicBool::new(false),
        }
    }

    // this could be bundled into `__acquire` but we want the ability
    // to run code before the actual acquiring happens
    #[inline(always)]
    pub fn __need_try_acquire(&self) -> bool {
        !self.is_finished.load(Ordering::Acquire)
    }

    // returns whether or not we need to perform the initialization and call `__release`
    #[inline(never)]
    pub fn __acquire(&self) -> bool {
        // one thread will acquire the lock and do the initialization, the rest
        // will wait until the lock is unlocked and will grab it one after the other
        self.init.lock();

        // we can't be sure if we actually got the lock first, lets check and see
        // if someone else finished the initialization once we own the lock
        let finished = self.is_finished.load(Ordering::Acquire);

        // if they did finish it, unlock
        if finished {
            self.init.unlock();
        }

        !finished
    }

    // unlocks the lock and marks the object as initialized
    #[inline(never)]
    pub fn __release(&self) {
        self.is_finished.store(true, Ordering::Release);
        self.init.unlock();
    }
}

/// Allows an analysis to define any other analysis that it depends on.
///
/// # Internal Implementation
/// Unfortunately, Rust has still not stabilized `const` for [`TypeId::of`] as of January
/// 2023, see <https://github.com/rust-lang/rust/issues/77125>. This requires trickery to get
/// lazy initialization that isn't slow.
///
/// Internally, this works similarly to how function-scoped `static` initialization
/// works in C++ (under the Itanium C++ ABI), arrays are lazily computed on the first
/// call to `expects_preserved` with the help of a guard (flag and a spinlock).
///
/// This accomplishes the end goal of ensuring that the array is only initialized once
/// even if multiple threads all call it at the same time when it's not initialized.
///
/// ```
/// # use sapphire::pass::*;
/// # use sapphire::analysis::*;
/// # use sapphire::analysis_preserved;
/// # use sapphire::ir::*;
/// # use std::any::TypeId;
/// pub struct MyAnalysis;
///
/// impl FunctionAnalysisPass for MyAnalysis {
///     type Result = i32;
///
///     fn expects_preserved(&self) -> &'static [TypeId] {
///         analysis_preserved!(ControlFlowGraphAnalysis, DominatorTreeAnalysis)
///     }
///
///     fn run(&mut self, _: &Function, _: &FunctionAnalysisManager) -> Self::Result {
///         42
///     }
/// }
/// ```
#[macro_export(local_inner_macros)]
macro_rules! analysis_preserved {
    ($($t:ty),*) => {
        {
            use $crate::pass::_InitGuard;
            use std::any::TypeId;
            use std::mem::MaybeUninit;

            static mut PRESERVED: MaybeUninit<[TypeId; __analysis_preserved_count!($($t)*)]> = MaybeUninit::uninit();
            static GUARD: _InitGuard = _InitGuard::__new();

            // check if anyone has already initialized this. almost always true
            if GUARD.__need_try_acquire() {
                let array = [
                    $(
                        TypeId::of::<$t>(),
                    )*];

                // multiple threads may try to do this at the same time, so __acquire
                // will wait if this happens and then check that it's initialized
                if GUARD.__acquire() {
                    unsafe {
                        PRESERVED = MaybeUninit::new(array);

                        GUARD.__release();
                    }
                }
            }

            // if we get here we know that we're initialized
            unsafe { PRESERVED.assume_init_ref() }
        }
    }
}

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

    fn invalidate(&mut self, ir: &IR, preserved: &PreservedAnalyses);

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

    fn invalidate(&mut self, ir: &IR, preserved: &PreservedAnalyses) {
        self.inner.invalidate(ir, preserved);
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
    id_to_pass: SaHashMap<TypeId, Pass>,
    results: SaHashMap<Traits::Key, MaybePassResult>,
}

impl<Traits: StorageTraits> AnalysisManager<Traits> {
    /// Creates an empty manager with no passes registered.
    fn new() -> Self {
        Self {
            passes: ArenaMap::default(),
            results: SaHashMap::default(),
            pass_to_id: SecondaryMap::default(),
            id_to_pass: SaHashMap::default(),
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
    fn invalidate(&mut self, ir: &Traits::IR, preserved: &PreservedAnalyses) {
        for (key, pass) in self.passes.iter() {
            // if the pass is preserved explicitly, we do nothing (and in debug
            // mode, we make sure that all the analyses depended on by that analysis
            // are also preserved). otherwise, we invalidate it
            if !preserved.is_preserved(self.pass_to_id[key]) {
                let result_key = Traits::key_from(ir, key);
                let slot = self
                    .results
                    .get_mut(&result_key)
                    .expect("didn't call `Self::initialize` for ir unit");

                // if the key is already invalid in the map, nothing happens.
                // if it was valid and there is a result in the map, we remove it.
                slot.get_mut().take();
            } else {
                #[cfg(debug_assertions)]
                {
                    let pass = pass.borrow();

                    for p in pass.expects_preserved() {
                        debug_assert!(preserved.is_preserved(*p));
                    }
                }
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

    /// Tells the analysis that it has been invalidated. It also
    /// sends preservation information along, some analyses need this.
    ///
    /// This is mostly here for [`FunctionAnalysisManagerModuleProxy`] to allow the module manaager
    /// to tell the function manager to invalidate passes.
    fn invalidate(&mut self, ir: &Module, preserved: &PreservedAnalyses) {
        let _ = ir;
        let _ = preserved;
    }

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

    /// Tells the analysis that it has been invalidated. It also
    /// sends preservation information along, some analyses need this.
    ///
    /// This is mostly here for [`FunctionAnalysisManagerModuleProxy`] to allow the module manaager
    /// to tell the function manager to invalidate passes.
    fn invalidate(&mut self, ir: &Function, preserved: &PreservedAnalyses) {
        let _ = ir;
        let _ = preserved;
    }

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
    fn invalidate(&mut self, ir: &Function, preserved: &PreservedAnalyses) {
        <T as FunctionAnalysisPass>::invalidate(self, ir, preserved)
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
    fn invalidate(&mut self, ir: &Module, preserved: &PreservedAnalyses) {
        <T as ModuleAnalysisPass>::invalidate(self, ir, preserved)
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

    /// Invalidates a set of analyses for a given function.
    ///
    /// Any analysis not explicitly marked to be preserved in `preserved` is
    /// considered to be invalidated.
    #[inline]
    pub fn invalidate(&mut self, ir: &Function, preserved: &PreservedAnalyses) {
        self.0.invalidate(ir, preserved)
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

    /// Invalidates a set of analyses for a given module.
    ///
    /// Any analysis not explicitly marked to be preserved in `preserved` is
    /// considered to be invalidated.
    #[inline]
    pub fn invalidate(&mut self, ir: &Module, preserved: &PreservedAnalyses) {
        self.0.invalidate(ir, preserved)
    }

    /// Registers a module analysis pass. The pass is not run, but the
    /// state for it to be used later is set up inside the manager.
    ///
    /// You cannot use `T` in any of the other methods in this type without
    /// having called this one with the same `T` first, or else you'll get a panic.
    #[inline]
    pub fn add_pass<T: ModuleAnalysisPass>(&mut self, pass: T) {
        self.0.add_pass(pass)
    }

    /// Lazily gets the result of an analysis. If the analysis has been invalidated,
    /// the result is re-computed, cached, and then returned.
    #[inline]
    pub fn get<T: ModuleAnalysisPass>(&self, ir: &Module) -> Ref<'_, T::Result> {
        self.0.get::<T>(ir)
    }
}

impl Default for ModuleAnalysisManager {
    fn default() -> Self {
        Self::new()
    }
}

/// Wrapper type that maps the function analysis manager into an
/// "analysis" that can be requested by module analyses.
///
/// The FAM is stored in an `Rc<RefCell<...>>` to facilitate both borrowing inside of
/// passes, and invalidation (which requires a `&mut`). One should not happen at
/// the same time as the other, but this is impossible to prove to the compiler otherwise.
pub struct FunctionAnalysisManagerModuleProxy {
    inner: Rc<RefCell<FunctionAnalysisManager>>,
}

impl FunctionAnalysisManagerModuleProxy {
    /// Wraps the FAM into a module pass.
    pub fn wrap(inner: FunctionAnalysisManager) -> Self {
        Self {
            inner: Rc::new(RefCell::new(inner)),
        }
    }
}

/// Alias for the underlying FAM type.
pub type FAMProxy = Rc<RefCell<FunctionAnalysisManager>>;

impl ModuleAnalysisPass for FunctionAnalysisManagerModuleProxy {
    type Result = FAMProxy;

    fn expects_preserved(&self) -> &'static [TypeId] {
        analysis_preserved!(DominatorTreeAnalysis, ControlFlowGraphAnalysis)
    }

    fn invalidate(&mut self, ir: &Module, preserved: &PreservedAnalyses) {
        let mut fam = self.inner.borrow_mut();

        for func in ir.functions() {
            fam.invalidate(ir.function(func), preserved);
        }
    }

    fn run(&mut self, _: &Module, _: &ModuleAnalysisManager) -> Self::Result {
        Rc::clone(&self.inner)
    }
}
