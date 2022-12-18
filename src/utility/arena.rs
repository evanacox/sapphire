//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

//! A simple typed arena module that does not allow deletion, and allows
//! configurable index sizes for maximum flexibility and performance.
//!
//! Very similar to `id_arena` and other simple typed arena crates, except this
//! one ties in better with the specific needs of this compiler.
//!
//! ```
//! # use sapphire::utility::*;
//!
//! ```

use std::marker::PhantomData;
use std::ops::{Index, IndexMut};

#[cfg(feature = "enable-serde")]
use serde::{Deserialize, Serialize};

/// Models a type that can act as a key for the arena map types.
///
///
pub trait ArenaKey: Copy + Eq {
    type Data;

    fn new(index: usize) -> Self;

    fn index(self) -> usize;
}

/// Creates a type-safe key for a [`PrimaryArenaMap`] and associated data structures.
///
/// This macro allows the inner storage type of the key to be customized, or
/// a default that should always work can be used if the inner type is not specified.
///
/// ```
/// # use sapphire::arena_key;
/// # use sapphire::utility::PrimaryArenaMap;
/// arena_key! {
///     /// We can have doc comments! This one uses the default data type.
///     pub struct EntityRef;
///   
///     // this one is private, and uses u8 as the key type.
///     struct ExtremelyDenseRef(u8);
/// }
///
/// type EntityMap<V> = PrimaryArenaMap<EntityRef, V>;
/// type ExtremelyDenseMap<V> = PrimaryArenaMap<ExtremelyDenseRef, V>;
/// ```
#[macro_export(local_inner_macros)]
macro_rules! arena_key {
    ( $(#[$outer:meta])* $vis:vis struct $name:ident($ty:ty); $($rest:tt)* ) => {
        $(#[$outer])*
        #[repr(transparent)]
        #[derive(Copy, Clone, Default, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
        #[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
        $vis struct $name($ty);

        impl $crate::ArenaKey for $name {
            type Data = $ty;

            fn new(index: usize) -> Self {
                use std::convert::TryFrom;

                $ty::try_from(index)
                    .expect("`Arena` is full, index is not representable with key type")
            }

            fn index(self) -> usize {
                self.0 as usize
            }
        }

        arena_key!($($rest)*);
    };

    ( $(#[$outer:meta])* $vis:vis struct $name:ident; $($rest:tt)* ) => {
        arena_key! { $(#[$outer])* $vis struct $name(usize); $($rest)* }
    };

    () => {}
}

/// Creates a type-safe key for a [`PrimaryArenaMap`] with [`u32`] as the
/// underlying data type. Acts just like [`arena_key`] but with [`u32`] being
/// the default type instead of the unspecified default.
///
/// ```
/// # use sapphire::dense_arena_key;
/// # use sapphire::utility::PrimaryArenaMap;
/// dense_arena_key! {
///     pub struct DenseRef; // data type is u32 now
/// }
///
/// type DenseMapping = PrimaryArenaMap<DenseRef, String>;
/// ```
#[macro_export(local_inner_macros)]
macro_rules! dense_arena_key {
    ( $(#[$outer:meta])* $vis:vis struct $name:ident; $($rest:tt)* ) => {
        arena_key! { $(#[$outer])* $vis struct $name(u32); $($rest)* }
    }
}

/// This is meant to act as a primary mapping of `K -> V`, where `K` is some key
/// type and `V` is the value being stored. Other mappings that use the same
/// key as an existing [`PrimaryArenaMap`] should use [`SecondaryArenaMap`] instead.
///
/// This is effectively a typed wrapper around `Vec<T>`, the main advantage is
/// that it does not implicitly convert into array types (i.e. it actually acts like
/// a map instead of a sequence) and it only allows indexing with the correct type.
///
/// This allows type safety to be significantly increased, with unique key types for
/// different types of collections. Key size can also be customized on a per-map basis,
/// e.g. when a map is known to be small a smaller index type can be used.
///
/// Note that the key type puts an implicit limit on the size of the arena: a key type
/// using `u8` for example cannot store more than `u8::MAX + 1` different objects in the
/// arena, and trying to do so will panic.
///
/// ```
/// # use sapphire::arena_key;
/// # use sapphire::utility::PrimaryArenaMap;
/// arena_key! {
///     pub struct Name;
/// }
///
/// let mut blocks = PrimaryArenaMap::new();
/// let bb: Name = blocks.insert("Hello!");
///
/// assert_eq!(blocks[bb], "Hello!");
/// ```
#[derive(Debug, Clone)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct PrimaryArenaMap<T, K: ArenaKey> {
    data: Vec<T>,
    _unused: PhantomData<fn() -> K>,
}

impl<T, K: ArenaKey> PrimaryArenaMap<T, K> {
    pub fn new() -> Self {
        Self {
            data: Vec::default(),
            _unused: PhantomData::default(),
        }
    }

    pub fn insert(&mut self, value: T) -> K {
        self.data.push(value);

        K::new(self.data.len() - 1)
    }
}

impl<T, K: ArenaKey> Index<K> for PrimaryArenaMap<T, K> {
    type Output = T;

    fn index(&self, key: K) -> &Self::Output {
        &self.data[key.index()]
    }
}

impl<T, K: ArenaKey> IndexMut<K> for PrimaryArenaMap<T, K> {
    fn index_mut(&mut self, key: K) -> &mut Self::Output {
        &mut self.data[key.index()]
    }
}
