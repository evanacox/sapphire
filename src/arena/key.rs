//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use std::fmt::Debug;

/// Models a type that can act as a key for the arena map types.
///
/// This arena key can have a configurable size, and can lead to panics if
/// the underlying data type is too small to represent a given index.
///
/// Note that in most cases this trait should not be implemented directly,
/// prefer to use the [`arena_key`](crate::arena_key) or [`dense_arena_key`](crate::dense_arena_key)
/// macros that provide the implementation for you.
pub trait ArenaKey: Copy + Eq + Debug {
    /// The underlying data type of the key.
    type Item;

    /// Creates a new key from a given arena index. This should do any necessary
    /// conversions to convert a `usize` index into the internal storage type,
    /// ideally the conversion should be lossless.
    ///
    /// This should check that the index is in the bounds of its internal storage
    /// type, but this is not *required* for safety. It will just be harder to
    /// track down bugs when indexes overflow and end up referring to the wrong
    /// key instead of panicking.
    fn new(index: usize) -> Self;

    /// Converts the internal storage type into a `usize` index.
    ///
    /// This conversion should be lossless.
    fn index(self) -> usize;
}

/// Creates a type-safe key for a [`ArenaMap`](crate::arena::ArenaMap) and associated data structures.
///
/// This macro allows the inner storage type of the key to be customized, or
/// a default that should always work can be used if the inner type is not specified.
///
/// ```
/// # use sapphire::arena_key;
/// # use sapphire::arena::ArenaMap;
/// arena_key! {
///     /// We can have doc comments! This one uses the default data type.
///     pub struct EntityRef;
///   
///     // this one is private, and uses u8 as the key type.
///     struct ExtremelyDenseRef(u8);
/// }
///
/// type EntityMap<V> = ArenaMap<EntityRef, V>;
/// type ExtremelyDenseMap<V> = ArenaMap<ExtremelyDenseRef, V>;
/// ```
#[macro_export(local_inner_macros)]
macro_rules! arena_key {
    ( $(#[$outer:meta])* $vis:vis struct $name:ident($ty:ty); $($rest:tt)* ) => {
        $(#[$outer])*
        #[repr(transparent)]
        #[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
        #[cfg_attr(feature = "enable-serde", derive(serde::Serialize, serde::Deserialize))]
        $vis struct $name($ty);

        impl $crate::arena::ArenaKey for $name {
            type Item = $ty;

            #[inline]
            fn new(index: usize) -> Self {
                use std::convert::TryInto;

                Self(index.try_into().expect("index is not representable with key type"))
            }

            #[inline]
            fn index(self) -> usize {
                self.0 as usize
            }
        }

        impl ::std::fmt::Debug for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
                std::write!(f, "{}({})", std::stringify!($name), self.0)
            }
        }

        arena_key!($($rest)*);
    };

    ( $(#[$outer:meta])* $vis:vis struct $name:ident; $($rest:tt)* ) => {
        arena_key! { $(#[$outer])* $vis struct $name(usize); $($rest)* }
    };

    () => {}
}

/// Creates a type-safe key for a [`ArenaMap`](crate::arena::ArenaMap) with [`u32`] as the
/// underlying data type. Acts just like [`arena_key`] but with [`u32`] being
/// the default type instead of the unspecified default.
///
/// Note that this also implements `Packable` with the highest value of `u32`
/// being reserved.
///
/// ```
/// # use sapphire::dense_arena_key;
/// # use sapphire::arena::ArenaMap;
/// dense_arena_key! {
///     pub struct DenseRef; // data type is u32 now
/// }
///
/// type DenseMapping = ArenaMap<DenseRef, String>;
/// ```
#[macro_export(local_inner_macros)]
macro_rules! dense_arena_key {
    ( $(#[$outer:meta])* $vis:vis struct $name:ident; $($rest:tt)* ) => {
        arena_key! { $(#[$outer])* $vis struct $name(u32); }

        impl $crate::utility::Packable for $name {
            #[inline]
            fn reserved() -> Self {
                Self(u32::MAX)
            }

            #[inline]
            fn is_reserved(&self) -> bool {
                self.0 == u32::MAX
            }
        }

        dense_arena_key!($($rest)*);
    };

    () => {}
}

#[cfg(test)]
mod tests {
    use crate::arena::*;
    use crate::utility::Packable;
    use crate::{arena_key, dense_arena_key};
    use static_assertions::assert_eq_size;

    #[test]
    fn reserved_key_works() {
        dense_arena_key! { struct K; }

        let mut map = ArenaMap::<K, i32>::default();

        let k1 = map.insert(15);
        let k2 = map.insert(32);
        let k3 = K::reserved();

        assert!(k3.is_reserved());
        assert!(!k2.is_reserved());
        assert!(!k1.is_reserved());
    }

    #[test]
    fn arena_key_default_is_usize() {
        arena_key! { struct Key; }

        assert_eq_size!(Key, usize);
    }

    #[test]
    fn dense_arena_key_is_u32() {
        dense_arena_key! { struct Key; }

        assert_eq_size!(Key, u32);
    }

    #[test]
    fn arena_key_non_default_uses_type_provided() {
        arena_key! { struct Key(u16); }

        assert_eq_size!(Key, u16);
    }

    #[test]
    fn can_use_arena_key_default_in_map() {
        arena_key! { struct Key; }

        let mut map = ArenaMap::new();
        let k1: Key = map.insert(1);
        let k2: Key = map.insert(2);
        let k3: Key = map.insert(3);

        assert_eq!(map[k1], 1);
        assert_eq!(map[k2], 2);
        assert_eq!(map[k3], 3);
    }

    #[test]
    fn can_use_arena_key_non_default_in_map() {
        arena_key! { struct Key(u16); }

        let mut map = ArenaMap::new();
        let k1: Key = map.insert(1);
        let k2: Key = map.insert(2);
        let k3: Key = map.insert(3);

        assert_eq!(map[k1], 1);
        assert_eq!(map[k2], 2);
        assert_eq!(map[k3], 3);
    }

    #[test]
    fn can_use_dense_arena_key_in_map() {
        dense_arena_key! { struct Key; }

        let mut map = ArenaMap::new();
        let k1: Key = map.insert(1);
        let k2: Key = map.insert(2);
        let k3: Key = map.insert(3);

        assert_eq!(map[k1], 1);
        assert_eq!(map[k2], 2);
        assert_eq!(map[k3], 3);
    }

    #[test]
    #[should_panic(expected = "index is not representable with key type")]
    fn arena_key_bounds_causes_panic() {
        // hide the stack trace, assuming this test panics as it's supposed to.
        std::panic::set_hook(Box::new(|_| {}));

        arena_key! { struct Key(u8); }

        let mut map = ArenaMap::new();

        // 1 past what u8 can represent
        for i in 0..=256 {
            let k: Key = map.insert(i);

            assert_eq!(map[k], i);
        }
    }

    #[test]
    fn arena_key_larger_does_not_cause_panic() {
        arena_key! { struct Key(u16); }

        let mut map = ArenaMap::new();

        for i in 0..256 {
            let k: Key = map.insert(i);

            assert_eq!(map[k], i);
        }
    }
}
