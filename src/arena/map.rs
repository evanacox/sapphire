//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::arena;
use crate::arena::{
    iter::{IntoIter, Iter, IterMut, Keys},
    ArenaKey,
};
use std::fmt::{Debug, Formatter};
use std::marker::PhantomData;
use std::ops::{Index, IndexMut};
use std::{fmt, slice};

#[cfg(feature = "enable-serde")]
use serde::{Deserialize, Serialize};

/// This is meant to act as a primary mapping of `K -> V`, where `K` is some key
/// type and `V` is the value being stored. Other mappings that use the same
/// key as an existing [`ArenaMap`] should use [`SecondaryMap`](super::SecondaryMap) instead.
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
/// # use sapphire::arena::ArenaMap;
/// arena_key! {
///     struct Name;
/// }
///
/// let mut blocks = ArenaMap::new();
/// let bb: Name = blocks.insert("Hello!");
///
/// assert_eq!(blocks[bb], "Hello!");
/// ```
#[derive(Clone)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct ArenaMap<K: ArenaKey, V> {
    slots: Vec<V>,
    _unused: PhantomData<fn() -> K>,
}

impl<K: ArenaKey, V> ArenaMap<K, V> {
    /// Creates a new, empty arena. This creates the underlying [`Vec`] with [`Vec::default`].
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// arena_key! { struct Key; }
    /// let mut map = ArenaMap::new();
    /// let k: Key = map.insert("Hello!");
    /// ```
    #[inline]
    pub fn new() -> Self {
        Self {
            slots: Vec::default(),
            _unused: PhantomData::default(),
        }
    }

    /// Creates an empty arena with an initial capacity. This creates the underlying
    /// [`Vec`] with [`Vec::with_capacity`].
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// # arena_key! { struct Key; }
    /// let mut map = ArenaMap::with_capacity(10);
    /// assert!(map.capacity() >= 10);
    /// # let k1: Key = map.insert(5);
    /// ```
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            slots: Vec::with_capacity(capacity),
            _unused: PhantomData::default(),
        }
    }

    /// Checks if the arena contains a given key, i.e. whether a given key
    /// has been returned from [`Self::insert`] at some point.
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// # arena_key! { struct Key; }
    /// let mut map = ArenaMap::default();
    /// let k1: Key = map.insert(true);
    /// let k2 = map.next_key();
    /// assert_eq!(map.contains(k1), true);
    /// assert_eq!(map.contains(k2), false);
    /// ```
    #[inline]
    pub fn contains(&self, key: K) -> bool {
        key.key_index() < self.slots.len()
    }

    /// Accesses the arena and gets the value associated with
    /// a given key. If the key doesn't exist (i.e. if [`Self::contains`]
    /// would have returned `false`, `None` is returned.
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// # arena_key! { struct Key; }
    /// let mut map = ArenaMap::default();
    /// let k1: Key = map.insert(15);
    /// assert_eq!(map.get(k1), Some(&15));
    /// ```
    #[inline]
    pub fn get(&self, key: K) -> Option<&V> {
        self.slots.get(key.key_index())
    }

    /// Accesses the arena and gets the value associated with
    /// a given key. If the key doesn't exist (i.e. if [`Self::contains`]
    /// would have returned `false`, `None` is returned.
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// # arena_key! { struct Key; }
    /// let mut map = ArenaMap::default();
    /// let k1: Key = map.insert(15);
    /// assert_eq!(map.get_mut(k1), Some(&mut 15));
    /// ```
    #[inline]
    pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
        self.slots.get_mut(key.key_index())
    }

    /// Adds an item into the arena, and returns a key that can be used to
    /// access that data later.
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// # arena_key! { struct Key; }
    /// let mut map = ArenaMap::default();
    /// let k: Key = map.insert("Hello!");
    /// assert_eq!(map[k], "Hello!");
    /// ```
    #[inline]
    pub fn insert(&mut self, value: V) -> K {
        self.slots.push(value);

        K::key_new(self.slots.len() - 1)
    }

    /// Gets the key that *will be* returned by [`Self::insert`] when it's
    /// called next. This key is not valid until that [`Self::insert`] call occurs.
    ///
    /// Once that [`Self::insert`] call occurs, the key is equivalent to using the
    /// key returned by [`Self::insert`].
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// # arena_key! { struct Key; }
    /// let mut map = ArenaMap::default();
    /// let k1: Key = map.next_key();
    /// assert_eq!(map.contains(k1), false);
    ///
    /// let k2 = map.insert(0);
    /// assert_eq!(map.contains(k1), true);
    /// assert_eq!(map[k1], 0);
    /// assert_eq!(k1, k2);
    /// ```
    #[inline]
    pub fn next_key(&self) -> K {
        K::key_new(self.slots.len())
    }

    /// Gets the number of elements that have been pushed into the arena.
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// # arena_key! { struct Key; }
    /// let mut map = ArenaMap::<Key, i32>::default();
    /// assert_eq!(map.len(), 0);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.slots.len()
    }

    /// Checks if the arena has had any elements pushed into it.
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// # arena_key! { struct Key; }
    /// let mut map = ArenaMap::<Key, i32>::default();
    /// assert_eq!(map.is_empty(), true);
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.slots.is_empty()
    }

    /// Returns the total number of elements that the arena can hold without
    /// needing to reallocate.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.slots.capacity()
    }

    /// Returns the last element that was inserted in the map.
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// arena_key! { struct Key; }
    /// let mut map = ArenaMap::default();
    /// let k: Key = map.insert(15);
    /// assert_eq!(map.last(), Some((k, &15)));
    /// ```
    #[inline]
    pub fn last(&self) -> Option<(K, &V)> {
        let len = self.slots.len();
        let last = self.slots.last()?;

        Some((K::key_new(len - 1), last))
    }

    /// Returns the last element that was inserted in the map.
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// arena_key! { struct Key; }
    /// let mut map = ArenaMap::default();
    /// let k: Key = map.insert(15);
    /// assert_eq!(map.last_mut(), Some((k, &mut 15)));
    /// ```
    #[inline]
    pub fn last_mut(&mut self) -> Option<(K, &mut V)> {
        let len = self.slots.len();
        let last = self.slots.last_mut()?;

        Some((K::key_new(len - 1), last))
    }

    /// Reserves capacity for at least `additional` more elements to be inserted. This
    /// may potentially reserve much more space depending on the state of the arena.
    ///
    /// See [`Vec::reserve`] for the full behavior.
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        self.slots.reserve(additional)
    }

    /// Reserves the minimum capacity for exactly `additional` more elements to be inserted,
    /// without any potential over-reserving like [`Self::reserve`] does.
    ///
    /// See [`Vec::reserve_exact`] for the full behavior.
    #[inline]
    pub fn reserve_exact(&mut self, additional: usize) {
        self.slots.reserve_exact(additional)
    }

    /// Shrinks the capacity of the arena as much as possible without removing
    /// any elements. The capacity may not actually be reduced to exactly `len()`.
    ///
    /// See [`Vec::shrink_to_fit`] for the full behavior.
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.slots.shrink_to_fit()
    }

    /// Returns an iterator that iterates over the (valid) keys of the arena. Keys
    /// are guaranteed to be yielded in increasing order, in the range $$ [0, L) $$ such
    /// that $$ L $$ is [`len()`](Self::len).
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// arena_key! { struct Key; }
    /// let mut map = ArenaMap::default();
    /// let k1: Key = map.insert(15);
    /// let mut it = map.keys();
    /// assert_eq!(it.next(), Some(k1));
    /// ```
    pub fn keys(&self) -> Keys<K> {
        Keys::with_len(self.slots.len())
    }

    /// Returns an iterator that iterates over the values in the arena.
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// arena_key! { struct Key; }
    /// let mut map = ArenaMap::default();
    /// let k1: Key = map.insert(15);
    /// let mut it = map.values();
    /// assert_eq!(it.next(), Some(&15));
    /// ```
    pub fn values(&self) -> slice::Iter<'_, V> {
        self.slots.as_slice().iter()
    }

    /// Returns an iterator that iterates over the values in the arena,
    /// giving mutable references instead of shared references.
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// arena_key! { struct Key; }
    /// let mut map = ArenaMap::default();
    /// let k1: Key = map.insert(15);
    /// let mut it = map.values_mut();
    /// assert_eq!(it.next(), Some(&mut 15));
    /// ```
    pub fn values_mut(&mut self) -> slice::IterMut<'_, V> {
        self.slots.as_mut_slice().iter_mut()
    }

    /// Returns an iterator that iterates over the values in the arena,
    /// and the keys that map to those values.
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// arena_key! { struct Key; }
    /// let mut map = ArenaMap::default();
    /// let k1: Key = map.insert(15);
    /// let mut it = map.iter();
    /// assert_eq!(it.next(), Some((k1, &15)));
    /// ```
    pub fn iter(&self) -> impl Iterator<Item = (K, &V)> + DoubleEndedIterator + ExactSizeIterator {
        Iter::with_inner(self.values())
    }

    /// Returns an iterator that iterates over the values in the arena,
    /// and the keys that map to those values. Returns mutable references
    /// instead of shared references.
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// arena_key! { struct Key; }
    /// let mut map = ArenaMap::default();
    /// let k1: Key = map.insert(15);
    /// let mut it = map.iter_mut();
    /// assert_eq!(it.next(), Some((k1, &mut 15)));
    /// ```
    pub fn iter_mut(
        &mut self,
    ) -> impl Iterator<Item = (K, &mut V)> + DoubleEndedIterator + ExactSizeIterator {
        IterMut::with_inner(self.values_mut())
    }
}

impl<K: ArenaKey, V> IntoIterator for ArenaMap<K, V> {
    type Item = (K, V);
    type IntoIter = IntoIter<std::vec::IntoIter<V>, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter::with_inner(self.slots.into_iter())
    }
}

impl<K: ArenaKey, V> FromIterator<V> for ArenaMap<K, V> {
    fn from_iter<T: IntoIterator<Item = V>>(iter: T) -> Self {
        Self {
            slots: Vec::from_iter(iter),
            _unused: PhantomData::default(),
        }
    }
}

impl<K: ArenaKey, T> Default for ArenaMap<K, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> PartialEq for ArenaMap<K, V>
where
    K: ArenaKey,
    V: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.values().eq(other.values())
    }
}

impl<K, V> Eq for ArenaMap<K, V>
where
    K: ArenaKey,
    V: Eq,
{
}

impl<K, V> Debug for ArenaMap<K, V>
where
    K: ArenaKey,
    V: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        arena::debug_write_map(f, "ArenaMap", self.iter())
    }
}

impl<K: ArenaKey, T> Index<K> for ArenaMap<K, T> {
    type Output = T;

    fn index(&self, key: K) -> &Self::Output {
        self.slots
            .get(key.key_index())
            .expect("tried to access invalid key on `ArenaMap`")
    }
}

impl<K: ArenaKey, T> IndexMut<K> for ArenaMap<K, T> {
    fn index_mut(&mut self, key: K) -> &mut Self::Output {
        &mut self.slots[key.key_index()]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dense_arena_key;

    dense_arena_key! { struct E; }

    #[test]
    #[should_panic(expected = "tried to access invalid key on `ArenaMap`")]
    fn out_of_bounds() {
        // hide the stack trace, assuming this test panics as it's supposed to.
        std::panic::set_hook(Box::new(|_| {}));

        let mut m1 = ArenaMap::<E, i32>::new();
        let m2 = ArenaMap::<E, i32>::new();

        let k = m1.insert(6);

        let _ = m2[k];
    }

    #[test]
    fn basic() {
        let r0 = E(0);
        let r1 = E(1);
        let m = ArenaMap::<E, isize>::new();

        let v: Vec<E> = m.keys().collect();
        assert_eq!(v, []);

        assert!(!m.contains(r0));
        assert!(!m.contains(r1));
    }

    #[test]
    fn insert() {
        let mut m = ArenaMap::new();
        let k0: E = m.insert(12);
        let k1 = m.insert(33);

        assert_eq!(m[k0], 12);
        assert_eq!(m[k1], 33);
        assert_eq!(&mut m[k1], &mut 33);

        let v: Vec<E> = m.keys().collect();
        assert_eq!(v, [k0, k1]);
    }

    #[test]
    fn next_key() {
        let mut m = ArenaMap::new();
        let k0: E = m.next_key();
        let k1 = m.insert(12);

        assert_eq!(k0, k1);
        assert_eq!(m[k0], m[k1]);
    }

    #[test]
    fn get() {
        let mut m = ArenaMap::new();
        let k0: E = m.insert(12);
        let k1 = m.next_key();

        assert_eq!(m.get(k0), Some(&12));
        assert_eq!(m.get(k1), None);
    }

    #[test]
    fn get_mut() {
        let mut m = ArenaMap::new();
        let k0: E = m.insert(12);
        let k1 = m.next_key();

        assert_eq!(m.get_mut(k0), Some(&mut 12));
        assert_eq!(m.get_mut(k1), None);
    }

    #[test]
    fn len_is_empty() {
        let mut m = ArenaMap::<E, i32>::new();

        assert_eq!(m.len(), 0);
        assert!(m.is_empty());

        m.insert(15);

        assert_eq!(m.len(), 1);
        assert!(!m.is_empty());
    }

    #[test]
    fn reserve() {
        let mut m = ArenaMap::<E, i32>::new();

        m.reserve(15);

        assert!(m.capacity() >= 15);
    }

    #[test]
    fn reserve_exact() {
        let mut m = ArenaMap::<E, i32>::new();

        m.reserve_exact(15);

        assert!(m.capacity() >= 15);
    }

    #[test]
    fn shrink_to_fit() {
        let mut m = ArenaMap::<E, i32>::new();

        for i in 0..10 {
            let _ = m.insert(i);
        }

        m.shrink_to_fit();

        assert!(m.capacity() >= 10);
    }

    #[test]
    fn last() {
        let mut m = ArenaMap::<E, i32>::new();

        assert_eq!(m.last(), None);
        assert_eq!(m.last_mut(), None);

        let _ = m.insert(15);
        let k2 = m.insert(20);

        assert_eq!(m.last(), Some((k2, &20)));
        assert_eq!(m.last_mut(), Some((k2, &mut 20)));
    }

    #[test]
    fn into_iter() {
        let mut m: ArenaMap<E, usize> = ArenaMap::new();

        m.insert(12);
        m.insert(33);

        for (i, (key, value)) in m.into_iter().enumerate() {
            assert_eq!(key.key_index(), i);

            match i {
                0 => assert_eq!(value, 12),
                1 => assert_eq!(value, 33),
                _ => unreachable!(),
            }
        }
    }

    #[test]
    fn iter() {
        let mut m: ArenaMap<E, usize> = ArenaMap::new();

        m.insert(12);
        m.insert(33);

        let mut i = 0;

        for (key, value) in m.iter() {
            assert_eq!(key.key_index(), i);
            match i {
                0 => assert_eq!(*value, 12),
                1 => assert_eq!(*value, 33),
                _ => panic!(),
            }
            i += 1;
        }

        i = 0;

        for (key_mut, value_mut) in m.iter_mut() {
            assert_eq!(key_mut.key_index(), i);
            match i {
                0 => assert_eq!(*value_mut, 12),
                1 => assert_eq!(*value_mut, 33),
                _ => panic!(),
            }
            i += 1;
        }
    }

    #[test]
    fn iter_rev() {
        let mut m: ArenaMap<E, usize> = ArenaMap::new();

        m.insert(12);
        m.insert(33);

        let mut i = 2;
        for (key, value) in m.iter().rev() {
            i -= 1;
            assert_eq!(key.key_index(), i);
            match i {
                0 => assert_eq!(*value, 12),
                1 => assert_eq!(*value, 33),
                _ => panic!(),
            }
        }

        i = 2;

        for (key, value) in m.iter_mut().rev() {
            i -= 1;
            assert_eq!(key.key_index(), i);
            match i {
                0 => assert_eq!(*value, 12),
                1 => assert_eq!(*value, 33),
                _ => panic!(),
            }
        }
    }

    #[test]
    fn keys() {
        let mut m: ArenaMap<E, usize> = ArenaMap::new();

        m.insert(12);
        m.insert(33);

        for (i, key) in m.keys().enumerate() {
            assert_eq!(key.key_index(), i);
        }
    }

    #[test]
    fn keys_rev() {
        let mut m: ArenaMap<E, usize> = ArenaMap::new();
        m.insert(12);
        m.insert(33);

        let mut i = 2;
        for key in m.keys().rev() {
            i -= 1;
            assert_eq!(key.key_index(), i);
        }
    }

    #[test]
    fn values() {
        let mut m: ArenaMap<E, usize> = ArenaMap::new();
        m.insert(12);
        m.insert(33);

        let mut i = 0;

        for value in m.values() {
            match i {
                0 => assert_eq!(*value, 12),
                1 => assert_eq!(*value, 33),
                _ => panic!(),
            }
            i += 1;
        }

        i = 0;

        for value_mut in m.values_mut() {
            match i {
                0 => assert_eq!(*value_mut, 12),
                1 => assert_eq!(*value_mut, 33),
                _ => panic!(),
            }
            i += 1;
        }
    }

    #[test]
    fn values_rev() {
        let mut m: ArenaMap<E, usize> = ArenaMap::new();
        m.insert(12);
        m.insert(33);

        let mut i = 2;
        for value in m.values().rev() {
            i -= 1;
            match i {
                0 => assert_eq!(*value, 12),
                1 => assert_eq!(*value, 33),
                _ => panic!(),
            }
        }
        i = 2;
        for value_mut in m.values_mut().rev() {
            i -= 1;
            match i {
                0 => assert_eq!(*value_mut, 12),
                1 => assert_eq!(*value_mut, 33),
                _ => panic!(),
            }
        }
    }

    #[test]
    fn from_iter() {
        let mut m: ArenaMap<E, usize> = ArenaMap::new();
        m.insert(12);
        m.insert(33);

        let n = m.values().collect::<ArenaMap<E, _>>();

        assert_eq!(m.len(), n.len());

        for (me, ne) in m.values().zip(n.values()) {
            assert_eq!(*me, **ne);
        }
    }

    #[test]
    fn contiguous_keys() {
        let mut m: ArenaMap<E, i32> = ArenaMap::new();
        let mut prev: E = E::key_new(0);

        for i in 0..100 {
            m.insert(i);
        }

        for key in m.keys().skip(1) {
            assert_eq!(prev.key_index(), key.key_index() - 1);

            prev = key;
        }
    }

    #[test]
    fn equal() {
        let mut m1: ArenaMap<E, i32> = ArenaMap::new();
        let mut m2: ArenaMap<E, i32> = ArenaMap::new();

        assert_eq!(m1, m2);

        for i in 0..50 {
            m1.insert(i);
            m2.insert(i);
        }

        assert_eq!(m1, m2);
    }

    #[test]
    fn not_equal() {
        let mut m1: ArenaMap<E, i32> = ArenaMap::new();
        let mut m2: ArenaMap<E, i32> = ArenaMap::new();

        m1.insert(15);

        // empty != non-empty
        assert_ne!(m1, m2);

        m1.insert(20);
        m2.insert(20);
        m2.insert(15);

        // inserted same, diff order
        assert_ne!(m1, m2);
    }

    #[test]
    fn debug() {
        let m1: ArenaMap<E, i32> = {
            let mut m = ArenaMap::new();

            let _ = m.insert(15);
            let _ = m.insert(20);

            m
        };

        {
            let debug_normal = format!("{m1:?}");
            let expected = r#"ArenaMap {E(0): 15, E(1): 20}"#;

            assert_eq!(debug_normal, expected);
        }

        {
            let debug_pretty = format!("{m1:#?}");
            let expected = r#"ArenaMap {
    E(0): 15,
    E(1): 20,
}"#;

            assert_eq!(debug_pretty, expected);
        }
    }
}
