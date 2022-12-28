//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::arena;
use crate::arena::iter::IntoIter;
use crate::arena::{ArenaKey, ArenaMap};
use ahash::{AHashMap, RandomState};
use std::collections::HashMap;
use std::fmt;
use std::fmt::{Debug, Formatter};
use std::hash::Hash;
use std::iter::Map;
use std::marker::PhantomData;
use std::ops::Index;
use std::rc::Rc;

#[cfg(feature = "enable-serde")]
use serde::{de::SeqAccess, de::Visitor, Deserialize, Deserializer, Serialize, Serializer};

/// Contains a table of immutable, unique elements. All elements are only
/// stored once, no duplicates are stored inside of the arena itself. Lookups
/// by key are almost as efficient as they are in a plain [`ArenaMap`], although
/// an extra pointer dereference must be done.
///
/// This deduplication is paid for by adding hashing overhead to every
/// call to [`Self::insert`], and by requiring values to be stored in an [`Rc<V>`](Rc).
/// This makes them immutable, as allowing them to be mutable would invalidate hashes.
///
/// A very similar API to [`ArenaMap`] is exposed.
pub struct UniqueArenaMap<K, V>
where
    K: ArenaKey,
    V: Eq + Hash,
{
    slots: ArenaMap<K, Rc<V>>,
    dedup: HashMap<Rc<V>, K, RandomState>,
}

impl<K, V> UniqueArenaMap<K, V>
where
    K: ArenaKey,
    V: Hash + Eq,
{
    /// Creates a new arena with nothing in it.
    pub fn new() -> Self {
        Self {
            slots: ArenaMap::default(),
            dedup: AHashMap::default().into(),
        }
    }

    /// Creates the arena with a starting capacity.
    ///
    /// See [`Vec::with_capacity`] for details.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            slots: ArenaMap::with_capacity(capacity),
            dedup: AHashMap::with_capacity(capacity).into(),
        }
    }

    fn with_values(values: Vec<V>) -> Self {
        let mut instance = Self::with_capacity(values.len());

        // assuming `values` is in-order, any pre-existing indices are
        // preserved as necessary for the deserializer
        for v in values {
            instance.insert(v);
        }

        instance
    }

    /// Inserts a value that is either unique or a duplicate of some value
    /// that is already in the arena. If `value` is a duplicate, `value` is dropped
    /// and a key that refers to an equivalent value (i.e. value that compares equal
    /// via [`Eq`] and has the same hash via [`Hash`]) is returned.
    ///
    /// ```
    /// # use sapphire::arena::UniqueArenaMap;
    /// # use sapphire::arena_key;
    /// # use std::rc::Rc;
    /// arena_key! { struct Key; }
    /// let rc = Rc::new(42);
    /// let mut map = UniqueArenaMap::new();
    /// let k1: Key = map.insert(rc.clone()); // original, inserted
    /// let k2: Key = map.insert(rc.clone()); // duplicate, not inserted
    /// assert_eq!(k1, k2);
    /// assert_eq!(Rc::strong_count(&rc), 2); // only 2 refs, `rc` and 1x copy inside the map
    /// ```
    pub fn insert(&mut self, value: V) -> K {
        if let Some(k) = self.dedup.get(&value) {
            return *k;
        }

        let rc = Rc::new(value);
        let new_key = self.slots.insert(rc.clone());

        if self.dedup.insert(rc, new_key).is_some() {
            panic!("re-inserted existing value without being able to find it by lookup")
        }

        new_key
    }

    /// Checks if the arena contains a given key, i.e. whether a given key
    /// has been returned from [`Self::insert`] at some point.
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// # arena_key! { struct Key; }
    /// let mut map = UniqueArenaMap::default();
    /// let k1: Key = map.insert(true);
    /// assert_eq!(map.contains(k1), true);
    /// ```
    #[inline]
    pub fn contains(&self, key: K) -> bool {
        self.slots.contains(key)
    }

    /// Accesses the arena and gets the value associated with
    /// a given key. If the key doesn't exist (i.e. if [`Self::contains`]
    /// would have returned `false`, `None` is returned.
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// # arena_key! { struct Key; }
    /// let mut map = UniqueArenaMap::default();
    /// let k1: Key = map.insert(15);
    /// assert_eq!(map.get(k1), Some(&15));
    /// ```
    #[inline]
    pub fn get(&self, key: K) -> Option<&V> {
        self.slots.get(key).map(|rc| rc.as_ref())
    }

    /// Gets the key that *will be* returned by [`Self::insert`] when it's
    /// called next (with a non-duplicate key). This key is not valid until
    /// that [`Self::insert`] call occurs.
    ///
    /// Once that [`Self::insert`] call occurs, the key is equivalent to using the
    /// key returned by [`Self::insert`].
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// # arena_key! { struct Key; }
    /// let mut map = UniqueArenaMap::default();
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
        K::new(self.slots.len())
    }

    /// Gets the number of elements that have been pushed into the arena.
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// # arena_key! { struct Key; }
    /// let mut map = UniqueArenaMap::<Key, i32>::default();
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
    /// let mut map = UniqueArenaMap::<Key, i32>::default();
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

    /// Returns the last element that was inserted in the map. Note
    /// that this is not necessarily the last *call* to [`Self::insert`], this is
    /// the last element that was actually *inserted* (i.e. the last non-duplicate
    /// element to be inserted).
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// arena_key! { struct Key; }
    /// let mut map = UniqueArenaMap::default();
    /// let k: Key = map.insert(15);
    /// assert_eq!(map.last(), Some((k, &15)));
    /// ```
    #[inline]
    pub fn last(&self) -> Option<(K, &V)> {
        self.slots.last().map(|(k, rc)| (k, rc.as_ref()))
    }

    /// Reserves capacity for at least `additional` more unique elements to be inserted. This
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
    /// let mut map = UniqueArenaMap::default();
    /// let k1: Key = map.insert(15);
    /// let mut it = map.keys();
    /// assert_eq!(it.next(), Some(k1));
    /// ```
    pub fn keys(&self) -> impl Iterator<Item = K> {
        self.slots.keys()
    }

    /// Returns an iterator that iterates over the values in the arena.
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// arena_key! { struct Key; }
    /// let mut map = UniqueArenaMap::default();
    /// let k1: Key = map.insert(15);
    /// let mut it = map.values();
    /// assert_eq!(it.next(), Some(&15));
    /// ```
    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.slots.values().map(|rc| rc.as_ref())
    }

    /// Returns an iterator that iterates over the values in the arena,
    /// and the keys that map to those values.
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// arena_key! { struct Key; }
    /// let mut map = UniqueArenaMap::default();
    /// let k1: Key = map.insert(15);
    /// let mut it = map.iter();
    /// assert_eq!(it.next(), Some((k1, &15)));
    /// ```
    pub fn iter(&self) -> impl Iterator<Item = (K, &V)> {
        self.slots.iter().map(|(k, rc)| (k, rc.as_ref()))
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
struct RcCountError {
    count: usize,
}

impl<K, V> IntoIterator for UniqueArenaMap<K, V>
where
    K: ArenaKey,
    V: Hash + Eq,
{
    type Item = (K, V);
    type IntoIter = Map<IntoIter<std::vec::IntoIter<Rc<V>>, K, Rc<V>>, fn((K, Rc<V>)) -> (K, V)>;

    fn into_iter(self) -> Self::IntoIter {
        // remove the other strong reference to our data so `try_unwrap`
        // won't fail, our type invariants enforce that there are exactly
        // 2 references alive at any given time
        drop(self.dedup);

        self.slots.into_iter().map(|(k, rc)| {
            (
                k,
                Rc::try_unwrap(rc)
                    .map_err(|rc| RcCountError {
                        count: Rc::strong_count(&rc),
                    })
                    .expect("somehow got copy of Rc<V> in UniqueArenaMap"),
            )
        })
    }
}

impl<K, V> Default for UniqueArenaMap<K, V>
where
    K: ArenaKey,
    V: Hash + Eq,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> PartialEq for UniqueArenaMap<K, V>
where
    K: ArenaKey,
    V: Hash + Eq,
{
    fn eq(&self, other: &Self) -> bool {
        self.values().eq(other.values())
    }
}

impl<K, V> Eq for UniqueArenaMap<K, V>
where
    K: ArenaKey,
    V: Hash + Eq,
{
}

impl<K, V> Clone for UniqueArenaMap<K, V>
where
    K: ArenaKey,
    V: Hash + Eq + Clone,
{
    fn clone(&self) -> Self {
        // we can't directly #[derive(Clone)] because of the Rc<V>s
        // that we contain. We need to directly clone the values from inside
        // the arena and re-insert them, and build a new arena/hashmap
        // with completely new Rc<V>s.
        let mut new = Self::with_capacity(self.len());

        for v in self.values() {
            new.insert(v.clone());
        }

        new
    }
}

impl<K, V> Debug for UniqueArenaMap<K, V>
where
    K: ArenaKey,
    V: Debug + Eq + Hash,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        arena::debug_write_map(f, "UniqueArenaMap", self.iter())
    }
}

impl<K, V> Index<K> for UniqueArenaMap<K, V>
where
    K: ArenaKey,
    V: Hash + Eq,
{
    type Output = V;

    fn index(&self, key: K) -> &Self::Output {
        self.slots[key].as_ref()
    }
}

#[cfg(feature = "enable-serde")]
impl<K, V> Serialize for UniqueArenaMap<K, V>
where
    K: ArenaKey,
    V: Hash + Eq + Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        // map it to a sequence of `&str`s, it gets serialized the same way a &[&str] would
        //
        // we need to maintain the order, so indices that are a part of other data
        // structures aren't broken after deserialization
        serializer.collect_seq(self.slots.iter().map(|(_, rc)| rc.as_ref()))
    }
}

#[cfg(feature = "enable-serde")]
struct UniqueArenaMapVisitor<'de, K, V>(PhantomData<fn() -> (K, &'de V)>)
where
    K: ArenaKey,
    V: Hash + Eq + Deserialize<'de>;

#[cfg(feature = "enable-serde")]
impl<'de, K, V> Visitor<'de> for UniqueArenaMapVisitor<'de, K, V>
where
    K: ArenaKey,
    V: Hash + Eq + Deserialize<'de>,
{
    type Value = UniqueArenaMap<K, V>;

    fn expecting(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        write!(formatter, "a sequence of `T` values")
    }

    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        let size = seq.size_hint().unwrap_or(128);
        let mut values = Vec::with_capacity(size);

        // any indices that were deserialized as part of other data structures
        // rely on the order here so we maintain that
        while let Some(value) = seq.next_element()? {
            values.push(value);
        }

        Ok(UniqueArenaMap::with_values(values))
    }
}

#[cfg(feature = "enable-serde")]
impl<'de, K, V> Deserialize<'de> for UniqueArenaMap<K, V>
where
    K: ArenaKey,
    V: Hash + Eq + Deserialize<'de> + 'de,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_seq(UniqueArenaMapVisitor(PhantomData::default()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dense_arena_key;

    dense_arena_key! { struct E; }

    #[test]
    fn returns_same_object() {
        let mut map = UniqueArenaMap::<E, i32>::new();

        let k1 = map.insert(15);
        let k2 = map.insert(15);

        assert_eq!(k1, k2);
        assert!(std::ptr::eq(&map[k1], &map[k2])); // returns reference to same object
    }

    #[test]
    fn doesnt_contain_multiple_copies() {
        let rc = Rc::new(42);
        let mut map = UniqueArenaMap::<E, Rc<i32>>::new();

        for _ in 0..100 {
            let _ = map.insert(rc.clone());
        }

        let k1 = map.insert(rc.clone());
        let k2 = map.insert(rc.clone());

        assert_eq!(k1, k2);
        assert_eq!(Rc::strong_count(&rc), 2);
    }

    #[test]
    fn interface_works() {
        let mut map = UniqueArenaMap::<E, i32>::new();

        let k1 = map.insert(15);
        let k2 = map.insert(12);
        let k3 = map.insert(0);
        let k4 = map.insert(5);
        let k5 = map.insert(15);
        let k6 = map.insert(0);
        let k7 = map.insert(15);
        let k8 = map.insert(12);
        let k9 = map.insert(100);

        assert_eq!(k1, k5);
        assert_eq!(k1, k7);
        assert_eq!(k2, k8);
        assert_eq!(k3, k6);

        assert_ne!(k4, k9);

        assert_eq!(map[k1], 15);
        assert_eq!(map[k2], 12);
        assert_eq!(map[k3], 0);
        assert_eq!(map[k4], 5);
        assert_eq!(map[k9], 100);
    }

    #[cfg(feature = "enable-serde")]
    use serde_test::{assert_tokens, Token};

    #[test]
    #[cfg(feature = "enable-serde")]
    fn deserialize_pool_empty() {
        let pool = UniqueArenaMap::<E, i32>::new();

        assert_tokens(
            &pool,
            &[
                // should just be an empty sequence with a specified length
                Token::Seq { len: Some(0) },
                Token::SeqEnd,
            ],
        );
    }

    #[test]
    #[cfg(feature = "enable-serde")]
    fn deserialize_pool_full() {
        let mut pool = UniqueArenaMap::<E, i32>::new();

        let _ = pool.insert(1);
        let _ = pool.insert(2);
        let _ = pool.insert(3);

        assert_tokens(
            &pool,
            &[
                Token::Seq { len: Some(3) },
                Token::I32(1),
                Token::I32(2),
                Token::I32(3),
                Token::SeqEnd,
            ],
        );
    }
}
