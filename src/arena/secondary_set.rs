//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::arena::iter::Keys;
use crate::arena::{ArenaKey, ArenaMap, BitsetFilterIterator};
use smallbitvec::{sbvec, SmallBitVec};
use std::fmt;
use std::fmt::{Debug, Formatter};
use std::hash::{Hash, Hasher};
use std::iter::{Enumerate, Filter, Map};
use std::marker::PhantomData;

#[cfg(feature = "enable-serde")]
use serde::{
    de, de::MapAccess, de::Visitor, ser::SerializeMap, Deserialize, Deserializer, Serialize,
    Serializer,
};

/// Intended to be a dense representation for a set of keys from a primary map.
///
/// This is theoretically equivalent to a [`SecondaryMap<K, ()>`](crate::arena::SecondaryMap)
/// but is a bit leaner under-the-hood, being implemented as just a bitvector with no additional
/// slot storage.
///
/// ```
/// # use sapphire::arena_key;
/// # use sapphire::arena::*;
/// arena_key! { struct Key; }
/// let mut map = ArenaMap::default();
/// let k1: Key = map.insert(15);
/// let k2 = map.insert(20);
/// let secondary = SecondarySet::map_keys(&map, |m, k| m[k] % 2 == 0);
///
/// assert_eq!(secondary.contains(k1), false);
/// assert_eq!(secondary.contains(k2), true);
/// ```
#[derive(Clone)]
pub struct SecondarySet<K: ArenaKey> {
    bits: SmallBitVec,
    cardinality: usize,
    _unused: PhantomData<fn() -> K>,
}

impl<K: ArenaKey> SecondarySet<K> {
    /// Creates an empty set with `0` as the capacity.
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// arena_key! { struct Key; }
    /// let map = SecondarySet::<Key>::new();
    /// ```
    pub fn new() -> Self {
        Self {
            bits: SmallBitVec::default(),
            cardinality: 0,
            _unused: PhantomData::default(),
        }
    }

    /// Creates an empty set that is pre-allocated for a specific number of keys.
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// arena_key! { struct Key; }
    /// let primary = ArenaMap::<Key, usize>::new();
    /// let map = SecondarySet::<Key>::with_capacity(primary.len());
    /// ```
    pub fn with_capacity(cap: usize) -> Self {
        Self {
            bits: sbvec![false; cap],
            cardinality: 0,
            _unused: PhantomData::default(),
        }
    }

    /// Creates an empty map that is configured for optimal performance
    /// when used with keys from a specific primary [`ArenaMap`].
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// arena_key! { struct Key; }
    /// let primary = ArenaMap::<Key, usize>::new();
    /// let map = SecondarySet::<Key>::with_primary(&primary);
    /// ```
    #[inline]
    pub fn with_primary<T>(primary: &ArenaMap<K, T>) -> Self {
        Self::with_capacity(primary.len())
    }

    /// Efficiently creates a [`SecondarySet`] by applying a function to each key
    /// inside of `primary` to determine if a key should be included in the set or not.
    ///
    /// Effectively, this results in the set $$ { k | f(k) is true } $$
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// arena_key! { struct Key; }
    /// let mut primary = ArenaMap::<Key, i32>::new();
    /// let k1 = primary.insert(4);
    /// let k2 = primary.insert(5);
    ///
    /// let is_even = SecondarySet::map_keys(&primary, |map, key| map[key] % 2 == 0);
    ///
    /// assert_eq!(is_even.contains(k1), true);
    /// assert_eq!(is_even.contains(k2), false);
    /// ```
    pub fn map_keys<T, F>(primary: &ArenaMap<K, T>, mut f: F) -> Self
    where
        F: FnMut(&ArenaMap<K, T>, K) -> bool,
    {
        let mut bits = SmallBitVec::with_capacity(primary.len());
        let mut cardinality = 0;

        for key in primary.keys() {
            bits.push(f(primary, key));

            cardinality += bits.last().unwrap() as usize;
        }

        Self {
            bits,
            cardinality,
            _unused: PhantomData::default(),
        }
    }

    /// Returns the number of keys that are currently in the set.
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// arena_key! { struct Key; }
    /// let mut map = ArenaMap::default();
    /// let k1: Key = map.insert(15);
    /// let k2 = map.insert(20);
    /// let secondary = SecondarySet::map_keys(&map, |m, k| {
    /// eprintln!("{}", m[k]);
    /// m[k] % 2 == 0});
    /// assert_eq!(secondary.cardinality(), 1);
    /// ```
    pub fn cardinality(&self) -> usize {
        self.cardinality
    }

    /// Returns if the set is completely empty.
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// arena_key! { struct Key; }
    /// let mut map = ArenaMap::default();
    /// let k1: Key = map.insert(15);
    /// let k2 = map.insert(17);
    /// let secondary = SecondarySet::map_keys(&map, |m, k| m[k] % 2 == 0);
    /// assert_eq!(secondary.is_empty(), true);
    /// ```
    pub fn is_empty(&self) -> bool {
        self.cardinality == 0
    }

    /// Returns how many keys can be stored in the set without reallocating.
    pub fn capacity(&self) -> usize {
        self.bits.capacity()
    }

    /// Returns whether or not a key is present in the set.
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// arena_key! { struct Key; }
    /// let mut map = ArenaMap::default();
    /// let k1: Key = map.insert(15);
    /// let k2 = map.insert(20);
    /// let mut secondary = SecondarySet::default();
    /// assert_eq!(secondary.insert(k1), false);
    /// assert_eq!(secondary.contains(k1), true);
    /// ```
    pub fn contains(&self, key: K) -> bool {
        // if the key is outside range, it isn't present. if it is, check the bit
        // that we got at the key's index
        self.bits.get(key.key_index()).unwrap_or(false)
    }

    /// Inserts a key into the set, returns whether the key was in the set
    /// prior to insertion.
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// arena_key! { struct Key; }
    /// let mut map = ArenaMap::default();
    /// let k1: Key = map.insert(15);
    /// let k2 = map.insert(20);
    /// let mut secondary = SecondarySet::default();
    /// assert_eq!(secondary.insert(k1), false);
    /// assert_eq!(secondary.contains(k1), true);
    /// ```
    pub fn insert(&mut self, key: K) -> bool {
        let idx = key.key_index();

        // push-like case, going one past what we already have. we just use `push`
        // directly here for optimization purposes
        if idx == self.bits.len() {
            self.bits.push(true);
            self.cardinality += 1;

            return false;
        }

        // case of us inserting outside the range we already have, expand if so
        if idx > self.bits.len() {
            // note that this is not truly **reserving**, this is actually adding
            // new things into our vec as far as the vec itself is concerned.
            // the vec is doing its own reserving internally
            self.bits.resize(idx + self.bits.len() + 1, false);
        }

        let old = self.bits[idx];

        // if old is true we don't want to change cardinality, so we add 0.
        // if it's false, old is 0 and we do want to change, so we add 1
        self.cardinality += !old as usize;
        self.bits.set(idx, true);

        old
    }

    /// Removes a key from the set if it's present, and returns whether or not
    /// a key was removed.
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// arena_key! { struct Key; }
    /// let mut map = ArenaMap::default();
    /// let k1: Key = map.insert(15);
    /// let k2 = map.insert(20);
    /// let mut secondary = SecondarySet::default();
    /// secondary.insert(k1);
    /// assert_eq!(secondary.remove(k1), true);
    /// assert_eq!(secondary.remove(k1), false);
    /// ```
    pub fn remove(&mut self, key: K) -> bool {
        let idx = key.key_index();

        if idx >= self.bits.len() {
            false
        } else {
            let old = self.bits[idx];

            // if the bit was set, we decrease cardinality
            self.cardinality -= old as usize;
            self.bits.set(idx, false);

            old
        }
    }

    /// Removes all keys from the set without deallocating the buffer.
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// arena_key! { struct Key; }
    /// let mut map = ArenaMap::default();
    /// let k1: Key = map.insert(15);
    /// let k2 = map.insert(20);
    /// let mut secondary = SecondarySet::default();
    /// secondary.insert(k1);
    /// secondary.clear();
    /// assert_eq!(secondary.contains(k1), false);
    /// ```
    pub fn clear(&mut self) {
        for i in 0..self.bits.len() {
            self.bits.set(i, false);
        }
    }

    /// Returns an iterator that iterates over the keys that are present in the set. Keys
    /// are guaranteed to be yielded in increasing order, in the range $$ [0, C) $$ such
    /// that $$ C $$ is [`cardinality()`](Self::cardinality).
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// arena_key! { struct Key; }
    /// let mut map = ArenaMap::default();
    /// let k1: Key = map.insert(15);
    /// let k2 = map.insert(20);
    /// let secondary = SecondarySet::map_keys(&map, |m, k| m[k] % 2 != 0);
    /// let mut it = secondary.keys();
    /// assert_eq!(it.next(), Some(k1));
    /// assert_eq!(it.next(), None);
    /// ```
    pub fn keys(&self) -> impl Iterator<Item = K> + '_ {
        Keys::with_len(self.bits.len())
            // we don't want to yield invalid keys
            .filter_uninitialized_slots(self.bits.iter())
    }
}

impl<K: ArenaKey> Default for SecondarySet<K> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: ArenaKey> Debug for SecondarySet<K> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "SecondarySet ")?;

        f.debug_list().entries(self.keys()).finish()
    }
}

impl<K: ArenaKey> PartialEq for SecondarySet<K> {
    fn eq(&self, other: &Self) -> bool {
        if self.cardinality() != other.cardinality() {
            return false;
        }

        let mut current = 0;

        for (b1, b2) in self.bits.iter().zip(other.bits.iter()) {
            if current == self.cardinality() {
                break;
            }

            if b1 && b2 {
                current += 1;
            }
        }

        current == self.cardinality()
    }
}

impl<K: ArenaKey> Eq for SecondarySet<K> {}

impl<K: ArenaKey> Hash for SecondarySet<K> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // again, terrible but you shouldn't use this anyway
        for (i, bit) in self.bits.iter().enumerate() {
            if bit {
                state.write_usize(i);
            }
        }
    }
}

type SecondarySetInner<K> = Map<
    Filter<Enumerate<smallbitvec::IntoIter>, fn(&(usize, bool)) -> bool>,
    fn((usize, bool)) -> K,
>;

pub struct SecondarySetIntoIter<K: ArenaKey> {
    inner: SecondarySetInner<K>,
    _unused: PhantomData<fn() -> K>,
}

impl<K: ArenaKey> Iterator for SecondarySetIntoIter<K> {
    type Item = K;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

impl<K: ArenaKey> IntoIterator for SecondarySet<K> {
    type Item = K;
    type IntoIter = SecondarySetIntoIter<K>;

    fn into_iter(self) -> Self::IntoIter {
        let filter = (|(_, init)| *init) as fn(&(usize, bool)) -> bool;
        let mapper = (|(idx, _)| K::key_new(idx)) as fn((usize, bool)) -> Self::Item;

        SecondarySetIntoIter {
            inner: self.bits.into_iter().enumerate().filter(filter).map(mapper),
            _unused: PhantomData::default(),
        }
    }
}

#[cfg(feature = "enable-serde")]
impl<K: ArenaKey> Serialize for SecondarySet<K> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut state = serializer.serialize_map(Some(3))?;
        let keys: Vec<usize> = self
            .bits
            .iter()
            .enumerate()
            .filter(|(_, bit)| *bit)
            .map(|(i, _)| i)
            .collect();

        state.serialize_entry("cardinality", &self.cardinality)?;
        state.serialize_entry("highest", &keys.last().copied().unwrap_or(0))?;
        state.serialize_entry("keys", &keys)?;

        state.end()
    }
}

#[cfg(feature = "enable-serde")]
struct SecondarySetVisitor<K: ArenaKey>(PhantomData<fn() -> K>);

#[cfg(feature = "enable-serde")]
impl<'de, K: ArenaKey> Visitor<'de> for SecondarySetVisitor<K> {
    type Value = SecondarySet<K>;

    fn expecting(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "expecting a SecondarySet made up of `cardinality`, `"
        )
    }

    fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
    where
        A: MapAccess<'de>,
    {
        let cardinality: usize = match map.next_entry()? {
            Some((s, cardinality)) => {
                let field: String = s;

                if field != "cardinality" {
                    return Err(de::Error::missing_field("cardinality"));
                }

                cardinality
            }
            _ => return Err(de::Error::missing_field("cardinality")),
        };

        let highest: usize = match map.next_entry()? {
            Some((s, highest)) => {
                let field: String = s;

                if field != "highest" {
                    return Err(de::Error::missing_field("highest"));
                }

                highest
            }
            _ => return Err(de::Error::missing_field("highest")),
        };

        let keys: Vec<usize> = match map.next_entry()? {
            Some((s, keys)) => {
                let field: String = s;

                if field != "keys" {
                    return Err(de::Error::missing_field("keys"));
                }

                keys
            }
            _ => return Err(de::Error::missing_field("keys")),
        };

        let mut bits = SmallBitVec::default();
        bits.resize(highest + 1, false);

        for key in keys {
            bits.set(key, true);
        }

        Ok(SecondarySet {
            bits,
            cardinality,
            _unused: PhantomData::default(),
        })
    }
}

#[cfg(feature = "enable-serde")]
impl<'de, K: ArenaKey> Deserialize<'de> for SecondarySet<K> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_map(SecondarySetVisitor(PhantomData::default()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dense_arena_key;

    dense_arena_key! { struct E; }

    #[test]
    fn empty() {
        let m2 = SecondarySet::<E>::new();

        assert_eq!(m2.cardinality(), 0);
        assert!(m2.is_empty());
    }

    #[test]
    fn insert_consecutive() {
        let mut m1 = ArenaMap::new();
        let mut m2 = SecondarySet::<E>::new();

        let k1 = m1.insert("Hello!");
        let k2 = m1.insert("Goodbye!");
        let k3 = m1.insert("Foo!");

        assert_eq!(m2.cardinality(), 0);
        assert!(m2.is_empty());

        m2.insert(k1);
        m2.insert(k2);
        m2.insert(k3);

        assert!(m2.contains(k1));
        assert!(m2.contains(k2));
        assert!(m2.contains(k3));

        assert_eq!(m2.cardinality(), 3);
    }

    #[test]
    fn insert_random() {
        let mut m1 = ArenaMap::new();
        let mut m2 = SecondarySet::<E>::new();

        for name in 0..1000 {
            let _ = m1.insert(name);
        }

        let k1 = m1.insert(1000);

        // this should create slots to hold the previous 1000 elements,
        // but not actually have any of them initialized.
        m2.insert(k1);

        assert!(m2.contains(k1));

        assert_eq!(m2.cardinality(), 1);
        assert!(!m2.is_empty());

        // other keys should remain invalid
        for key in m1.keys().filter(|k| *k != k1) {
            assert!(!m2.contains(key));
        }
    }

    #[test]
    fn insert_exists() {
        let mut m1 = ArenaMap::new();
        let mut m2 = SecondarySet::<E>::new();

        let k1 = m1.insert(5);

        // should work as normal
        assert!(!m2.insert(k1));
        assert!(m2.contains(k1));

        // should return true now that it's in the set
        assert!(m2.insert(k1));
    }

    #[test]
    fn remove() {
        let mut m1 = ArenaMap::new();
        let mut m2 = SecondarySet::<E>::new();

        let k1 = m1.insert(5);
        let k2 = m1.insert(10);
        let k3 = m1.insert(15);

        m2.insert(k3);

        // key should stop existing after its removed
        assert!(m2.remove(k3));
        assert!(!m2.contains(k3));

        // others never existed, should be none
        assert!(!m2.remove(k2));
        assert!(!m2.remove(k1));
    }

    #[test]
    fn keys() {
        let mut m1 = ArenaMap::new();
        let mut m2 = SecondarySet::<E>::new();

        let k1 = m1.insert(5);
        let _k2 = m1.insert(10);
        let k3 = m1.insert(15);

        m2.insert(k1);
        m2.insert(k3);

        let mut it = m2.keys();

        assert_eq!(it.next(), Some(k1));
        assert_eq!(it.next(), Some(k3));
        assert_eq!(it.next(), None);
    }

    #[cfg(feature = "enable-serde")]
    use serde_test::{assert_tokens, Token};

    #[test]
    #[cfg(feature = "enable-serde")]
    fn deserialize_pool_empty() {
        let secondary = SecondarySet::<E>::new();

        assert_tokens(
            &secondary,
            &[
                Token::Map { len: Some(3) },
                Token::Str("cardinality"),
                Token::U64(0),
                Token::Str("highest"),
                Token::U64(0),
                Token::Str("keys"),
                Token::Seq { len: Some(0) },
                Token::SeqEnd,
                Token::MapEnd,
            ],
        );
    }

    #[test]
    #[cfg(feature = "enable-serde")]
    fn deserialize_pool_full() {
        let mut primary = ArenaMap::new();
        let mut secondary = SecondarySet::<E>::new();

        let _: E = primary.insert(1);
        let k2: E = primary.insert(2);
        let _ = primary.insert(3);

        secondary.insert(k2);

        assert_tokens(
            &secondary,
            &[
                Token::Map { len: Some(3) },
                Token::Str("cardinality"),
                Token::U64(1),
                Token::Str("highest"),
                Token::U64(1),
                Token::Str("keys"),
                Token::Seq { len: Some(1) },
                Token::U64(1),
                Token::SeqEnd,
                Token::MapEnd,
            ],
        );
    }
}
