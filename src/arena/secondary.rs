//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::arena::iter::{Iter, IterMut, Keys};
use crate::arena::{ArenaKey, ArenaMap};
use smallbitvec::{sbvec, SmallBitVec};
use std::fmt::{Debug, Formatter};
use std::iter::{Enumerate, Filter, Map, Zip};
use std::marker::PhantomData;
use std::mem;
use std::mem::MaybeUninit;
use std::ops::{Index, IndexMut};
use std::{fmt, iter};

use crate::arena;
#[cfg(feature = "enable-serde")]
use serde::{
    de::MapAccess, de::Visitor, ser::SerializeMap, Deserialize, Deserializer, Serialize, Serializer,
};

/// Intended to be a dense secondary mapping `K -> V` for keys from a primary [`ArenaMap`]. This
/// is to associate extra data with most (but ideally *all*) keys from a given `PrimaryMap`.
///
/// While the map *does* track insertion information in a dense bitset, this is not intended to
/// map only a few keys, as this map stores space for every mapping just like [`ArenaMap`] does. If
/// you anticipate only needing a few keys to be mapped and most not being mapped, use
/// TODO instead.
///
/// The map also allows random insertion, but optimal performance is best obtained through
/// using a combination of [`map_all_keys`](SecondaryMap::map_all_keys) and
/// [`map_some_keys`](SecondaryMap::map_some_keys).
///
/// ```
/// # use sapphire::arena_key;
/// # use sapphire::arena::*;
/// arena_key! { struct Player; }
///
/// // p1 => John, p2 => Bob
/// let mut players = ArenaMap::new();
/// let p1: Player = players.insert("John");
/// let p2 = players.insert("Bob");
///
/// // nice way to quickly do a map over all keys in `players`
/// let mut health = SecondaryMap::map_all_keys(&players, |_, _| 200);
///
/// // alternatively, you can do the insertions manually.
/// let mut ammo = SecondaryMap::with_primary(&players);
///
/// for k in players.keys() {
///   ammo.insert(k, 50);
/// }
///
/// assert_eq!(players[p1], "John");
/// assert_eq!(health[p2], 200);
/// assert_eq!(ammo[p1], 50);
/// ```
///
/// The underlying implementation is a [`Vec`] storing [`MaybeUninit<V>`](`std::mem::MaybeUninit`)s
/// along with information keeping track of which vec slots are inserted (and therefore initialized).
/// That [`Vec`] expands if a key is inserted that doesn't fit in the current [`Vec`], this is
/// what the "capacity" of the container is. The length is simply how many elements are initialized.
pub struct SecondaryMap<K: ArenaKey, V> {
    slots: Vec<MaybeUninit<V>>,
    initialized: SmallBitVec,
    len: usize,
    _unused: PhantomData<fn() -> K>,
}

impl<K: ArenaKey, V> SecondaryMap<K, V> {
    /// Creates an empty map with `0` as the capacity.
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// arena_key! { struct Key; }
    /// let map = SecondaryMap::<Key, i32>::new();
    /// ```
    #[inline]
    pub fn new() -> Self {
        Self {
            slots: Vec::default(),
            initialized: SmallBitVec::default(),
            len: 0,
            _unused: PhantomData::default(),
        }
    }

    /// Creates an empty map that is configured for optimal performance
    /// when used with keys from a specific primary [`ArenaMap`].
    ///
    /// See [`Self::reserve`] for details on how capacity works in a [`SecondaryMap`].
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// arena_key! { struct Key; }
    /// let primary = ArenaMap::<Key, usize>::new();
    /// let map = SecondaryMap::<Key, i32>::with_primary(&primary);
    /// ```
    pub fn with_primary<T>(primary: &ArenaMap<K, T>) -> Self {
        // we don't require V to implement Copy, so we can't use the clone variant of `vec!`
        let it = iter::repeat_with(|| MaybeUninit::uninit()).take(primary.len());

        Self {
            slots: Vec::from_iter(it),
            initialized: sbvec![false; primary.len()],
            len: 0,
            _unused: PhantomData::default(),
        }
    }

    /// Efficiently creates a [`SecondaryMap`] by applying a function to each key
    /// inside of `primary` and inserting the result.
    ///
    /// Effectively, this results on a mapping of `K -> f(K)`.
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// arena_key! { struct Key; }
    /// let mut primary = ArenaMap::new();
    /// let k1: Key = primary.insert(4);
    /// let k2 = primary.insert(16);
    ///
    /// let map = SecondaryMap::map_all_keys(&primary, |map, key| map[key] * 2);
    ///
    /// assert_eq!(map[k1], 8);
    /// assert_eq!(map[k2], 32);
    /// ```
    pub fn map_all_keys<T, F>(primary: &ArenaMap<K, T>, mut f: F) -> Self
    where
        F: FnMut(&ArenaMap<K, T>, K) -> V,
    {
        let mut slots = Vec::with_capacity(primary.len());
        let mut initialized = SmallBitVec::with_capacity(primary.len());

        for key in primary.keys() {
            slots.push(MaybeUninit::new(f(primary, key)));
            initialized.push(true);
        }

        Self {
            slots,
            initialized,
            len: primary.len(),
            _unused: PhantomData::default(),
        }
    }

    /// Efficiently creates a [`SecondaryMap`] by applying a function to each key
    /// inside of `primary` and inserting the result. The difference between this
    /// and [`Self::map_all_keys`] is that the mapping can skip over some keys.
    ///
    /// Effectively, this results on a mapping of `K -> f(K)` for all `K` where
    /// `f(K) != None`
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// arena_key! { struct Key; }
    /// let mut primary = ArenaMap::new();
    /// let k1: Key = primary.insert(4);
    /// let k2 = primary.insert(5);    
    ///
    /// let map = SecondaryMap::map_some_keys(&primary, |map, key| {
    ///     match map[key] {
    ///         x if x % 2 == 0 => None,
    ///         x => Some(x * 2)
    ///     }   
    /// });
    ///
    /// assert_eq!(map[k2], 10);
    /// assert_eq!(map.contains(k1), false);
    /// ```
    pub fn map_some_keys<T, F>(primary: &ArenaMap<K, T>, mut f: F) -> Self
    where
        F: FnMut(&ArenaMap<K, T>, K) -> Option<V>,
    {
        let mut slots = Vec::with_capacity(primary.len());
        let mut initialized = SmallBitVec::with_capacity(primary.len());
        let mut count = 0;

        for key in primary.keys() {
            debug_assert_eq!(key.index(), slots.len());

            match f(primary, key) {
                Some(val) => {
                    slots.push(MaybeUninit::new(val));
                    initialized.push(true);
                    count += 1;
                }
                None => {
                    slots.push(MaybeUninit::uninit());
                    initialized.push(false);
                }
            }
        }

        Self {
            slots,
            initialized,
            len: count,
            _unused: PhantomData::default(),
        }
    }

    /// Checks if the map contains a value for a given key.
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// arena_key! { struct Key; }
    /// let mut primary = ArenaMap::new();
    /// let mut secondary = SecondaryMap::new();
    /// let k1: Key = primary.insert("Hello!");
    /// secondary.insert(k1, 16);
    ///
    /// assert_eq!(secondary.contains(k1), true);
    /// ```
    pub fn contains(&self, key: K) -> bool {
        self.is_initialized(key)
    }

    /// Inserts a key/value pair into the table, mapping `key -> value`.
    ///
    /// If there is already a value mapped to `key` in the table, that
    /// value is returned. Otherwise, [`None`] is returned.
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// arena_key! { struct Key; }
    /// let mut primary = ArenaMap::new();
    /// let mut secondary = SecondaryMap::new();
    /// let k1: Key = primary.insert("Hello!");
    ///
    /// assert_eq!(secondary.insert(k1, 16), None); // no previous value
    /// assert_eq!(secondary.insert(k1, 13), Some(16)); // got previous
    /// ```
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let idx = key.index();

        // push-like case, going one past what we already have. we just use `push`
        // directly here for optimization purposes
        if idx == self.slots.len() {
            self.slots.push(MaybeUninit::new(value));
            self.initialized.push(true);
            self.len += 1;

            return None;
        }

        // case of us inserting outside the range we already have, expand if so
        if idx > self.slots.len() {
            // note that this is not truly **reserving**, this is actually adding
            // new things into our vec as far as the vec itself is concerned.
            // the vec is doing its own reserving internally
            self.reserve(idx - self.slots.len() + 1);
        }

        // regardless of the slot's state, we need to replace the value.
        if self.is_initialized(key) {
            // if it's already initialized we take the current value out
            // and insert the new value. no need to update bitset.
            let current = unsafe { self.slots[idx].assume_init_mut() };
            let old = mem::replace(current, value);

            Some(old)
        } else {
            // otherwise, mark the slot is initialized and insert the value
            self.initialized.set(idx, true);
            self.slots[idx] = MaybeUninit::new(value);
            self.len += 1;

            None
        }
    }

    /// Gets a value out of the map if the key has been previously added with [`Self::insert`].
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// arena_key! { struct Key; }
    /// let mut primary = ArenaMap::new();
    /// let mut secondary = SecondaryMap::new();
    /// let k1: Key = primary.insert("Hello!");
    ///
    /// secondary.insert(k1, 13);
    ///
    /// assert_eq!(secondary.get(k1), Some(&13));
    /// ```
    pub fn get(&self, key: K) -> Option<&V> {
        self.get_slot(key)
            .map(|slot| unsafe { slot.assume_init_ref() })
    }

    /// Gets a value out of the map if the key has been previously added with [`Self::insert`].
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// arena_key! { struct Key; }
    /// let mut primary = ArenaMap::new();
    /// let mut secondary = SecondaryMap::new();
    /// let k1: Key = primary.insert("Hello!");
    ///
    /// secondary.insert(k1, 13);
    ///
    /// assert_eq!(secondary.get_mut(k1), Some(&mut 13));
    /// ```
    pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
        self.get_slot_mut(key)
            .map(|slot| unsafe { slot.assume_init_mut() })
    }

    /// Removes a key from the table and returns the value that was at
    /// that key, if it existed. If the key isn't in the table, [`None`] is returned.
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// arena_key! { struct Key; }
    /// let mut primary = ArenaMap::new();
    /// let mut secondary = SecondaryMap::new();
    /// let k1: Key = primary.insert("Hello!");
    /// secondary.insert(k1, 13);
    ///
    /// assert_eq!(secondary.take(k1), Some(13));
    /// assert_eq!(secondary.take(k1), None);
    /// ```
    pub fn take(&mut self, key: K) -> Option<V> {
        match self.get_slot_mut(key) {
            Some(value) => {
                // get the old, initialized value (as a MaybeUninit) and replace it with an uninit value
                let old = mem::replace(value, MaybeUninit::uninit());

                // mark it uninitialized so future reads dont get uninit
                self.initialized.set(key.index(), false);

                // return the value
                Some(unsafe { old.assume_init() })
            }
            None => None,
        }
    }

    /// Informs the map of how big the primary arena is.
    ///
    /// Unlike a [`Vec`], the capacity is not quite the number of *elements* that can be
    /// stored without re-allocating, although it often is. The capacity is a measure of the highest
    /// key value that can be inserted without reallocating, i.e. how big the map thinks that
    /// the *primary* arena is.
    ///
    /// If the primary map has gained more elements, the secondary map should have that new length
    /// reserved.
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// arena_key! { struct Key; }
    /// let primary = ArenaMap::<Key, i32>::new();
    /// let mut map = SecondaryMap::<Key, isize>::new();
    /// map.reserve(primary.len());
    /// ```
    #[cold]
    pub fn reserve(&mut self, additional: usize) {
        let range = 0..additional;

        // add `additional` uninitialized values / false-s to "reserve" space. `extend` will
        // reserve the underlying vec internally, so we aren't just extending by 1 constantly.
        self.initialized.extend(range.clone().map(|_| false));
        self.slots.extend(range.map(|_| MaybeUninit::uninit()));
    }

    /// Shrinks the underlying capacity of the arena as much as possible without removing
    /// any slots. Note that this will not reduce [`Self::capacity`], as a [`SecondaryMap`]'s capacity
    /// is not the same thing as a [`Vec`]'s capacity. See [`Self::reserve`] for more details.  
    ///
    /// See [`Vec::shrink_to_fit`] for the full behavior.
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        // self.initialized does not have shrink_to_fit
        self.slots.shrink_to_fit();
    }

    /// Returns how big the map believes that the primary arena is.
    ///
    /// See [`Self::reserve`] for details on what exactly this means.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.slots.len()
    }

    /// Returns the number of values that have been inserted into this map, i.e.
    /// the number of keys that have associated values.
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// arena_key! { struct Key; }
    /// let mut map = SecondaryMap::<Key, i32>::new();
    /// assert_eq!(map.len(), 0);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Checks if the map has any values in it, i.e. if any key/value pairs
    /// have been inserted.
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// arena_key! { struct Key; }
    /// let mut map = SecondaryMap::<Key, i32>::new();
    /// assert_eq!(map.is_empty(), true);
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
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
    pub fn keys(&self) -> impl Iterator<Item = K> + '_ {
        Keys::with_len(self.slots.len())
            // we don't want to yield invalid keys either
            .filter_uninitialized_slots(self.initialized.iter())
    }

    /// Returns an iterator that iterates over the values in the arena.
    ///
    /// ```
    /// # use sapphire::arena_key;
    /// # use sapphire::arena::*;
    /// arena_key! { struct Key; }
    /// let mut map = ArenaMap::default();
    /// let k1: Key = map.insert(15);
    /// let secondary = SecondaryMap::map_all_keys(&map, |m, k| m[k] * 2);
    /// let mut it = secondary.values();
    /// assert_eq!(it.next(), Some(&30));
    /// ```
    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.slots
            .as_slice()
            .iter()
            .filter_uninitialized_slots(self.initialized.iter())
            .map(|val| unsafe { val.assume_init_ref() })
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
    /// let mut secondary = SecondaryMap::map_all_keys(&map, |m, k| m[k] * 2);
    /// let mut it = secondary.values_mut();
    /// assert_eq!(it.next(), Some(&mut 30));
    /// ```
    pub fn values_mut(&mut self) -> impl Iterator<Item = &mut V> {
        self.slots
            .as_mut_slice()
            .iter_mut()
            .filter_uninitialized_slots(self.initialized.iter())
            .map(|val| unsafe { val.assume_init_mut() })
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
    /// let mut secondary = SecondaryMap::with_primary(&map);
    /// secondary.insert(k1, 'c');
    /// let mut it = secondary.iter();
    /// assert_eq!(it.next(), Some((k1, &'c')));
    /// ```
    pub fn iter(&self) -> impl Iterator<Item = (K, &V)> {
        // already filtered by `self.values()`
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
    pub fn iter_mut(&mut self) -> impl Iterator<Item = (K, &mut V)> {
        // already filtered by `self.values()`
        IterMut::with_inner(self.values_mut())
    }

    #[inline]
    fn is_initialized(&self, key: K) -> bool {
        // note that capacity may be wildly different because of the different
        // implementations between a `SmallBitVec` and a `Vec`
        debug_assert_eq!(self.initialized.len(), self.slots.len());

        self.initialized.get(key.index()) == Some(true)
    }

    #[inline]
    fn is_index_initialized(&self, index: usize) -> bool {
        // note that capacity may be wildly different because of the different
        // implementations between a `SmallBitVec` and a `Vec`
        debug_assert_eq!(self.initialized.len(), self.slots.len());

        self.initialized.get(index) == Some(true)
    }

    #[inline]
    fn get_slot(&self, key: K) -> Option<&MaybeUninit<V>> {
        if self.is_initialized(key) {
            Some(&self.slots[key.index()])
        } else {
            None
        }
    }

    #[inline]
    fn get_slot_mut(&mut self, key: K) -> Option<&mut MaybeUninit<V>> {
        if self.is_initialized(key) {
            Some(&mut self.slots[key.index()])
        } else {
            None
        }
    }
}

impl<K: ArenaKey, V> Index<K> for SecondaryMap<K, V> {
    type Output = V;

    fn index(&self, index: K) -> &Self::Output {
        self.get(index)
            .expect("tried to access invalid key on `SecondaryMap`")
    }
}

impl<K: ArenaKey, V> IndexMut<K> for SecondaryMap<K, V> {
    fn index_mut(&mut self, index: K) -> &mut Self::Output {
        self.get_mut(index)
            .expect("tried to access invalid key on `SecondaryMap`")
    }
}

impl<K: ArenaKey, V> Clone for SecondaryMap<K, V>
where
    V: Clone,
{
    fn clone(&self) -> Self {
        let mut copy = Self {
            slots: Vec::with_capacity(self.slots.len()),
            initialized: self.initialized.clone(),
            len: self.len(),
            _unused: PhantomData::default(),
        };

        for (slot, init) in iter::zip(self.slots.iter(), self.initialized.iter()) {
            copy.slots.push(if init {
                let obj = unsafe { slot.assume_init_ref() };

                MaybeUninit::new(obj.clone())
            } else {
                MaybeUninit::uninit()
            })
        }

        copy
    }
}

impl<K: ArenaKey, V> Default for SecondaryMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> PartialEq for SecondaryMap<K, V>
where
    K: ArenaKey,
    V: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        // need to check that keys are equal too
        self.iter().eq(other.iter())
    }
}

impl<K, V> Eq for SecondaryMap<K, V>
where
    K: ArenaKey,
    V: Eq,
{
}

impl<K, V> Debug for SecondaryMap<K, V>
where
    K: ArenaKey,
    V: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        arena::write_map(f, "SecondaryMap", self.iter())
    }
}

impl<K: ArenaKey, V> IntoIterator for SecondaryMap<K, V> {
    type Item = (K, V);
    type IntoIter = Map<
        Enumerate<BitsetFilterIntoIter<std::vec::IntoIter<MaybeUninit<V>>>>,
        fn((usize, MaybeUninit<V>)) -> (K, V),
    >;

    fn into_iter(self) -> Self::IntoIter {
        self.slots
            .into_iter()
            .filter_uninitialized_slots(self.initialized.into_iter())
            .enumerate()
            .map(|(i, val)| (K::new(i), unsafe { val.assume_init() }))
    }
}

type BitsetFilterIntoIter<T> = Map<
    Filter<Zip<T, smallbitvec::IntoIter>, fn(&(<T as Iterator>::Item, bool)) -> bool>,
    fn((<T as Iterator>::Item, bool)) -> <T as Iterator>::Item,
>;

type BitsetFilterIter<T, Other> = Map<
    Filter<Zip<T, Other>, fn(&(<T as Iterator>::Item, bool)) -> bool>,
    fn((<T as Iterator>::Item, bool)) -> <T as Iterator>::Item,
>;

trait BitsetFilterIterator: Iterator + Sized {
    fn filter_uninitialized_slots<Other: Iterator<Item = bool>>(
        self,
        bits: Other,
    ) -> BitsetFilterIter<Self, Other> {
        // for whatever reason, rust nightly won't do the implicit conversion even though
        // the conversion itself is safe since there's no closure state. i have no idea
        let filter = (|(_, init)| *init) as fn(&(Self::Item, bool)) -> bool;
        let mapper = (|(val, _)| val) as fn((Self::Item, bool)) -> Self::Item;

        // we carry alongside the bitset iterator, and go slot by slot
        // alongside the rest of the iterator and just filter ones where the bitset is 0
        // bitset 0 at slot => slot is uninitialized, 1 => initialized
        self //
            .zip(bits)
            .filter(filter)
            .map(mapper)
    }
}

impl<T: Iterator> BitsetFilterIterator for T {}

#[cfg(feature = "enable-serde")]
impl<K: ArenaKey, V> Serialize for SecondaryMap<K, V>
where
    V: Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let collected_bits: Vec<bool> = self.initialized.iter().collect();
        let collected_refs: Vec<&V> = self
            .slots
            .iter()
            .enumerate()
            .filter(|(i, _)| self.is_index_initialized(*i))
            .map(|(_, val)| unsafe { val.assume_init_ref() })
            .collect();

        let mut state = serializer.serialize_map(Some(2))?;

        state.serialize_entry("bits", &collected_bits)?;
        state.serialize_entry("slots", &collected_refs)?;

        state.end()
    }
}

#[cfg(feature = "enable-serde")]
struct SecondaryMapVisitor<K: ArenaKey, V>(PhantomData<fn() -> (K, V)>);

#[cfg(feature = "enable-serde")]
impl<'de, K: ArenaKey, V> Visitor<'de> for SecondaryMapVisitor<K, V>
where
    V: Deserialize<'de>,
{
    type Value = SecondaryMap<K, V>;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "expecting a SecondaryMap made up of a sequence of `bool`s and a sequence of `V`s"
        )
    }

    fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
    where
        A: MapAccess<'de>,
    {
        use serde::de;

        let bits: Vec<bool> = match map.next_entry()? {
            Some((s, bits)) => {
                let field: String = s;

                if field != "bits" {
                    return Err(de::Error::missing_field("bits"));
                }

                bits
            }
            _ => return Err(de::Error::missing_field("bits")),
        };

        let elements: Vec<V> = match map.next_entry()? {
            Some((s, slots)) => {
                let field: String = s;

                if field != "slots" {
                    return Err(de::Error::missing_field("slots"));
                }

                slots
            }
            _ => return Err(de::Error::missing_field("slots")),
        };

        // get our data into the form stored by the secondary map
        let initialized = SmallBitVec::from_iter(bits.into_iter());
        let mut slots = Vec::<MaybeUninit<V>>::new();
        let len = elements.len();

        // make the slots be the correct size so we can start taking elements from `elements`
        slots.resize_with(initialized.len(), || MaybeUninit::uninit());

        let mut elem_it = elements.into_iter();

        for (i, is_initialized) in initialized.iter().enumerate() {
            if is_initialized {
                slots[i] = match elem_it.next() {
                    Some(val) => MaybeUninit::new(val),
                    None => return Err(de::Error::custom("`bits` should have the same number of true values as `slots` has values in total"))
                };
            }
        }

        Ok(SecondaryMap {
            slots,
            initialized,
            len,
            _unused: PhantomData::default(),
        })
    }
}

#[cfg(feature = "enable-serde")]
impl<'de, K: ArenaKey, V> Deserialize<'de> for SecondaryMap<K, V>
where
    V: Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_map(SecondaryMapVisitor(PhantomData::default()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dense_arena_key;

    dense_arena_key! { struct E; }

    #[test]
    #[should_panic(expected = "tried to access invalid key on `SecondaryMap`")]
    fn out_of_bounds() {
        // hide the stack trace, assuming this test panics as it's supposed to.
        std::panic::set_hook(Box::new(|_| {}));

        let mut m1 = ArenaMap::<E, i32>::new();
        let m2 = SecondaryMap::<E, i64>::new();

        let k = m1.insert(6);

        m2[k];
    }

    #[test]
    fn empty() {
        let m2 = SecondaryMap::<E, i64>::new();

        assert_eq!(m2.len(), 0);
        assert_eq!(m2.capacity(), 0);
        assert_eq!(m2.is_empty(), true);
    }

    #[test]
    fn insert_consecutive() {
        let mut m1 = ArenaMap::new();
        let mut m2 = SecondaryMap::<E, i64>::new();

        let k1 = m1.insert("Hello!");
        let k2 = m1.insert("Goodbye!");
        let k3 = m1.insert("Foo!");

        assert_eq!(m2.capacity(), 0);
        assert_eq!(m2.len(), 0);
        assert_eq!(m2.is_empty(), true);

        m2.insert(k1, 13);
        m2.insert(k2, 14);
        m2.insert(k3, 15);

        assert_eq!(m2[k1], 13);
        assert_eq!(m2[k2], 14);
        assert_eq!(m2[k3], 15);

        assert_eq!(m2.len(), 3);
    }

    #[test]
    fn insert_random() {
        let mut m1 = ArenaMap::new();
        let mut m2 = SecondaryMap::<E, isize>::new();

        for name in 0..1000 {
            let _ = m1.insert(name);
        }

        let k1 = m1.insert(1000);

        // this should create slots to hold the previous 1000 elements,
        // but not actually have any of them initialized.
        m2.insert(k1, -6);

        assert_eq!(m2[k1], -6);
        assert_eq!(m2.contains(k1), true);

        assert_eq!(m2.len(), 1);
        assert_eq!(m2.capacity(), 1001);
        assert_eq!(m2.is_empty(), false);

        // other keys should remain invalid
        for key in m1.keys().filter(|k| *k != k1) {
            assert_eq!(m2.contains(key), false);
        }
    }

    #[test]
    fn insert_exists() {
        let mut m1 = ArenaMap::new();
        let mut m2 = SecondaryMap::<E, isize>::new();

        let k1 = m1.insert(5);

        m2.insert(k1, 100);

        // should work as normal
        assert_eq!(m2[k1], 100);

        // should return old value and replace with the new one
        assert_eq!(m2.insert(k1, 200), Some(100));
        assert_eq!(m2[k1], 200);
    }

    #[test]
    fn take_removes() {
        let mut m1 = ArenaMap::new();
        let mut m2 = SecondaryMap::<E, isize>::new();

        let k1 = m1.insert(5);
        let k2 = m1.insert(10);
        let k3 = m1.insert(15);

        m2.insert(k3, 100);

        // key should stop existing after its removed
        assert_eq!(m2.take(k3), Some(100));
        assert_eq!(m2.contains(k3), false);

        // should be none now, key doesnt exist anymore
        assert_eq!(m2.take(k3), None);

        // others never existed, should be none
        assert_eq!(m2.take(k2), None);
        assert_eq!(m2.take(k1), None);
    }

    #[test]
    fn keys() {
        let mut m1 = ArenaMap::new();
        let mut m2 = SecondaryMap::<E, isize>::new();

        let _k1 = m1.insert(5);
        let _k2 = m1.insert(10);
        let k3 = m1.insert(15);

        m2.insert(k3, 10);

        let mut it = m2.keys();

        assert_eq!(it.next(), Some(k3));
        assert_eq!(it.next(), None);
    }

    #[cfg(feature = "enable-serde")]
    use serde_test::{assert_tokens, Token};

    #[test]
    #[cfg(feature = "enable-serde")]
    fn deserialize_pool_empty() {
        let secondary = SecondaryMap::<E, i32>::new();

        assert_tokens(
            &secondary,
            &[
                Token::Map { len: Some(2) },
                Token::Str("bits"),
                Token::Seq { len: Some(0) },
                Token::SeqEnd,
                Token::Str("slots"),
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
        let mut secondary = SecondaryMap::<E, i32>::new();

        let _: E = primary.insert(1);
        let k2: E = primary.insert(2);
        let _ = primary.insert(3);

        secondary.insert(k2, 2);

        assert_tokens(
            &secondary,
            &[
                Token::Map { len: Some(2) },
                Token::Str("bits"),
                Token::Seq { len: Some(2) },
                Token::Bool(false),
                Token::Bool(true),
                Token::SeqEnd,
                Token::Str("slots"),
                Token::Seq { len: Some(1) },
                Token::I32(2),
                Token::SeqEnd,
                Token::MapEnd,
            ],
        );
    }
}
