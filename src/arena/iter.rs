//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::arena::ArenaKey;
use std::iter::{Enumerate, Filter, FusedIterator, Map, Zip};
use std::marker::PhantomData;

macro_rules! pair_iter_impl {
    ($name:ident, $t:ty $(, $lt:lifetime)*) => {
        impl<$($lt, )* Inner, K, V> $name<$($lt, )* Inner, K, V>
        where
            Inner: Iterator<Item = $t>,
            K: ArenaKey,
            $(V: $lt)*
        {
            pub(crate) fn with_inner(inner: Inner) -> Self {
                Self {
                    inner: inner.enumerate(),
                    _unused: PhantomData::default()
                }
            }
        }

        impl<$($lt, )* Inner, K, V> Iterator for $name<$($lt, )* Inner, K, V>
        where
            Inner: Iterator<Item = $t>,
            K: ArenaKey,
            $(V: $lt)*
        {
            type Item = (K, $t);

            fn next(&mut self) -> Option<Self::Item> {
                self.inner.next().map(|(i, val)| (K::key_new(i), val))
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                self.inner.size_hint()
            }
        }

        impl<$($lt, )* Inner, K, V> DoubleEndedIterator for $name<$($lt, )* Inner, K, V>
        where
            Inner: Iterator<Item = $t> + DoubleEndedIterator + ExactSizeIterator,
            K: ArenaKey,
            $(V: $lt)*
        {
            fn next_back(&mut self) -> Option<Self::Item> {
                self.inner.next_back().map(|(i, val)| (K::key_new(i), val))
            }
        }

        impl<$($lt, )* Inner, K, V> ExactSizeIterator for $name<$($lt, )* Inner, K, V>
        where
            Inner: Iterator<Item = $t> + ExactSizeIterator,
            K: ArenaKey,
            $(V: $lt)*
        {
            fn len(&self) -> usize {
                self.inner.len()
            }
        }

        impl<$($lt, )* Inner, K, V> FusedIterator for $name<$($lt, )* Inner, K, V>
        where
            Inner: Iterator<Item = $t> + FusedIterator,
            K: ArenaKey,
            $(V: $lt)*
        {}
    }
}

/// Helper type for `.into_iter()` for arena map types
#[derive(Debug)]
pub struct IntoIter<Inner, K, V>
where
    Inner: Iterator<Item = V>,
    K: ArenaKey,
{
    inner: Enumerate<Inner>,
    _unused: PhantomData<fn() -> K>,
}

pair_iter_impl!(IntoIter, V);

/// Helper type for `.iter()` for arena map types
#[derive(Debug)]
pub(crate) struct Iter<'a, Inner, K, V>
where
    Inner: Iterator<Item = &'a V>,
    K: ArenaKey,
    V: 'a,
{
    inner: Enumerate<Inner>,
    _unused: PhantomData<fn() -> K>,
}

pair_iter_impl!(Iter, &'a V, 'a);

/// Helper type for `.iter_mut()` for arena map types
#[derive(Debug)]
pub(crate) struct IterMut<'a, Inner, K, V>
where
    Inner: Iterator<Item = &'a mut V>,
    K: ArenaKey,
    V: 'a,
{
    inner: Enumerate<Inner>,
    _unused: PhantomData<fn() -> K>,
}

pair_iter_impl!(IterMut, &'a mut V, 'a);

/// Provides a way of iterating over all of the keys in a given [`ArenaMap`](crate::arena::ArenaMap).
///
/// ```
/// # use sapphire::arena_key;
/// # use sapphire::arena::*;
/// arena_key! { struct K; }
/// let mut map = ArenaMap::<K, i32>::new();
/// let k1 = map.insert(1);
/// let k2 = map.insert(2);
/// let mut keys = map.keys();
/// assert_eq!(keys.next(), Some(k1));
/// assert_eq!(keys.next(), Some(k2));
/// ```
#[derive(Copy, Clone, Debug)]
pub struct Keys<K: ArenaKey> {
    pos: usize,
    reverse_pos: usize,
    _unused: PhantomData<fn() -> K>,
}

impl<K: ArenaKey> Keys<K> {
    pub(super) fn with_len(len: usize) -> Self {
        Self {
            pos: 0,
            reverse_pos: len,
            _unused: PhantomData::default(),
        }
    }
}

impl<K: ArenaKey> Iterator for Keys<K> {
    type Item = K;

    fn next(&mut self) -> Option<Self::Item> {
        if self.pos < self.reverse_pos {
            self.pos += 1;

            Some(K::key_new(self.pos - 1))
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.reverse_pos - self.pos;

        (size, Some(size))
    }
}

impl<K: ArenaKey> DoubleEndedIterator for Keys<K> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.pos < self.reverse_pos {
            self.reverse_pos -= 1;

            Some(K::key_new(self.reverse_pos))
        } else {
            None
        }
    }
}

impl<K: ArenaKey> ExactSizeIterator for Keys<K> {}

impl<K: ArenaKey> FusedIterator for Keys<K> {}

pub(crate) type BitsetFilterIntoIter<T> = Map<
    Filter<Zip<T, smallbitvec::IntoIter>, fn(&(<T as Iterator>::Item, bool)) -> bool>,
    fn((<T as Iterator>::Item, bool)) -> <T as Iterator>::Item,
>;

pub(crate) type BitsetFilterIter<T, Other> = Map<
    Filter<Zip<T, Other>, fn(&(<T as Iterator>::Item, bool)) -> bool>,
    fn((<T as Iterator>::Item, bool)) -> <T as Iterator>::Item,
>;

pub(crate) trait BitsetFilterIterator: Iterator + Sized {
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
