//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::utility::Packable;
use ahash::AHashMap;
use std::fmt;
use std::ops::Index;
use std::rc::Rc;

#[cfg(feature = "enable-serde")]
use serde::{de::SeqAccess, de::Visitor, Deserialize, Deserializer, Serialize, Serializer};

/// A reference to a string inside of a given [`StringPool`]. These are
/// significantly more compact than both [`String`]s and `&str`s, and are
/// thus better for usage inside IR storage where space is precious.
///
/// They must be resolved to real strings through [`StringPool::get`] or
/// the index operator, and can only be safely obtained through [`StringPool::insert`].
///
/// ```
/// # use sapphire::utility::*;
/// let mut pool = StringPool::new();
/// let s = pool.insert("Hello!");
///
/// assert_eq!(&pool[s], "Hello!");
/// ```
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct Str(pub(crate) u32); // `pub` specifically for shoving `Str`s into `Value`s, see block.rs

impl Packable for Str {
    fn reserved() -> Self {
        Self(u32::MAX)
    }

    fn is_reserved(&self) -> bool {
        self.0 == u32::MAX
    }
}

/// Contains a number of heap-allocated strings, and provides an API to
/// map [`Str`]s to those heap-allocated strings. All strings are automatically
/// de-duplicated internally, so two [`Str`]s from two calls to [`Self::insert`] with the
/// same string value will be equivalent.
///
/// Note that a pool provides no protection against using [`Str`]s for
/// the wrong pool, as for data compactness reasons that is simply not stored.
///
/// ```
/// # use sapphire::utility::*;
/// let mut pool = StringPool::new();
///
/// let k1 = pool.insert("Hello!");
/// let k2 = pool.insert("Goodbye!");
///
/// assert_eq!(&pool[k1], "Hello!");
/// assert_eq!(&pool[k2], "Goodbye!");
///
/// let k3 = pool.insert("Hello!");
/// assert_eq!(k1, k3);
/// assert_eq!(&pool[k1], "Hello!");
/// ```
#[derive(Debug, Clone)]
pub struct StringPool {
    // this is effectively a specialization of UniqueArenaMap, we need to do it this
    // way specifically because we're dealing in dynamically sized types and UniqueArenaMap
    // doesn't support those.
    strings: Vec<Rc<str>>,
    refs: AHashMap<Rc<str>, Str>,
}

impl StringPool {
    /// Creates an empty string pool that has no valid indices
    /// into it.
    ///
    /// ```
    /// # use sapphire::utility::*;
    /// let pool = StringPool::new();
    /// ```
    pub fn new() -> Self {
        Self {
            strings: Vec::default(),
            refs: AHashMap::default(),
        }
    }

    // provides a way to initialize a pool with a pre-set list of strings
    // and the implied valid indices from that. this is only for use
    // with deserialization
    fn with_strings(strings: &[String]) -> Self {
        let mut instance = Self::new();

        // assuming `strings` is in-order, any pre-existing indices are
        // preserved as necessary for the deserializer
        for string in strings {
            instance.insert(string.as_str());
        }

        instance
    }

    /// Inserts a string into the pool and returns a reference
    /// that can be used to access the string.
    ///
    /// ```
    /// # use sapphire::utility::*;
    /// let mut pool = StringPool::new();
    /// let name = pool.insert("John Smith");
    /// assert_eq!(&pool[name], "John Smith");
    /// ```
    pub fn insert(&mut self, string: &str) -> Str {
        if let Some(s) = self.refs.get(string) {
            return *s;
        }

        // let string put the data on the heap for us, then we copy it into
        // an rc that we actually store inside our map/vec. this avoids duplicating
        // any potentially very large strings, while still giving us hash lookups with `&str`
        let owned = String::from(string);
        let boxed = Rc::from(owned.into_boxed_str());
        let index = self.strings.len();

        // for whatever reason, compiler can't infer that `boxed` is an `Rc<str>`
        // just from the `Rc::from(Box<str>)`  call earlier. need this to disambiguate
        self.strings.push((&boxed as &Rc<str>).clone());

        if self.refs.insert(boxed, Str(index as u32)).is_some() {
            panic!("re-inserted existing value without being able to find it by lookup")
        }

        Str(index as u32)
    }

    /// Gets the string at a given `Str` index. If the index somehow doesn't exist,
    /// `None` is returned.
    ///
    /// ```
    /// # use sapphire::utility::StringPool;
    /// let mut pool = StringPool::new();
    /// let s1 = pool.insert("one");
    /// assert_eq!(pool.get(s1), Some("one"));
    /// ```
    pub fn get(&self, index: Str) -> Option<&str> {
        self.strings.get(index.0 as usize).map(|rc| rc.as_ref())
    }

    /// Provides an iterator over all of the strings that are in the pool.
    ///
    /// ```
    /// # use sapphire::utility::StringPool;
    /// let mut pool = StringPool::new();
    /// let _ = pool.insert("Hello!");
    /// let mut it = pool.values();
    /// assert_eq!(it.next(), Some("Hello!"));
    /// ```
    pub fn values(&self) -> impl Iterator<Item = &str> {
        self.strings.iter().map(|rc| rc.as_ref())
    }

    /// Returns the number of unique strings stored inside the pool.
    ///
    /// ```
    /// # use sapphire::utility::StringPool;
    /// let mut pool = StringPool::new();
    /// pool.insert("a");
    /// pool.insert("b");
    /// pool.insert("b");
    /// assert_eq!(pool.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        self.strings.len()
    }

    /// Checks if the pool contains any strings.
    ///
    /// ```
    /// # use sapphire::utility::StringPool;
    /// let mut pool = StringPool::new();
    /// assert_eq!(pool.is_empty(), true);
    /// ```
    pub fn is_empty(&self) -> bool {
        self.strings.is_empty()
    }
}

impl Default for StringPool {
    fn default() -> Self {
        Self::new()
    }
}

impl PartialEq for StringPool {
    fn eq(&self, other: &Self) -> bool {
        let pool1 = self.values();
        let pool2 = other.values();

        pool1.eq(pool2)
    }
}

impl Index<Str> for StringPool {
    type Output = str;

    fn index(&self, index: Str) -> &Self::Output {
        self.strings[index.0 as usize].as_ref()
    }
}

#[cfg(feature = "enable-serde")]
impl Serialize for StringPool {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        // map it to a sequence of `&str`s, it gets serialized the same way a &[&str] would
        //
        // we need to maintain the order, so indices that are a part of other data
        // structures aren't broken after deserialization
        serializer.collect_seq(self.strings.iter().map(|rc| rc.as_ref()))
    }
}

#[cfg(feature = "enable-serde")]
struct StringPoolVisitor;

#[cfg(feature = "enable-serde")]
impl<'de> Visitor<'de> for StringPoolVisitor {
    type Value = StringPool;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "a sequence of `str` values")
    }

    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        let size = seq.size_hint().unwrap_or(128);
        let mut values = Vec::with_capacity(size);

        // we just deserialize a sequence of `&str`s and then do our magic
        // outside of that.
        //
        // any indices that were deserialized as part of other data structures
        // rely on the order here so we maintain that
        while let Some(value) = seq.next_element()? {
            values.push(value);
        }

        Ok(StringPool::with_strings(&values))
    }
}

#[cfg(feature = "enable-serde")]
impl<'de> Deserialize<'de> for StringPool {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_seq(StringPoolVisitor)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default() {
        let pool = StringPool::new();

        assert_eq!(pool.len(), 0);
        assert_eq!(pool.is_empty(), true);
    }

    #[test]
    fn invalid_index() {
        let mut pool1 = StringPool::new();
        let pool2 = StringPool::new();

        let s1 = pool1.insert("Hello!");

        // pool2 doesn't have that index, invalid
        assert_eq!(pool2.get(s1), None);
        assert_eq!(pool1.get(s1), Some("Hello!"));
    }

    #[test]
    fn deduplicated() {
        let mut pool = StringPool::new();

        let s1 = pool.insert("one");
        let s2 = pool.insert("one");
        let s3 = pool.insert("two");

        assert_eq!(s1, s2);
        assert_ne!(s1, s3);
        assert_eq!(&pool[s1], "one");
        assert_eq!(&pool[s2], "one");
        assert_eq!(&pool[s3], "two");
        assert_eq!(pool.len(), 2);
    }

    #[cfg(feature = "enable-serde")]
    use serde_test::{assert_tokens, Token};

    #[test]
    #[cfg(feature = "enable-serde")]
    fn deserialize_pool_empty() {
        let pool = StringPool::new();

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
        let mut pool = StringPool::new();

        let _ = pool.insert("one");
        let _ = pool.insert("two");
        let _ = pool.insert("three");

        assert_tokens(
            &pool,
            &[
                // should just be an empty sequence with a specified length
                Token::Seq { len: Some(3) },
                Token::Str("one"),
                Token::Str("two"),
                Token::Str("three"),
                Token::SeqEnd,
            ],
        );
    }
}
