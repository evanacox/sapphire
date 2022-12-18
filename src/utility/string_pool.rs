//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use ahash::AHashMap;
use std::fmt::{Formatter, Result as FmtResult};
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
/// assert_eq!(pool[s], "Hello!");
/// ```
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct Str(u32);

/// Contains a number of heap-allocated strings, and provides an API to
/// map [`Str`]s to those heap-allocated strings.
///
#[derive(Debug, Clone)]
pub struct StringPool {
    // basic idea: we store strings inside `strings`, and we map strings to indices
    // inside of `refs`. we use this to de-duplicate strings
    strings: Vec<Rc<str>>,
    refs: AHashMap<Rc<str>, Str>,
}

impl StringPool {
    pub fn new() -> Self {
        Self {
            strings: Vec::default(),
            refs: AHashMap::default(),
        }
    }

    fn with_strings(strings: &[&str]) -> Self {
        let mut instance = Self::new();

        // assuming `strings` is in-order, any pre-existing indices are
        // preserved as necessary for the deserializer
        for string in strings {
            instance.insert(*string);
        }

        instance
    }

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
        self.refs
            .insert(boxed, Str(index as u32))
            .expect("re-inserted existing value without being able to find it by lookup")
    }

    ///
    ///
    ///
    pub fn get(&self, index: Str) -> Option<&str> {
        self.strings.get(index.0 as usize).map(|rc| rc.as_ref())
    }
}

impl Default for StringPool {
    fn default() -> Self {
        Self::new()
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

struct StringPoolVisitor;

#[cfg(feature = "enable-serde")]
impl<'de> Visitor<'de> for StringPoolVisitor {
    type Value = StringPool;

    fn expecting<'fmt>(&self, formatter: &mut Formatter<'fmt>) -> FmtResult {
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
