//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::arena::PackableKey;
use std::fmt::{Debug, Formatter, Result};
use std::mem;

#[cfg(feature = "enable-serde")]
use serde::{Deserialize, Serialize};

/// Helper trait for a type that can be packed into a `PackedOption`.
///
/// These types need to have some null-ish value that they can reserve,
/// that value will be used to distinguish between `None` and `Some`.
///
/// ```
/// # use sapphire::utility::*;
/// struct NonZero(i32);
///
/// impl Packable for NonZero {
///     fn reserved_null() -> Self {
///         NonZero(0)
///     }
///
///     fn is_reserved_null(&self) -> bool {
///         self.0 == 0
///     }
/// }
///
/// let opt = PackedOption::some(NonZero(15));
///
/// assert_eq!(opt.is_some(), true);
/// ```
pub trait Packable {
    /// Gets the reserved value of the type.
    ///
    /// This value is not meant to be constructed normally in any circumstances.
    fn reserved_null() -> Self;

    /// Checks if the current object is equivalent to the constant
    /// returned by [`Self::reserved_null`].
    fn is_reserved_null(&self) -> bool;
}

impl<K: PackableKey> Packable for K {
    #[inline]
    fn reserved_null() -> Self {
        Self::reserved()
    }

    #[inline]
    fn is_reserved_null(&self) -> bool {
        self.is_reserved()
    }
}

/// Provides an [`Option`]-like type for (valid) keys into `SlotMap`s without
/// paying any extra cost to store the flag. It takes up exactly as much
/// space as the key would on its own, while also storing whether or not
/// the key actually exists.
///
/// Relies on the null state of a key to distinguish between "none" and "some",
///
#[derive(Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Hash)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct PackedOption<T: Packable>(T);

impl<T: Packable> PackedOption<T> {
    /// Creates a `None` instance of `PackedOption`.
    ///
    /// ```
    /// # use sapphire::utility::*;
    /// # use sapphire::dense_arena_key;
    /// dense_arena_key! { struct Key; }
    /// let null = PackedOption::<Key>::none();
    /// assert_eq!(null.is_none(), true);
    /// ```
    #[inline]
    pub fn none() -> Self {
        Self(T::reserved_null())
    }

    /// Creates a `Some` instance of `PackedOption`.
    ///
    /// ```
    /// # use sapphire::utility::*;
    /// # struct NonZero(i32);
    /// # impl Packable for NonZero {
    /// #    fn reserved_null() -> Self {
    /// #        NonZero(0)
    /// #    }    
    /// #    fn is_reserved_null(&self) -> bool {     
    /// #        self.0 == 0
    /// #     }
    /// # }
    /// let opt = PackedOption::some(NonZero(15));
    /// assert_eq!(opt.is_some(), true);
    /// ```
    #[inline]
    pub fn some(value: T) -> Self {
        assert!(!value.is_reserved_null());

        Self(value)
    }

    /// Returns `true` if the packed option is a `None` value.
    ///
    /// ```
    /// # use sapphire::utility::*;
    /// # use sapphire::dense_arena_key;
    /// dense_arena_key! { struct Key; }
    /// let null = PackedOption::<Key>::none();
    /// assert_eq!(null.is_none(), true);
    /// ```
    #[inline]
    pub fn is_none(&self) -> bool {
        self.0.is_reserved_null()
    }

    /// Returns `true` if the packed option is a `Some` value.
    ///
    /// ```
    /// # use sapphire::utility::*;
    /// # use sapphire::dense_arena_key;
    /// dense_arena_key! { struct Key; }
    /// let null = PackedOption::<Key>::none();
    /// assert_eq!(null.is_some(), false);
    /// ```
    #[inline]
    pub fn is_some(&self) -> bool {
        !self.is_none()
    }

    /// Expand the packed option into a normal `Option` that can
    /// be pattern-matched on as expected.
    ///
    /// ```
    /// # use sapphire::utility::*;
    /// # use sapphire::dense_arena_key;
    /// dense_arena_key! { struct K; }
    /// let null = PackedOption::<K>::none();
    /// assert_eq!(null.expand_ref(), None);
    /// ```
    #[inline]
    pub fn expand_ref(&self) -> Option<&T> {
        if self.is_none() {
            None
        } else {
            Some(&self.0)
        }
    }

    /// Expand the packed option into a normal `Option` that can
    /// be pattern-matched on as expected.
    ///
    /// ```
    /// # use sapphire::utility::*;
    /// # use sapphire::dense_arena_key;
    /// dense_arena_key! { struct K; }
    /// let null = PackedOption::<K>::none();
    /// assert_eq!(null.expand(), None);
    /// ```
    #[inline]
    pub fn expand(self) -> Option<T> {
        if self.is_none() {
            None
        } else {
            Some(self.0)
        }
    }

    /// Maps a `PackedOption<T>` to `Option<U>` by applying a function to a contained value.
    ///
    /// ```
    /// # use sapphire::utility::*;
    /// # use sapphire::dense_arena_key;
    /// dense_arena_key! { struct Key; }
    /// let null = PackedOption::<Key>::none();
    /// assert_eq!(null.expand(), None);
    /// ```
    #[inline]
    pub fn map<U, F>(self, f: F) -> Option<U>
    where
        F: FnOnce(T) -> U,
    {
        self.expand().map(f)
    }

    /// Unwrap a packed `Some` value or panic.
    ///
    /// ```
    /// # use sapphire::utility::*;
    /// # #[derive(Debug, Eq, PartialEq, Ord, PartialOrd)]
    /// # struct NotZero(i32);
    /// # impl Packable for NotZero {
    /// #    fn reserved_null() -> Self {
    /// #        NotZero(0)
    /// #    }    
    /// #    fn is_reserved_null(&self) -> bool {     
    /// #        self.0 == 0
    /// #     }
    /// # }
    /// let opt = PackedOption::some(NotZero(15));
    /// assert_eq!(opt.unwrap(), NotZero(15));
    /// ```
    #[inline]
    pub fn unwrap(self) -> T {
        self.expand().unwrap()
    }

    /// Unwrap a packed `Some` value or panic.
    ///
    /// ```
    /// # use sapphire::utility::*;
    /// # #[derive(Debug, Eq, PartialEq, Ord, PartialOrd)]
    /// # struct NotZero(i32);
    /// # impl Packable for NotZero {
    /// #    fn reserved_null() -> Self {
    /// #        NotZero(0)
    /// #    }    
    /// #    fn is_reserved_null(&self) -> bool {     
    /// #        self.0 == 0
    /// #     }
    /// # }
    /// let opt = PackedOption::some(NotZero(15));
    /// assert_eq!(opt.expect("what?"), NotZero(15));
    /// ```
    #[inline]
    pub fn expect(self, msg: &str) -> T {
        self.expand().expect(msg)
    }

    /// Takes the value out of the packed option, leaving a `None` in its place.
    /// ```
    /// # use sapphire::utility::*;
    /// # #[derive(Debug, Eq, PartialEq, Ord, PartialOrd)]
    /// # struct NotZero(i32);
    /// # impl Packable for NotZero {
    /// #    fn reserved_null() -> Self {
    /// #        NotZero(0)
    /// #    }    
    /// #    fn is_reserved_null(&self) -> bool {     
    /// #        self.0 == 0
    /// #     }
    /// # }
    /// let mut opt = PackedOption::some(NotZero(15));
    /// assert_eq!(opt.take(), Some(NotZero(15)));
    /// assert_eq!(opt.is_none(), true);
    /// assert_eq!(opt.take(), None);
    /// ```
    #[inline]
    pub fn take(&mut self) -> Option<T> {
        mem::replace(self, None.into()).expand()
    }
}

impl<T: Packable> Default for PackedOption<T> {
    fn default() -> Self {
        Self::none()
    }
}

impl<T: Packable> From<Option<T>> for PackedOption<T> {
    fn from(opt: Option<T>) -> Self {
        match opt {
            None => Self::none(),
            Some(t) => Self::some(t),
        }
    }
}

impl<T: Packable> From<PackedOption<T>> for Option<T> {
    fn from(value: PackedOption<T>) -> Self {
        value.expand()
    }
}

impl<T> Debug for PackedOption<T>
where
    T: Packable + Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        self.expand_ref().fmt(f)
    }
}

#[cfg(test)]
mod test {
    use crate::arena::ArenaMap;
    use crate::dense_arena_key;
    use crate::utility::PackedOption;

    dense_arena_key! {
        struct E;
    }

    #[test]
    fn observer_methods() {
        let mut map = ArenaMap::default();
        let key: E = map.insert("Hello!");

        let none = PackedOption::default();
        let mut some = PackedOption::some(key);

        assert_eq!(none.is_none(), true);
        assert_eq!(none.is_some(), false);
        assert_eq!(some.is_none(), false);
        assert_eq!(some.is_some(), true);

        some = none;

        assert_eq!(some.is_none(), true);
        assert_eq!(some.is_some(), false);
    }
}
