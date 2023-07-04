//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

struct ShiftUpto {
    curr: usize,
    upto: usize,
}

impl Iterator for ShiftUpto {
    type Item = (usize, usize);

    fn next(&mut self) -> Option<Self::Item> {
        if self.curr + 1 == self.upto {
            None
        } else {
            self.curr += 1;

            Some((self.curr - 1, self.curr))
        }
    }
}

/// Returns a "moving window" iterator that goes over every integer in `[0, upto)`.
///
/// ```
/// # use sapphire::utility::shift_increment;
/// let mut it = shift_increment(0, 3);
///
/// assert_eq!(it.next(), Some((0, 1)));
/// assert_eq!(it.next(), Some((1, 2)));
/// assert_eq!(it.next(), None);
/// ```
pub fn shift_increment(start: usize, upto: usize) -> impl Iterator<Item = (usize, usize)> {
    ShiftUpto { curr: start, upto }
}

#[cfg(test)]
mod tests {
    use crate::utility::shift_increment;

    #[test]
    fn test_works() {
        {
            let mut it = shift_increment(0, 2);

            assert_eq!(it.next(), Some((0, 1)));
            assert_eq!(it.next(), None);
        }

        {
            let mut it = shift_increment(0, 3);

            assert_eq!(it.next(), Some((0, 1)));
            assert_eq!(it.next(), Some((1, 2)));
            assert_eq!(it.next(), None);
        }
    }
}
