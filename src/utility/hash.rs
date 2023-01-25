//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use std::collections::{HashMap, HashSet};

/// Alias for `std::collections::HashMap<K, V, ahash::RandomState>`. This is a
/// hash table that uses a faster hash function, this is significantly faster
/// for the small keys that we are using everywhere.
pub type SaHashMap<K, V> = HashMap<K, V, ahash::RandomState>;

/// Alias for `std::collections::HashSet<V, ahash::RandomState>`. This is a
/// hash table that uses a faster hash function, this is significantly faster
/// for the small keys that we are using everywhere.
pub type SaHashSet<V> = HashSet<V, ahash::RandomState>;
