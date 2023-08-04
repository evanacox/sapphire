//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::testcase::FileTestCase;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::OnceLock;
use std::{fs, mem};

type DirectoryContents =
    HashMap<String, Vec<(String, String, FileTestCase<'static>)>, ahash::RandomState>;

static ALL_TEST_CASES: OnceLock<DirectoryContents> = OnceLock::new();

fn recursive_build(out: &mut DirectoryContents, curr_key: String, current_dir: PathBuf) {
    let mut subdirs = Vec::default();

    {
        let files = match out.entry(curr_key.clone()) {
            Entry::Vacant(vac) => vac.insert(Vec::default()),
            Entry::Occupied(_) => unreachable!(),
        };

        for entry in fs::read_dir(current_dir).expect("invalid directory") {
            let entry = entry.expect("i/o error");
            let metadata = entry.metadata().unwrap();
            let name = entry.file_name().into_string().expect("invalid UTF-8 path");
            let path = entry.path();

            if metadata.is_dir() {
                let inner = if curr_key.is_empty() {
                    name
                } else {
                    format!("{curr_key}/{name}")
                };

                subdirs.push((inner, path.clone()));
            } else {
                let content = fs::read_to_string(&path).expect("unable to read file");
                // while content isn't 'static right now, it's immediately going into a lazy_static
                // after this. strings are guaranteed to stay on the heap due to Vec<u8> guarantees
                let check =
                    FileTestCase::from_raw(&name, unsafe { mem::transmute(content.as_str()) });

                files.push((name, content, check))
            }
        }

        files.sort_by(|(n1, _, _), (n2, _, _)| n1.cmp(n2));
    }

    for (inner, path) in subdirs {
        recursive_build(out, inner, path);
    }
}

fn init_directory() -> DirectoryContents {
    let mut map = DirectoryContents::default();
    let mut root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    root.push("tests/");

    recursive_build(&mut map, String::default(), root);

    map
}

pub fn cases_in_subdir(path: &'static str) -> &'static [(String, String, FileTestCase)] {
    assert!(
        ALL_TEST_CASES
            .get_or_init(init_directory)
            .contains_key(path),
        "no files found for path `{path}`"
    );

    &ALL_TEST_CASES.get_or_init(init_directory)[path]
}
