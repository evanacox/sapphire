//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::ir::DebugInfo;
use crate::reader2::Error;

/// Formats a `reader2::Parser` error into a human-readable string
pub fn format_parse_error<'a>(name: &'a str, source: &'a str, err: Error<'a>) -> String {
    let pair = match err.pair {
        Some(pair) => pair,
        None => {
            return format!(
                "{source}: hit EOF while expecting tokens, error: '{}'",
                err.error
            )
        }
    };

    // get the line we want as the first element in this iterator
    let mut lines = source.lines().skip((pair.line - 1) as usize);
    let line = lines.next().unwrap();

    let (line_n, col_n) = (pair.line.to_string(), pair.col.to_string());
    let mut error = String::default();

    let num_padding = " ".repeat(line_n.len());
    let col_padding = " ".repeat((pair.col - 1) as usize);
    let underline = "^".repeat(pair.len as usize);

    error += &format!("  --> {name}:{line_n}:{col_n}\n");
    error += &format!(" {num_padding} |\n");
    error += &format!(" {line_n} | {line}\n");
    error += &format!(" {num_padding} | {col_padding}{underline}\n");
    error += &format!(" {num_padding} |\n");
    error += &format!(" {num_padding} = {}", err.error);

    error
}

/// Formats errors emitted by the verifier, this is also used by `reader2`.
pub fn format_verifier_error(
    name: &str,
    source: &str,
    mut issues: Vec<(String, DebugInfo)>,
) -> String {
    issues.sort_unstable_by_key(|(_, info)| (info.line(), info.col()));

    let mut error = String::default();

    for (err, info) in issues {
        let line = info.line();
        let col = info.col();

        error += &format!("{name}:{line}:{col}: {err}\n");
    }

    error.pop();

    error
}
