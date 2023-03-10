//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use smallvec::SmallVec;

/// Models a type that can be traversed in a tree-like fashion. This is
/// intended for debug APIs / passes that deal in human-readable trees.
pub trait IntoTree<'a, const N: usize> {
    /// The node type of the tree
    type Node: Copy;

    /// Returns the root tree node
    fn root(&'a self) -> Self::Node;

    /// Returns the list of children that a given node has
    fn children(&'a self, node: Self::Node) -> SmallVec<[Self::Node; N]>;
}

/// Prints a tree in a consistent format.
///
/// Ex:
///
/// ```none
/// root
/// ├── child 1
/// │   ├── grandchild 1
/// │   └── grandchild 2
/// └── child 2
///     └── grandchild 3
/// ```
pub fn stringify_tree<'a, U, T, F, const N: usize>(tree: &'a T, mut stringify: F) -> String
where
    U: Copy,
    T: IntoTree<'a, N, Node = U>,
    F: FnMut(U) -> String,
{
    let mut result = String::default();

    stringify_tree_recursive(&mut result, "", tree.root(), tree, &mut stringify);

    result
}

fn stringify_tree_recursive<'a, U, T, F, const N: usize>(
    out: &mut String,
    prefix: &str,
    curr: T::Node,
    tree: &'a T,
    stringify: &mut F,
) where
    U: Copy,
    T: IntoTree<'a, N, Node = U>,
    F: FnMut(U) -> String,
{
    let children = tree.children(curr);

    *out += &stringify(curr);
    out.push('\n');

    if children.is_empty() {
        return;
    }

    // in this case, we need an extra bar in the new prefix because there will be
    // other subtrees after ours.

    let new_start = format!("{prefix}├── ");
    let new_prefix = format!("{prefix}│   ");

    for child in &children[0..children.len() - 1] {
        *out += &new_start;

        stringify_tree_recursive(out, &new_prefix, *child, tree, stringify);
    }

    // in this case, we don't need to add a continuing bar to the
    // prefix, because there's nothing after a given subtree
    *out += &format!("{prefix}└── ");
    stringify_tree_recursive(
        out,
        &format!("{prefix}    "),
        children[children.len() - 1],
        tree,
        stringify,
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    use smallvec::smallvec;

    #[derive(Clone)]
    enum BinaryTree {
        Leaf(i32),
        Tree(i32, Box<BinaryTree>, Box<BinaryTree>),
    }

    #[derive(Copy, Clone)]
    struct BinaryTreeIter<'b> {
        curr: &'b BinaryTree,
    }

    impl<'a> IntoTree<'a, 2> for BinaryTree {
        type Node = BinaryTreeIter<'a>;

        fn root(&'a self) -> Self::Node {
            Self::Node { curr: self }
        }

        fn children(&'a self, node: Self::Node) -> SmallVec<[Self::Node; 2]> {
            match node.curr {
                BinaryTree::Leaf(_) => SmallVec::default(),
                BinaryTree::Tree(_, lhs, rhs) => {
                    smallvec![BinaryTreeIter { curr: lhs }, BinaryTreeIter { curr: rhs }]
                }
            }
        }
    }

    #[test]
    fn simple_binary_tree() {
        //
        // 0
        //   1
        //     2
        //     3
        //   4
        //     5
        //       6
        //       7
        //     8
        //
        //
        let tree = BinaryTree::Tree(
            0,
            Box::new(BinaryTree::Tree(
                1,
                Box::new(BinaryTree::Leaf(2)),
                Box::new(BinaryTree::Leaf(3)),
            )),
            Box::new(BinaryTree::Tree(
                4,
                Box::new(BinaryTree::Tree(
                    5,
                    Box::new(BinaryTree::Leaf(6)),
                    Box::new(BinaryTree::Leaf(7)),
                )),
                Box::new(BinaryTree::Leaf(8)),
            )),
        );

        let stringify = |node: BinaryTreeIter<'_>| match node.curr {
            BinaryTree::Leaf(n) | BinaryTree::Tree(n, _, _) => format!("{n}"),
        };

        let expected = r#"0
├── 1
│   ├── 2
│   └── 3
└── 4
    ├── 5
    │   ├── 6
    │   └── 7
    └── 8
"#;

        assert_eq!(stringify_tree(&tree, stringify), expected);
    }
}
