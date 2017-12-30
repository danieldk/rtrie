use std::cmp;
use std::cmp::Ordering;
use std::iter::Peekable;
use std::mem;

use num_traits::{Bounded, One, PrimInt};
use rand::Rng;
use rand::distributions::range::SampleRange;

/// Trait for node priority types.
pub trait Priority: PrimInt + SampleRange {}
impl<T> Priority for T
where
    T: PrimInt + SampleRange,
{
}

/// A randomized ternary search trie.
///
/// This is a variant of the ternary search tree that uses randomization
/// to ensure that the tree is (typically) balanced. See: *Randomized
/// Ternary Search Tries*, Nicolai Diethelm:
///
/// <https://arxiv.org/abs/1606.04042>
pub struct TernaryTrie<P, V>
where
    P: Priority,
{
    root: BoxedNode<P, V>,
    rng: Box<Rng>,
}

impl<P, V> TernaryTrie<P, V>
where
    P: Priority,
{
    /// Construct a trie. This constructor has a priority type parameter,
    /// This allows the user to specify the type of the priority. E.g. for
    /// smaller trees a narrow unsigned could suffice and saves memory.
    pub fn new_with_prio<R>(rng: R) -> Self
    where
        R: Rng + 'static,
    {
        TernaryTrie {
            root: BoxedNode::default(),
            rng: Box::new(rng),
        }
    }

    /// Returns `true` when a string is in the trie, or `false` otherwise.
    ///
    /// Since a ternary trie cannot contain the empty string, this method
    /// will always return `false` for an empty string.
    pub fn contains_key<S>(&self, s: S) -> bool
    where
        S: IntoIterator<Item = char>,
    {
        let mut chars = s.into_iter().peekable();

        if chars.peek().is_none() {
            return false;
        }

        match self.root.prefix_node(chars) {
            Some(node) => node.str_prio != Bounded::min_value(),
            None => false,
        }
    }

    /// Returns the number of nodes in the trie.
    pub fn node_count(&self) -> usize {
        self.root.node_count()
    }

    /// Insert a string into the trie.
    ///
    /// Since a ternary tree cannot store empty strings, the `insert` method
    /// will panic when inserting an empty string.
    pub fn insert<S>(&mut self, s: S, value: V)
    where
        S: IntoIterator<Item = char>,
    {
        let mut chars = s.into_iter().peekable();

        assert!(
            chars.peek().is_some(),
            "Empty strings cannot be inserted into a TernaryTrie"
        );

        let mut root = BoxedNode::default();
        mem::swap(&mut root, &mut self.root);
        self.root = root.insert(chars, value, &mut self.rng);
    }

    /// Return an iterator over the strings in the trie.
    pub fn iter<'a>(&'a self) -> Iter<'a, P, V> {
        Iter::new(self.root.as_ref())
    }

    /// Iterate over the strings starting with the given `prefix`.
    pub fn prefix_iter<'a, S>(&'a self, prefix: S) -> Iter<'a, P, V>
    where
        S: IntoIterator<Item = char>,
    {
        let prefix: String = prefix.into_iter().collect();

        if prefix.is_empty() {
            return Iter::new(self.root.as_ref());
        }

        // Get the tree node that represents the prefix.
        let node = self.root.prefix_node(prefix.chars().peekable());

        Iter::with_prefix(node, prefix)
    }

    /// Remove a string from the trie.
    ///
    /// Since a ternary tree cannot store empty strings, the `remove` method
    /// will panic when attempting to insert an empty string.
    pub fn remove<S>(&mut self, s: S)
    where
        S: IntoIterator<Item = char>,
    {
        let mut chars = s.into_iter().peekable();

        assert!(
            chars.peek().is_some(),
            "Empty strings cannot be removed from a TernaryTrie"
        );

        let mut root = BoxedNode::default();
        mem::swap(&mut root, &mut self.root);
        self.root = root.remove(chars);
    }
}

impl<V> TernaryTrie<u32, V> {
    /// Construct a trie. The random number generator will be used to
    /// generate string priorities.
    pub fn new<R>(rng: R) -> Self
    where
        R: Rng + 'static,
    {
        TernaryTrie {
            root: BoxedNode::default(),
            rng: Box::new(rng),
        }
    }
}

#[derive(Debug)]
struct TreeNode<P, V> {
    ch: char,
    value: Option<V>,

    // Node priority. This should always be larger than the priorities of the
    // left and right child.
    prio: P,

    // String priority: 0 if this node does not represent a string, non-0 otherwise.
    str_prio: P,

    left: BoxedNode<P, V>,
    mid: BoxedNode<P, V>,
    right: BoxedNode<P, V>,
}

impl<P, V> TreeNode<P, V>
where
    P: Priority,
{
    fn new(ch: char) -> Self {
        TreeNode {
            ch,
            value: None,
            prio: Bounded::min_value(),
            str_prio: Bounded::min_value(),
            left: BoxedNode::default(),
            mid: BoxedNode::default(),
            right: BoxedNode::default(),
        }
    }
}

/// A boxed node: the motivation is twofold:
///
/// - The size of a recursive value type cannot be computed.
/// - This representation allows us to model absent nodes (that we can
///   still insert on).
#[derive(Debug)]
struct BoxedNode<P, V>(Option<Box<TreeNode<P, V>>>);

impl<P, V> BoxedNode<P, V> {
    /// Construct a boxed node from a tree node.
    fn new(node: TreeNode<P, V>) -> Self {
        BoxedNode(Some(Box::new(node)))
    }

    /// Get the boxed node as a reference.
    fn as_ref(&self) -> Option<&TreeNode<P, V>> {
        self.0.as_ref().map(|b| b.as_ref())
    }
}

impl<P, V> BoxedNode<P, V>
where
    P: Priority,
{
    /// Insert characters into the tree starting at this boxed node. This
    /// method will panic if it is passed an iterator without characters.
    fn insert<I, R>(self, mut chars: Peekable<I>, value: V, rng: &mut R) -> Self
    where
        I: Iterator<Item = char>,
        R: Rng,
    {
        let ch = *chars.peek().unwrap();

        // Unwrap the treenode, creating a new node if it was an empty node.
        let mut node = match self.0 {
            Some(node) => *node,
            None => TreeNode::new(ch),
        };

        // Recursively insert in the correct child, rotating this node and
        // the left/right child node when the child has a higher priority.
        match ch.cmp(&node.ch) {
            Ordering::Less => {
                node.left = node.left.insert(chars, value, rng);
                if node.left.as_ref().unwrap().prio > node.prio {
                    node = rotate_with_left(node);
                }
            }
            Ordering::Greater => {
                node.right = node.right.insert(chars, value, rng);
                if node.right.as_ref().unwrap().prio > node.prio {
                    node = rotate_with_right(node);
                }
            }
            Ordering::Equal => {
                chars.next();

                if chars.peek().is_some() {
                    node.mid = node.mid.insert(chars, value, rng);
                } else if node.str_prio == Bounded::min_value() {
                    // Generate non-zero string priority to mark that the node
                    // represents a string.
                    node.str_prio =
                        rng.gen_range::<P>(Bounded::min_value(), Bounded::max_value()) + One::one();
                    node.value = Some(value);
                } else {
                    // Replace the value for a string that is already in the tree.
                    node.value = Some(value);
                }

                // If there is a mid child, the node takes the highest of the
                // child priority and the priority of its own string (if any).
                node.prio = match node.mid.0 {
                    Some(ref mid) => cmp::max(node.str_prio, mid.prio),
                    None => node.str_prio,
                }
            }
        }

        BoxedNode::new(node)
    }

    fn node_count(&self) -> usize {
        match self.as_ref() {
            Some(node) => {
                1 + node.left.node_count() + node.mid.node_count() + node.right.node_count()
            }
            None => 0,
        }
    }

    /// Returns the node that represents the given prefix. Note that we
    /// return the accepting node and not its mid chid. Otherwise, a
    /// caller could not check if the prefix is also a string.
    fn prefix_node<I>(&self, mut chars: Peekable<I>) -> Option<&TreeNode<P, V>>
    where
        I: Iterator<Item = char>,
    {
        match self.as_ref() {
            Some(node) => chars.peek().cloned().and_then(|ch| match ch.cmp(&node.ch) {
                Ordering::Less => node.left.prefix_node(chars),
                Ordering::Greater => node.right.prefix_node(chars),
                Ordering::Equal => {
                    chars.next();
                    if chars.peek().is_some() {
                        node.mid.prefix_node(chars)
                    } else {
                        Some(node)
                    }
                }
            }),
            None => None,
        }
    }

    /// Remove the string with the given 'suffix' characters.
    pub fn remove<I>(self, mut chars: Peekable<I>) -> Self
    where
        I: Iterator<Item = char>,
    {
        let ch = *chars.peek().unwrap();

        // Unwrap the treenode, If the node is None, there is nothing to delete
        let mut node = match self.0 {
            Some(node) => *node,
            None => return self,
        };

        // Remove recursively on the correct daughter.
        match ch.cmp(&node.ch) {
            Ordering::Less => node.left = node.left.remove(chars),
            Ordering::Greater => node.right = node.right.remove(chars),
            Ordering::Equal => {
                chars.next();

                if chars.peek().is_some() {
                    node.mid = node.mid.remove(chars);
                } else {
                    // Remove the string by setting its priority to 0.
                    node.str_prio = Bounded::min_value();
                }

                // If there is a mid child, the node takes the highest of the
                // child priority and the priority of its own string (if any).
                node.prio = match node.mid.0 {
                    Some(ref mid) => cmp::max(node.str_prio, mid.prio),
                    None => node.str_prio,
                };

                return heapify_or_delete(node);
            }
        }

        BoxedNode::new(node)
    }
}

impl<P, V> Default for BoxedNode<P, V> {
    fn default() -> Self {
        BoxedNode(None)
    }
}

/// Iterator items.
enum IterItem<'a, P, V>
where
    P: 'a,
    V: 'a,
{
    /// Pair of a node and the 'generated' string to reach the node.
    Node(Option<&'a TreeNode<P, V>>, String),

    /// A value (string accepted by the trie).
    Value(String, &'a V),
}

pub struct Iter<'a, P: 'a, V: 'a> {
    work: Vec<IterItem<'a, P, V>>,
}

impl<'a, P, V> Iter<'a, P, V>
where
    P: Priority,
    V: 'a,
{
    /// Create a new iterator starting at the given node.
    fn new(root: Option<&'a TreeNode<P, V>>) -> Self {
        Iter {
            work: vec![IterItem::Node(root, String::new())],
        }
    }

    /// Create a new iterator starting at the given node, with a prefix.
    fn with_prefix(root: Option<&'a TreeNode<P, V>>, prefix: String) -> Self {
        if prefix.is_empty() {
            return Iter {
                work: vec![IterItem::Node(root, prefix)],
            };
        }

        let mut items = Vec::new();
        if let Some(root) = root {
            items.push(IterItem::Node(root.mid.as_ref(), prefix.clone()));

            // If the prefix is non-empty, we also have to check whether the
            // given node/prefix is a string. If so, we add this as a result
            // item.
            if root.str_prio != Bounded::min_value() {
                items.push(IterItem::Value(prefix, root.value.as_ref().unwrap()));
            }
        }

        Iter { work: items }
    }
}

impl<'a, P, V> Iterator for Iter<'a, P, V>
where
    P: Priority,
{
    type Item = (String, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let item = match self.work.pop() {
                Some(item) => item,
                None => return None,
            };

            match item {
                IterItem::Value(k, v) => return Some((k, v)),
                IterItem::Node(node, prefix) => {
                    // Note 'work' is a stack, so we have to add work that we want
                    // to do last first and vice versa.

                    let node = match node {
                        Some(node) => node,
                        None => continue,
                    };

                    // Add reachable nodes as work.
                    self.work
                        .push(IterItem::Node(node.right.as_ref(), prefix.clone()));

                    let mut new_prefix = prefix.clone();
                    new_prefix.push(node.ch);

                    self.work
                        .push(IterItem::Node(node.mid.as_ref(), new_prefix.clone()));

                    if node.str_prio != Bounded::min_value() {
                        self.work.push(IterItem::Value(
                            new_prefix.clone(),
                            node.value.as_ref().unwrap(),
                        ));
                    }

                    self.work
                        .push(IterItem::Node(node.left.as_ref(), prefix.clone()));
                }
            }
        }
    }
}

#[allow(dead_code)]
pub fn dead_nodes<P, V>(trie: &TernaryTrie<P, V>) -> bool
where
    P: Priority,
{
    dead_nodes_(trie.root.as_ref())
}

fn dead_nodes_<P, V>(node: Option<&TreeNode<P, V>>) -> bool
where
    P: Priority,
{
    match node {
        Some(node) => {
            if dead_nodes_(node.left.as_ref()) || dead_nodes_(node.mid.as_ref())
                || dead_nodes_(node.right.as_ref())
            {
                true
            } else {
                node.mid.0.is_none() && node.str_prio == Bounded::min_value()
            }
        }
        None => false,
    }
}

/// Rotate a node with a child if a child has a higher priority. Remove the
/// node when its priority is zero.
fn heapify_or_delete<P, V>(mut node: TreeNode<P, V>) -> BoxedNode<P, V>
where
    P: Priority,
{
    let left_prio = node.left
        .as_ref()
        .map(|n| n.prio)
        .unwrap_or(Bounded::min_value());
    let right_prio = node.right
        .as_ref()
        .map(|n| n.prio)
        .unwrap_or(Bounded::min_value());

    if node.prio < left_prio || node.prio < right_prio {
        if left_prio > right_prio {
            node = rotate_with_left(node);
            node.right = heapify_or_delete(*node.right.0.unwrap());
        } else {
            node = rotate_with_right(node);
            node.left = heapify_or_delete(*node.left.0.unwrap());
        }
    } else if node.prio == Bounded::min_value() {
        return BoxedNode::default();
    }

    BoxedNode::new(node)
}

/// Rotate node with its left child.
fn rotate_with_left<P, V>(mut node: TreeNode<P, V>) -> TreeNode<P, V> {
    let mut y = *node.left.0.unwrap();
    node.left = y.right;
    y.right = BoxedNode::new(node);
    y
}

/// Rotate node with its right child.
fn rotate_with_right<P, V>(mut node: TreeNode<P, V>) -> TreeNode<P, V> {
    let mut y = *node.right.0.unwrap();
    node.right = y.left;
    y.left = BoxedNode::new(node);
    y
}

#[cfg(test)]
mod tests {
    use rand;
    use rand::distributions::{IndependentSample, Normal};

    use std::collections::HashMap;
    use std::iter::FromIterator;

    use super::*;
    use super::dead_nodes;

    use tests::SmallAlphabet;

    quickcheck! {
        fn ternary_prefix_prop(data: Vec<(Vec<SmallAlphabet>, usize)>) -> bool {
            prefix_test(TernaryTrie::new(rand::weak_rng()), data)
        }
    }

    quickcheck! {
        fn ternary_contains_prop(data1: Vec<(Vec<SmallAlphabet>, usize)>, data2: Vec<(Vec<SmallAlphabet>, usize)>) -> bool {
            contains_test(TernaryTrie::new(rand::weak_rng()), data1, data2)
        }
    }

    quickcheck! {
        fn ternary_remove_prop(data: Vec<(Vec<SmallAlphabet>, usize)>) -> bool {
            remove_test(TernaryTrie::new(rand::weak_rng()), data)
        }
    }

    quickcheck! {
        fn ternary_prefix_prop_u8(data: Vec<(Vec<SmallAlphabet>, usize)>) -> bool {
            prefix_test(TernaryTrie::<u8, usize>::new_with_prio(rand::weak_rng()), data)
        }
    }

    quickcheck! {
        fn ternary_contains_prop_u8(data1: Vec<(Vec<SmallAlphabet>, usize)>, data2: Vec<(Vec<SmallAlphabet>, usize)>) -> bool {
            contains_test(TernaryTrie::<u8, usize>::new_with_prio(rand::weak_rng()), data1, data2)
        }
    }

    quickcheck! {
        fn ternary_remove_prop_u8(data: Vec<(Vec<SmallAlphabet>, usize)>) -> bool {
            remove_test(TernaryTrie::<u8, usize>::new_with_prio(rand::weak_rng()), data)
        }
    }

    quickcheck! {
        fn ternary_prefix_prop_i32(data: Vec<(Vec<SmallAlphabet>, usize)>) -> bool {
            prefix_test(TernaryTrie::<i32, usize>::new_with_prio(rand::weak_rng()), data)
        }
    }

    quickcheck! {
        fn ternary_contains_prop_i32(data1: Vec<(Vec<SmallAlphabet>, usize)>, data2: Vec<(Vec<SmallAlphabet>, usize)>) -> bool {
            contains_test(TernaryTrie::<i32, usize>::new_with_prio(rand::weak_rng()), data1, data2)
        }
    }

    quickcheck! {
        fn ternary_remove_prop_i32(data: Vec<(Vec<SmallAlphabet>, usize)>) -> bool {
            remove_test(TernaryTrie::<i32, usize>::new_with_prio(rand::weak_rng()), data)
        }
    }

    fn contains_test<P, V>(
        mut trie: TernaryTrie<P, V>,
        data1: Vec<(Vec<SmallAlphabet>, V)>,
        data2: Vec<(Vec<SmallAlphabet>, V)>,
    ) -> bool
    where
        P: Priority,
        V: Clone,
    {
        let data1: HashMap<_, _> = small_alphabet_to_string(data1);
        let data2: HashMap<_, _> = small_alphabet_to_string(data2);

        for (k, v) in &data1 {
            trie.insert(k.chars(), v.clone());
        }

        for (k, _) in &data1 {
            if !trie.contains_key(k.chars()) {
                return false;
            }
        }

        for (k, _) in &data2 {
            if !data1.contains_key(k) && trie.contains_key(k.chars()) {
                return false;
            }
        }

        true
    }

    fn prefix_test<P, V>(mut trie: TernaryTrie<P, V>, data: Vec<(Vec<SmallAlphabet>, V)>) -> bool
    where
        P: Priority,
        V: Clone + Eq,
    {
        let data: Vec<_> = small_alphabet_to_string(data);

        if data.is_empty() {
            return true;
        }

        for &(ref k, ref v) in &data {
            trie.insert(k.chars(), v.clone());
        }

        let prefix = random_prefix(&data);

        let found_prefixes: HashMap<_, _> = trie.prefix_iter(prefix.chars())
            .map(|(k, v)| (k, v.clone()))
            .collect();
        let correct_prefixes: HashMap<_, _> = data.into_iter()
            .filter(|&(ref k, _)| k.starts_with(&prefix))
            .collect();

        found_prefixes == correct_prefixes
    }

    fn remove_test<P, V>(mut trie: TernaryTrie<P, V>, data: Vec<(Vec<SmallAlphabet>, V)>) -> bool
    where
        P: Priority,
        V: Clone,
    {
        let data: HashMap<_, _> = small_alphabet_to_string(data);

        for (k, v) in &data {
            trie.insert(k.chars(), v.clone());
        }

        for (k, _) in data {
            if !trie.contains_key(k.chars()) {
                return false;
            }

            trie.remove(k.chars());

            if trie.contains_key(k.chars()) {
                return false;
            }

            if dead_nodes(&trie) {
                return false;
            }
        }

        true
    }

    pub fn small_alphabet_to_string<I, B, V>(from: I) -> B
    where
        I: IntoIterator<Item = (Vec<SmallAlphabet>, V)>,
        B: FromIterator<(String, V)>,
        V: Clone,
    {
        from.into_iter()
            .filter(|&(ref k, _)| !k.is_empty())
            .map(|(k, v)| (FromIterator::<SmallAlphabet>::from_iter(k), v.clone()))
            .collect()
    }

    pub fn random_prefix<V>(data: &[(String, V)]) -> String {
        let mut rng = rand::thread_rng();
        let idx = rng.gen_range(0, data.len());

        let s: String = data[idx].0.clone();

        // Get a random and valid length, biased towards short prefixes.
        let mut len;
        loop {
            let normal = Normal::new(0., 2.);
            len = normal.ind_sample(&mut rng).abs().round() as usize + 1;

            if len <= s.len() {
                break;
            }
        }

        s.chars().take(len).collect()
    }
}
