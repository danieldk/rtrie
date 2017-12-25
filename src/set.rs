use rand::Rng;

use super::{Priority, TernaryTrie};

pub struct TernaryTrieSet<P>(TernaryTrie<P, ()>)
where
    P: Priority;

impl<P> TernaryTrieSet<P>
where
    P: Priority,
{
    /// Construct a trie-based set. This constructor has a priority type
    /// parameter. This allows the user to specify the type of the priority.
    /// E.g. for smaller trees a narrow unsigned could suffice and saves
    /// memory.
    pub fn new_with_prio<R>(rng: R) -> Self
    where
        R: Rng + 'static,
    {
        TernaryTrieSet(TernaryTrie::new_with_prio(rng))
    }

    /// Returns `true` when a string is in the trie, or `false` otherwise.
    ///
    /// Since a ternary trie cannot contain the empty string, this method
    /// will always return `false` for an empty string.
    pub fn contains<S>(&self, s: S) -> bool
    where
        S: IntoIterator<Item = char>,
    {
        self.0.contains_key(s)
    }

    /// Returns the number of nodes in the trie.
    pub fn node_count(&self) -> usize {
        self.0.node_count()
    }

    /// Insert a string into the trie.
    ///
    /// Since a ternary tree cannot store empty strings, the `insert` method
    /// will panic when inserting an empty string.
    pub fn insert<S>(&mut self, s: S)
    where
        S: IntoIterator<Item = char>,
    {
        self.0.insert(s, ())
    }

    pub fn iter<'a>(&'a self) -> Iter<'a, P> {
        Iter {
            inner: self.0.iter(),
        }
    }

    /// Iterate over the strings starting with the given `prefix`.
    pub fn prefix_iter<'a, S>(&'a self, prefix: S) -> Iter<'a, P>
    where
        S: IntoIterator<Item = char>,
    {
        Iter {
            inner: self.0.prefix_iter(prefix),
        }
    }

    /// Remove a string from the trie.
    ///
    /// Since a ternary tree cannot store empty strings, the `remove` method
    /// will panic when attempting to remove an empty string.
    pub fn remove<S>(&mut self, s: S)
    where
        S: IntoIterator<Item = char>,
    {
        self.0.remove(s)
    }
}

impl TernaryTrieSet<u32> {
    pub fn new<R>(rng: R) -> Self
    where
        R: Rng + 'static,
    {
        TernaryTrieSet(TernaryTrie::new(rng))
    }
}

pub struct Iter<'a, P>
where
    P: 'a,
{
    inner: super::ternary::Iter<'a, P, ()>,
}

impl<'a, P> Iterator for Iter<'a, P>
where
    P: Priority,
{
    type Item = String;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(k, _)| k)
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use rand;

    use ternary::dead_nodes;
    use tests::*;
    use {Priority, TernaryTrieSet};

    quickcheck! {
        fn ternary_set_prefix_prop(data: Vec<Vec<SmallAlphabet>>) -> bool {
            prefix_test(TernaryTrieSet::new(rand::weak_rng()), data)
        }
    }

    quickcheck! {
        fn ternary_set_contains_prop(data1: Vec<Vec<SmallAlphabet>>, data2: Vec<Vec<SmallAlphabet>>) -> bool {
            contains_test(TernaryTrieSet::new(rand::weak_rng()), data1, data2)
        }
    }

    quickcheck! {
        fn ternary_set_remove_prop(data: Vec<Vec<SmallAlphabet>>) -> bool {
            remove_test(TernaryTrieSet::new(rand::weak_rng()), data)
        }
    }

    quickcheck! {
        fn ternary_set_prefix_prop_u8(data: Vec<Vec<SmallAlphabet>>) -> bool {
            prefix_test(TernaryTrieSet::<u8>::new_with_prio(rand::weak_rng()), data)
        }
    }

    quickcheck! {
        fn ternary_set_contains_prop_u8(data1: Vec<Vec<SmallAlphabet>>, data2: Vec<Vec<SmallAlphabet>>) -> bool {
            contains_test(TernaryTrieSet::<u8>::new_with_prio(rand::weak_rng()), data1, data2)
        }
    }

    quickcheck! {
        fn ternary_set_remove_prop_u8(data: Vec<Vec<SmallAlphabet>>) -> bool {
            remove_test(TernaryTrieSet::<u8>::new_with_prio(rand::weak_rng()), data)
        }
    }

    quickcheck! {
        fn ternary_set_prefix_prop_i32(data: Vec<Vec<SmallAlphabet>>) -> bool {
            prefix_test(TernaryTrieSet::<i32>::new_with_prio(rand::weak_rng()), data)
        }
    }

    quickcheck! {
        fn ternary_set_contains_prop_i32(data1: Vec<Vec<SmallAlphabet>>, data2: Vec<Vec<SmallAlphabet>>) -> bool {
            contains_test(TernaryTrieSet::<i32>::new_with_prio(rand::weak_rng()), data1, data2)
        }
    }

    quickcheck! {
        fn ternary_set_remove_prop_i32(data: Vec<Vec<SmallAlphabet>>) -> bool {
            remove_test(TernaryTrieSet::<i32>::new_with_prio(rand::weak_rng()), data)
        }
    }

    pub fn contains_test<P>(
        mut trie: TernaryTrieSet<P>,
        data1: Vec<Vec<SmallAlphabet>>,
        data2: Vec<Vec<SmallAlphabet>>,
    ) -> bool
    where
        P: Priority,
    {
        let data1: HashSet<_> = small_alphabet_to_string(data1);
        let data2: HashSet<_> = small_alphabet_to_string(data2);
        let diff = &data2 - &data1;

        for s in &data1 {
            trie.insert(s.chars());
        }

        for s in &data1 {
            if !trie.contains(s.chars()) {
                return false;
            }
        }

        for s in &diff {
            if trie.contains(s.chars()) {
                return false;
            }
        }

        true
    }

    fn prefix_test<P>(mut trie: TernaryTrieSet<P>, data: Vec<Vec<SmallAlphabet>>) -> bool
    where
        P: Priority,
    {
        let data: Vec<_> = small_alphabet_to_string(data);

        if data.is_empty() {
            return true;
        }

        for s in &data {
            trie.insert(s.chars());
        }

        let prefix = random_prefix(&data);

        let found_prefixes: HashSet<_> = trie.prefix_iter(prefix.chars()).collect();
        let correct_prefixes: HashSet<String> = data.iter()
            .filter(|w| w.starts_with(&prefix))
            .cloned()
            .collect();

        found_prefixes == correct_prefixes
    }

    fn remove_test<P>(mut trie: TernaryTrieSet<P>, data: Vec<Vec<SmallAlphabet>>) -> bool
    where
        P: Priority,
    {
        let data: HashSet<_> = small_alphabet_to_string(data);

        for s in &data {
            trie.insert(s.chars());
        }

        for s in data {
            if !trie.contains(s.chars()) {
                return false;
            }

            trie.remove(s.chars());

            if trie.contains(s.chars()) {
                return false;
            }

            if dead_nodes(&trie.0) {
                return false;
            }
        }

        true
    }
}
