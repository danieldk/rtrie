use rand;

use std::collections::HashSet;

use super::*;
use super::ternary::dead_nodes;

use tests::*;

quickcheck! {
    fn ternary_prefix_prop(data: Vec<Vec<SmallAlphabet>>) -> bool {
        prefix_test(TernaryTrie::new(rand::weak_rng()), data)
    }
}

quickcheck! {
    fn ternary_contains_prop(data1: Vec<Vec<SmallAlphabet>>, data2: Vec<Vec<SmallAlphabet>>) -> bool {
        contains_test(TernaryTrie::new(rand::weak_rng()), data1, data2)
    }
}

quickcheck! {
    fn ternary_remove_prop(data: Vec<Vec<SmallAlphabet>>) -> bool {
        remove_test(TernaryTrie::new(rand::weak_rng()), data)
    }
}

quickcheck! {
    fn ternary_prefix_prop_u8(data: Vec<Vec<SmallAlphabet>>) -> bool {
        prefix_test(TernaryTrie::<u8, ()>::new_with_prio(rand::weak_rng()), data)
    }
}

quickcheck! {
    fn ternary_contains_prop_u8(data1: Vec<Vec<SmallAlphabet>>, data2: Vec<Vec<SmallAlphabet>>) -> bool {
        contains_test(TernaryTrie::<u8, ()>::new_with_prio(rand::weak_rng()), data1, data2)
    }
}

quickcheck! {
    fn ternary_remove_prop_u8(data: Vec<Vec<SmallAlphabet>>) -> bool {
        remove_test(TernaryTrie::<u8, ()>::new_with_prio(rand::weak_rng()), data)
    }
}

quickcheck! {
    fn ternary_prefix_prop_i32(data: Vec<Vec<SmallAlphabet>>) -> bool {
        prefix_test(TernaryTrie::<i32, ()>::new_with_prio(rand::weak_rng()), data)
    }
}

quickcheck! {
    fn ternary_contains_prop_i32(data1: Vec<Vec<SmallAlphabet>>, data2: Vec<Vec<SmallAlphabet>>) -> bool {
        contains_test(TernaryTrie::<i32, ()>::new_with_prio(rand::weak_rng()), data1, data2)
    }
}

quickcheck! {
    fn ternary_remove_prop_i32(data: Vec<Vec<SmallAlphabet>>) -> bool {
        remove_test(TernaryTrie::<i32, ()>::new_with_prio(rand::weak_rng()), data)
    }
}

fn contains_test<P>(
    mut trie: TernaryTrie<P, ()>,
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
        trie.insert(s.chars(), ());
    }

    for s in &data1 {
        if !trie.contains_key(s.chars()) {
            return false;
        }
    }

    for s in &diff {
        if trie.contains_key(s.chars()) {
            return false;
        }
    }

    true
}

fn prefix_test<P>(mut trie: TernaryTrie<P, ()>, data: Vec<Vec<SmallAlphabet>>) -> bool
where
    P: Priority,
{
    let data: Vec<_> = small_alphabet_to_string(data);

    if data.is_empty() {
        return true;
    }

    for s in &data {
        trie.insert(s.chars(), ());
    }

    let prefix = random_prefix(&data);

    let found_prefixes: HashSet<_> = trie.prefix_iter(prefix.chars()).map(|(k, _)| k).collect();
    let correct_prefixes: HashSet<String> = data.iter()
        .filter(|w| w.starts_with(&prefix))
        .cloned()
        .collect();

    found_prefixes == correct_prefixes
}

fn remove_test<P>(mut trie: TernaryTrie<P, ()>, data: Vec<Vec<SmallAlphabet>>) -> bool
where
    P: Priority,
{
    let data: HashSet<_> = small_alphabet_to_string(data);

    for s in &data {
        trie.insert(s.chars(), ());
    }

    for s in data {
        if !trie.contains_key(s.chars()) {
            return false;
        }

        trie.remove(s.chars());

        if trie.contains_key(s.chars()) {
            return false;
        }

        if dead_nodes(&trie) {
            return false;
        }
    }

    true
}
