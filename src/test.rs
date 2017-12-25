use quickcheck::{Arbitrary, Gen};
use rand;
use rand::Rng;
use rand::distributions::{IndependentSample, Normal};

use std::collections::HashSet;
use std::iter::FromIterator;

use super::*;
use super::ternary::dead_nodes;

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum SmallAlphabet {
    A,
    B,
    C,
    D,
}

impl Arbitrary for SmallAlphabet {
    fn arbitrary<G: Gen>(g: &mut G) -> Self {
        match g.gen_range(0, 4) {
            0 => SmallAlphabet::A,
            1 => SmallAlphabet::B,
            2 => SmallAlphabet::C,
            3 => SmallAlphabet::D,
            _ => unreachable!(),
        }
    }
}

impl From<SmallAlphabet> for char {
    fn from(a: SmallAlphabet) -> Self {
        match a {
            SmallAlphabet::A => 'a',
            SmallAlphabet::B => 'b',
            SmallAlphabet::C => 'c',
            SmallAlphabet::D => 'd',
        }
    }
}

impl FromIterator<SmallAlphabet> for String {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = SmallAlphabet>,
    {
        iter.into_iter().map(Into::<char>::into).collect()
    }
}

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
        prefix_test(TernaryTrie::<u8>::new_with_prio(rand::weak_rng()), data)
    }
}

quickcheck! {
    fn ternary_contains_prop_u8(data1: Vec<Vec<SmallAlphabet>>, data2: Vec<Vec<SmallAlphabet>>) -> bool {
        contains_test(TernaryTrie::<u8>::new_with_prio(rand::weak_rng()), data1, data2)
    }
}

quickcheck! {
    fn ternary_remove_prop_u8(data: Vec<Vec<SmallAlphabet>>) -> bool {
        remove_test(TernaryTrie::<u8>::new_with_prio(rand::weak_rng()), data)
    }
}

quickcheck! {
    fn ternary_prefix_prop_i32(data: Vec<Vec<SmallAlphabet>>) -> bool {
        prefix_test(TernaryTrie::<i32>::new_with_prio(rand::weak_rng()), data)
    }
}

quickcheck! {
    fn ternary_contains_prop_i32(data1: Vec<Vec<SmallAlphabet>>, data2: Vec<Vec<SmallAlphabet>>) -> bool {
        contains_test(TernaryTrie::<i32>::new_with_prio(rand::weak_rng()), data1, data2)
    }
}

quickcheck! {
    fn ternary_remove_prop_i32(data: Vec<Vec<SmallAlphabet>>) -> bool {
        remove_test(TernaryTrie::<i32>::new_with_prio(rand::weak_rng()), data)
    }
}

fn small_alphabet_to_string<I, B>(from: I) -> B
where
    I: IntoIterator<Item = Vec<SmallAlphabet>>,
    B: FromIterator<String>,
{
    from.into_iter()
        .filter(|w| !w.is_empty())
        .map(FromIterator::<SmallAlphabet>::from_iter)
        .collect()
}

fn contains_test<P>(
    mut trie: TernaryTrie<P>,
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

fn prefix_test<P>(mut trie: TernaryTrie<P>, data: Vec<Vec<SmallAlphabet>>) -> bool
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

fn remove_test<P>(mut trie: TernaryTrie<P>, data: Vec<Vec<SmallAlphabet>>) -> bool
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

        if dead_nodes(&trie) {
            return false;
        }
    }

    true
}

fn random_prefix(data: &[String]) -> String {
    let mut rng = rand::thread_rng();
    let idx = rng.gen_range(0, data.len());

    let s: String = data[idx].clone();

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
