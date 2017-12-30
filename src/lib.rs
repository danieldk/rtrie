extern crate num_traits;

#[cfg(test)]
#[macro_use]
extern crate quickcheck;

extern crate rand;

mod ternary;
pub use ternary::{Priority, TernaryTrie};

mod set;
pub use set::TernaryTrieSet;

#[cfg(test)]
mod tests {
    use std::iter::FromIterator;

    use quickcheck::{Arbitrary, Gen};
    use rand;
    use rand::Rng;
    use rand::distributions::{IndependentSample, Normal};

    #[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
    pub enum SmallAlphabet {
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

    pub fn small_alphabet_to_string<I, B>(from: I) -> B
    where
        I: IntoIterator<Item = Vec<SmallAlphabet>>,
        B: FromIterator<String>,
    {
        from.into_iter()
            .filter(|w| !w.is_empty())
            .map(FromIterator::<SmallAlphabet>::from_iter)
            .collect()
    }

    pub fn random_prefix(data: &[String]) -> String {
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
}
