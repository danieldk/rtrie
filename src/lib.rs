extern crate num_traits;

#[cfg(test)]
#[macro_use]
extern crate quickcheck;

extern crate rand;

mod ternary;
pub use ternary::{Priority, TernaryTrie};

#[cfg(test)]
mod test;
