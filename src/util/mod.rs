use std::borrow::Borrow;
use std::collections::{BTreeSet, HashSet};
use std::hash::Hash;

pub(crate) mod multiset;

pub(crate) fn borrow_all<T, B: Borrow<T>>(to_borrow: &[B]) -> Vec<&T> {
    to_borrow.iter().map(|b| b.borrow()).collect()
}

pub(crate) fn borrow_all_pairs<L, R, LB, RB>(to_borrow: &[(LB, RB)]) -> Vec<(&L, &R)>
where
    LB: Borrow<L>,
    RB: Borrow<R>,
{
    to_borrow
        .iter()
        .map(|(l, r)| (l.borrow(), r.borrow()))
        .collect()
}

pub(crate) trait Set<T>: FromIterator<T> {
    fn contains(&self, item: &T) -> bool;
}

impl<T: PartialEq> Set<T> for Vec<T> {
    fn contains(&self, item: &T) -> bool {
        self.as_slice().contains(item)
    }
}

impl<T: Eq + Hash> Set<T> for HashSet<T> {
    fn contains(&self, item: &T) -> bool {
        HashSet::contains(self, item)
    }
}

impl<T: Eq + Ord> Set<T> for BTreeSet<T> {
    fn contains(&self, item: &T) -> bool {
        BTreeSet::contains(self, item)
    }
}
