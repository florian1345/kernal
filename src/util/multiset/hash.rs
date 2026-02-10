use std::collections::HashMap;
use std::collections::hash_map::Iter as HashMapIter;
use std::fmt::{self, Debug, Formatter};
use std::hash::Hash;

use crate::util::multiset::{self, Multiset, MultisetMap};

impl<T: Eq + Hash> MultisetMap<T> for HashMap<T, usize> {
    fn get_mut(&mut self, item: &T) -> Option<&mut usize> {
        HashMap::get_mut(self, item)
    }

    fn insert(&mut self, item: T) {
        self.insert(item, 1);
    }

    fn remove(&mut self, item: &T) {
        HashMap::remove(self, item);
    }
}

pub(crate) struct HashMultisetIter<'iter, T> {
    hash_map_iter: HashMapIter<'iter, T, usize>,
}

impl<'iter, T> Iterator for HashMultisetIter<'iter, T> {
    type Item = (&'iter T, usize);

    fn next(&mut self) -> Option<(&'iter T, usize)> {
        self.hash_map_iter
            .next()
            .map(|(value, multiplicity)| (value, *multiplicity))
    }
}

pub(crate) struct HashMultiset<T> {
    entries: HashMap<T, usize>,
}

impl<T: Debug + Eq + Hash> Multiset<T> for HashMultiset<T> {
    type Iter<'iter>
        = HashMultisetIter<'iter, T>
    where
        T: 'iter,
        Self: 'iter;

    fn new() -> HashMultiset<T> {
        HashMultiset {
            entries: HashMap::new(),
        }
    }

    fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    fn iter<'reference>(&'reference self) -> HashMultisetIter<'reference, T>
    where
        T: 'reference,
    {
        HashMultisetIter {
            hash_map_iter: self.entries.iter(),
        }
    }

    fn add(&mut self, item: T) {
        multiset::multiset_map_add(&mut self.entries, item)
    }

    fn remove(&mut self, item: &T) -> bool {
        multiset::multiset_map_remove(&mut self.entries, item)
    }
}

impl<T: Debug + Eq + Hash> FromIterator<T> for HashMultiset<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> HashMultiset<T> {
        multiset::multiset_from_iter(iter)
    }
}

impl<T: Debug + Eq + Hash> Debug for HashMultiset<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        multiset::fmt_multiset_debug(self, f)
    }
}

#[cfg(test)]
mod tests {

    use crate::test_multiset_impl;
    use crate::util::multiset::Multiset;
    use crate::util::multiset::hash::HashMultiset;

    test_multiset_impl!(HashMultiset);
}
