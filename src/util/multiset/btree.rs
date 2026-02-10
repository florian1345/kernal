use std::collections::BTreeMap;
use std::collections::btree_map::Iter as BTreeMapIter;
use std::fmt::{self, Debug, Formatter};

use crate::util::multiset::{self, Multiset, MultisetMap};

impl<T: Eq + Ord> MultisetMap<T> for BTreeMap<T, usize> {
    fn get_mut(&mut self, item: &T) -> Option<&mut usize> {
        BTreeMap::get_mut(self, item)
    }

    fn insert(&mut self, item: T) {
        self.insert(item, 1);
    }

    fn remove(&mut self, item: &T) {
        BTreeMap::remove(self, item);
    }
}

pub(crate) struct BTreeMultisetIter<'iter, T> {
    btree_map_iter: BTreeMapIter<'iter, T, usize>,
}

impl<'iter, T> Iterator for BTreeMultisetIter<'iter, T> {
    type Item = (&'iter T, usize);

    fn next(&mut self) -> Option<Self::Item> {
        self.btree_map_iter
            .next()
            .map(|(value, multiplicity)| (value, *multiplicity))
    }
}

pub(crate) struct BTreeMultiset<T> {
    entries: BTreeMap<T, usize>,
}

impl<T: Debug + Eq + Ord> Multiset<T> for BTreeMultiset<T> {
    type Iter<'iter>
        = BTreeMultisetIter<'iter, T>
    where
        T: 'iter,
        Self: 'iter;

    fn new() -> Self {
        BTreeMultiset {
            entries: BTreeMap::new(),
        }
    }

    fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    fn iter<'reference>(&'reference self) -> BTreeMultisetIter<'reference, T>
    where
        T: 'reference,
    {
        BTreeMultisetIter {
            btree_map_iter: self.entries.iter(),
        }
    }

    fn add(&mut self, item: T) {
        multiset::multiset_map_add(&mut self.entries, item)
    }

    fn remove(&mut self, item: &T) -> bool {
        multiset::multiset_map_remove(&mut self.entries, item)
    }
}

impl<T: Debug + Eq + Ord> FromIterator<T> for BTreeMultiset<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> BTreeMultiset<T> {
        multiset::multiset_from_iter(iter)
    }
}

impl<T: Debug + Eq + Ord> Debug for BTreeMultiset<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        multiset::fmt_multiset_debug(self, f)
    }
}

#[cfg(test)]
mod tests {

    use crate::test_multiset_impl;
    use crate::util::multiset::Multiset;
    use crate::util::multiset::btree::BTreeMultiset;

    test_multiset_impl!(BTreeMultiset);
}
