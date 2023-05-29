use std::collections::HashMap;
use std::collections::hash_map::Iter as HashMapIter;
use std::fmt::{self, Debug, Formatter};
use std::hash::Hash;

use crate::util::multiset::{self, Multiset};

pub(crate) struct HashMultisetIter<'iter, T> {
    hash_map_iter: HashMapIter<'iter, T, usize>
}

impl<'iter, T> Iterator for HashMultisetIter<'iter, T> {
    type Item = (&'iter T, usize);

    fn next(&mut self) -> Option<(&'iter T, usize)> {
        self.hash_map_iter.next().map(|(value, multiplicity)| (value, *multiplicity))
    }
}

pub(crate) struct HashMultiset<T> {
    entries: HashMap<T, usize>
}

impl<T: Debug + Hash + Eq> Multiset<T> for HashMultiset<T> {

    type Iter<'iter> = HashMultisetIter<'iter, T>
    where
        T: 'iter,
        Self: 'iter;

    fn new() -> HashMultiset<T> {
        HashMultiset {
            entries: HashMap::new()
        }
    }

    fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    fn iter<'reference>(&'reference self) -> HashMultisetIter<'reference, T>
    where
        T: 'reference
    {
        HashMultisetIter {
            hash_map_iter: self.entries.iter()
        }
    }

    fn add(&mut self, item: T) {
        if let Some(multiplicity) = self.entries.get_mut(&item) {
            *multiplicity += 1;
        }
        else {
            self.entries.insert(item, 1);
        }
    }

    fn remove(&mut self, item: &T) -> bool {
        if let Some(multiplicity) = self.entries.get_mut(item) {
            *multiplicity -= 1;

            if *multiplicity == 0 {
                self.entries.remove(item);
            }

            true
        }
        else {
            false
        }
    }
}

impl<T: Debug + Hash + Eq> FromIterator<T> for HashMultiset<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut multiset = HashMultiset::new();

        for item in iter {
            multiset.add(item);
        }

        multiset
    }
}

impl<T: Debug + Hash + Eq> Debug for HashMultiset<T> {
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
