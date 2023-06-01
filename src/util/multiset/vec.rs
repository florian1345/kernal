use std::fmt::{Debug, Formatter};
use std::fmt;

use crate::util::multiset::{self, Multiset};

pub(crate) struct VecMultisetIter<'iter, T> {
    set: &'iter VecMultiset<T>,
    index: usize
}

impl<'iter, T> Iterator for VecMultisetIter<'iter, T> {
    type Item = (&'iter T, usize);

    fn next(&mut self) -> Option<(&'iter T, usize)> {
        match self.set.entries.get(self.index) {
            Some((entry, multiplicity)) => {
                self.index += 1;
                Some((entry, *multiplicity))
            },
            None => None
        }
    }
}

pub(crate) struct VecMultiset<T> {
    entries: Vec<(T, usize)>
}

impl<T: Debug + PartialEq> Multiset<T> for VecMultiset<T> {
    type Iter<'iter> = VecMultisetIter<'iter, T>
    where
        T: 'iter,
        Self: 'iter;

    fn new() -> VecMultiset<T> {
        VecMultiset {
            entries: Vec::new()
        }
    }

    fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    fn iter<'reference>(&'reference self) -> Self::Iter<'reference>
    where
        T: 'reference
    {
        VecMultisetIter {
            set: self,
            index: 0
        }
    }

    fn add(&mut self, item: T) {
        for (contained_item, amount) in &mut self.entries {
            if contained_item == &item {
                *amount += 1;
                return;
            }
        }

        self.entries.push((item, 1));
    }

    fn remove(&mut self, item: &T) -> bool {
        for (index, (contained_item, amount)) in self.entries.iter_mut().enumerate() {
            if contained_item == item {
                *amount -= 1;

                if *amount == 0 {
                    self.entries.swap_remove(index);
                }

                return true;
            }
        }

        false
    }
}

impl<T: Debug + PartialEq> FromIterator<T> for VecMultiset<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> VecMultiset<T> {
        multiset::multiset_from_iter(iter)
    }
}

impl<T: Debug + PartialEq> Debug for VecMultiset<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        multiset::fmt_multiset_debug(self, f)
    }
}

#[cfg(test)]
mod tests {

    use crate::test_multiset_impl;
    use crate::util::multiset::Multiset;
    use crate::util::multiset::vec::VecMultiset;

    test_multiset_impl!(VecMultiset);
}
