use std::borrow::Borrow;
use std::fmt::{Debug, Formatter};
use std::fmt;

pub(crate) fn borrow_all<T, B: Borrow<T>>(to_borrow: &[B]) -> Vec<&T> {
    to_borrow.iter().map(|b| b.borrow()).collect()
}

pub(crate) fn borrow_all_pairs<L, R, LB, RB>(to_borrow: &[(LB, RB)]) -> Vec<(&L, &R)>
where
    LB: Borrow<L>,
    RB: Borrow<R>
{
    to_borrow.iter().map(|(l, r)| (l.borrow(), r.borrow())).collect()
}

pub(crate) struct VecMultiset<T> {
    entries: Vec<(T, usize)>
}

impl<T> VecMultiset<T> {
    pub(crate) fn new() -> VecMultiset<T> {
        VecMultiset {
            entries: Vec::new()
        }
    }
}

impl<T> VecMultiset<T> {
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = (&T, usize)> {
        self.entries.iter().map(|(item, amount)| (item, *amount))
    }
}

impl<T: PartialEq> VecMultiset<T> {
    pub(crate) fn add(&mut self, item: T) {
        for (contained_item, amount) in &mut self.entries {
            if contained_item == &item {
                *amount += 1;
                return;
            }
        }

        self.entries.push((item, 1));
    }

    pub(crate) fn remove(&mut self, item: &T) -> bool {
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

impl<T: PartialEq> FromIterator<T> for VecMultiset<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut multiset = VecMultiset::new();

        for item in iter {
            multiset.add(item);
        }

        multiset
    }
}

impl<T: Debug> Debug for VecMultiset<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for (index, (item, amount)) in self.iter().enumerate() {
            if index > 0 {
                write!(f, ", ")?;
            }

            write!(f, "{} of <{:?}>", amount, item)?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {

    use crate::util::VecMultiset;

    #[test]
    fn new_vec_multiset_is_empty() {
        assert!(VecMultiset::<String>::new().is_empty());
        assert!(VecMultiset::<u32>::new().iter().next().is_none());
    }

    #[test]
    fn vec_multiset_with_single_entry_is_not_empty() {
        let mut set = VecMultiset::new();
        set.add(1);

        assert!(!set.is_empty());
    }

    #[test]
    fn vec_multiset_with_twice_the_same_element_collapses_to_single_entry() {
        let mut set = VecMultiset::new();
        set.add("hello");
        set.add("hello");
        let entries = set.iter().collect::<Vec<_>>();

        assert_eq!(&[(&"hello", 2)], entries.as_slice());
    }

    #[test]
    fn vec_multiset_collapses_with_later_element() {
        let mut set = VecMultiset::new();
        set.add("hello");
        set.add("world");
        set.add("world");
        let entries = set.iter().collect::<Vec<_>>();

        assert_eq!(&[(&"hello", 1), (&"world", 2)], entries.as_slice());
    }

    #[test]
    fn vec_multiset_converted_correctly_from_iterator() {
        let set: VecMultiset<u32> = [1, 2, 3, 2, 4, 2, 3].into_iter().collect();
        let entries = set.iter().collect::<Vec<_>>();

        assert_eq!(&[(&1, 1), (&2, 3), (&3, 2), (&4, 1)], entries.as_slice());
    }

    #[test]
    fn vec_multiset_decreases_amount_when_removing_element_contained_multiple_times() {
        let mut set: VecMultiset<u32> = [1, 2, 2, 3].into_iter().collect();
        set.remove(&2);
        let entries = set.iter().collect::<Vec<_>>();

        assert_eq!(&[(&1, 1), (&2, 1), (&3, 1)], entries.as_slice());
    }

    #[test]
    fn vec_multiset_removes_entry_when_removing_element_contained_once() {
        let mut set: VecMultiset<u32> = [1, 2, 2].into_iter().collect();
        set.remove(&1);
        let entries = set.iter().collect::<Vec<_>>();

        assert_eq!(&[(&2, 2)], entries.as_slice());
    }
}
