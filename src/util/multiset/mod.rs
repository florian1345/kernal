use std::fmt::{self, Debug, Formatter};

pub(crate) mod btree;
pub(crate) mod hash;
pub(crate) mod vec;

/// A trait for multisets, which are unordered collections that can contain elements multiple times.
/// Equality of elements is defined via the [PartialEq] trait. Multiplicities are the cardinalities
/// of the [PartialEq]-equivalence classes. Implementations of this trait may use other traits (such
/// as [Hash](hash::Hash) or [Ord]) to make lookups faster.
pub(crate) trait Multiset<T> : Debug + FromIterator<T> {

    /// The type of iterator used by this multiset. It iterates over pairs whose left element is a
    /// representative of the [PartialEq]-equivalence-class of a set item and the right element its
    /// multiplicity.
    type Iter<'iter>: Iterator<Item = (&'iter T, usize)>
    where
        T: 'iter,
        Self: 'iter;

    /// Creates a new, empty multiset.
    fn new() -> Self;

    /// Indicates whether this multiset is empty, i.e. contains no elements.
    fn is_empty(&self) -> bool;

    /// An iterator over pairs whose left element is a representative of an
    /// [PartialEq]-equivalence-class contained in this multiset and the right element is the
    /// multiplicity of that element. It is guaranteed to never return any element with a
    /// multiplicity of 0.
    fn iter<'reference>(&'reference self) -> Self::Iter<'reference>
    where
        T: 'reference;

    /// Adds the given `item` to this set. If no equal item was contained, it will be added to the
    /// set with a multiplicity of 1. Otherwise, the multiplicity of the equal element will be
    /// increased by 1.
    fn add(&mut self, item: T);

    /// Removes the given `item` from this set, that is, decreases the multiplicity of the
    /// [PartialEq]-equivalence-class by 1. If that causes it to reach 0, the entry is removed
    /// completely, i.e. no longer returned by [Multiset::iter].
    ///
    /// Returns `true` if an equal element was found, otherwise returns `false` and does nothing.
    fn remove(&mut self, item: &T) -> bool;
}

fn multiset_from_iter<T, M: Multiset<T>, I: IntoIterator<Item = T>>(iter: I) -> M {
    let mut multiset = M::new();

    for item in iter {
        multiset.add(item);
    }

    multiset
}

fn fmt_multiset_debug<T, M>(multiset: &M, f: &mut Formatter<'_>) -> fmt::Result
where
    T: Debug + PartialEq,
    M: Multiset<T>
{
    for (index, (item, amount)) in multiset.iter().enumerate() {
        if index > 0 {
            write!(f, ", ")?;
        }

        write!(f, "{} of <{:?}>", amount, item)?;
    }

    Ok(())
}

trait MultisetMap<T> {

    fn get_mut(&mut self, item: &T) -> Option<&mut usize>;

    fn insert(&mut self, item: T);

    fn remove(&mut self, item: &T);
}

fn multiset_map_add<T, M: MultisetMap<T>>(multiset_map: &mut M, item: T) {
    if let Some(multiplicity) = multiset_map.get_mut(&item) {
        *multiplicity += 1;
    }
    else {
        multiset_map.insert(item);
    }
}

fn multiset_map_remove<T, M: MultisetMap<T>>(multiset_map: &mut M, item: &T) -> bool {
    if let Some(multiplicity) = multiset_map.get_mut(item) {
        *multiplicity -= 1;

        if *multiplicity == 0 {
            multiset_map.remove(item);
        }

        true
    }
    else {
        false
    }
}

#[cfg(test)]
mod tests {

    #[macro_export]
    macro_rules! test_multiset_impl {
        ($multiset_type:ident) => {
            use std::collections::HashSet;

            #[test]
            fn new_multiset_is_empty() {
                assert!($multiset_type::<String>::new().is_empty());
                assert!($multiset_type::<u32>::new().iter().next().is_none());
            }

            #[test]
            fn multiset_with_single_entry_is_not_empty() {
                let mut set = $multiset_type::new();
                set.add(1);

                assert!(!set.is_empty());
            }

            #[test]
            fn multiset_with_twice_the_same_element_collapses_to_single_entry() {
                let mut set = $multiset_type::new();
                set.add("hello");
                set.add("hello");
                let entries = set.iter().collect::<HashSet<_>>();

                assert_eq!(HashSet::from([(&"hello", 2)]), entries);
            }

            #[test]
            fn multiset_collapses_with_later_element() {
                let mut set = $multiset_type::new();
                set.add("hello");
                set.add("world");
                set.add("world");
                let entries = set.iter().collect::<HashSet<_>>();

                assert_eq!(HashSet::from([(&"hello", 1), (&"world", 2)]), entries);
            }

            #[test]
            fn multiset_converted_correctly_from_iterator() {
                let set: $multiset_type<u32> = [1, 2, 3, 2, 4, 2, 3].into_iter().collect();
                let entries = set.iter().collect::<HashSet<_>>();

                assert_eq!(HashSet::from([(&1, 1), (&2, 3), (&3, 2), (&4, 1)]), entries);
            }

            #[test]
            fn multiset_decreases_amount_when_removing_first_element() {
                let mut set: $multiset_type<u32> = [1, 1, 2, 3].into_iter().collect();
                let remove_result = set.remove(&1);
                let entries = set.iter().collect::<HashSet<_>>();

                assert!(remove_result);
                assert_eq!(HashSet::from([(&1, 1), (&2, 1), (&3, 1)]), entries);
            }

            #[test]
            fn multiset_removes_entry_when_removing_element_first_element() {
                let mut set: $multiset_type<u32> = [1, 2, 2].into_iter().collect();
                let remove_result = set.remove(&1);
                let entries = set.iter().collect::<HashSet<_>>();

                assert!(remove_result);
                assert_eq!(HashSet::from([(&2, 2)]), entries);
            }

            #[test]
            fn multiset_decreases_amount_when_removing_later_element() {
                let mut set: $multiset_type<u32> = [1, 2, 2, 2].into_iter().collect();
                let remove_result = set.remove(&2);
                let entries = set.iter().collect::<HashSet<_>>();

                assert!(remove_result);
                assert_eq!(HashSet::from([(&1, 1), (&2, 2)]), entries);
            }

            #[test]
            fn multiset_removes_entry_when_removing_element_later_element() {
                let mut set: $multiset_type<u32> = [1, 1, 2, 3].into_iter().collect();
                let remove_result = set.remove(&3);
                let entries = set.iter().collect::<HashSet<_>>();

                assert!(remove_result);
                assert_eq!(HashSet::from([(&1, 2), (&2, 1)]), entries);
            }

            #[test]
            fn multiset_returns_false_and_maintains_content_when_removing_element_not_contained() {
                let mut set: $multiset_type<u32> = [2, 3, 4].into_iter().collect();
                let remove_result = set.remove(&1);
                let entries = set.iter().collect::<HashSet<_>>();

                assert!(!remove_result);
                assert_eq!(HashSet::from([(&2, 1), (&3, 1), (&4, 1)]), entries);
            }
        }
    }
}
