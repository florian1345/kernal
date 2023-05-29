use std::fmt::Debug;

pub(crate) mod vec;

/// A trait for multisets, which are unordered collections that can contain elements multiple times.
/// Equality of elements is defined via the [PartialEq] trait. Multiplicities are the cardinalities
/// of the [PartialEq]-equivalence classes. Implementations of this trait may use other traits (such
/// as [Hash](std::hash::Hash) or [Ord]) to make lookups faster.
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
