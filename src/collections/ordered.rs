use std::collections::{BTreeSet, LinkedList, VecDeque};

use crate::collections::Collection;

/// A marker trait for ordered [Collection]s whose item ordering is deliberate, specified by the
/// iteration order of [Collection::iterator]. It is implemented for all ordered collection types of
/// the standard library.
pub trait OrderedCollection<'collection>: Collection<'collection> {}

impl<'collection, T: 'collection> OrderedCollection<'collection> for [T] {}

impl<'collection, T: 'collection, const N: usize> OrderedCollection<'collection> for [T; N] {}

impl<'collection, T: 'collection> OrderedCollection<'collection> for Vec<T> {}

impl<'collection, T: 'collection> OrderedCollection<'collection> for VecDeque<T> {}

impl<'collection, T: 'collection> OrderedCollection<'collection> for LinkedList<T> {}

impl<'collection, T: 'collection> OrderedCollection<'collection> for BTreeSet<T> {}

impl<'collection, C> OrderedCollection<'collection> for &C
where
    C: OrderedCollection<'collection> + ?Sized + 'collection
{}

impl<'collection, C> OrderedCollection<'collection> for &mut C
where
    C: OrderedCollection<'collection> + ?Sized + 'collection
{}

impl<'collection, C> OrderedCollection<'collection> for Box<C>
where
    C: OrderedCollection<'collection> + ?Sized
{}
