use std::fmt::Debug;

pub(crate) mod vec;

pub(crate) trait Multiset<T> : Debug + FromIterator<T> {

    type Iter<'iter>: Iterator<Item = (&'iter T, usize)>
    where
        T: 'iter,
        Self: 'iter;

    fn new() -> Self;

    fn is_empty(&self) -> bool;

    fn iter<'reference>(&'reference self) -> Self::Iter<'reference>
    where
        T: 'reference;

    fn add(&mut self, item: T);

    fn remove(&mut self, item: &T) -> bool;
}
