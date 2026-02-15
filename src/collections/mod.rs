//! Defines the basic [Collection] trait to generalize collections such as sets and lists.
//! Additional assertions for collections are provided by [CollectionAssertions]. Sub-modules
//! provide further specialization.

use std::borrow::Borrow;
use std::cmp::Ordering;
use std::collections::binary_heap::Iter as BinaryHeapIter;
use std::collections::btree_set::Iter as BTreeSetIter;
use std::collections::hash_set::Iter as HashSetIter;
use std::collections::linked_list::Iter as LinkedListIter;
use std::collections::vec_deque::Iter as VecDequeIter;
use std::collections::{BTreeSet, BinaryHeap, HashSet, LinkedList, VecDeque};
use std::fmt::{self, Debug, Formatter};
use std::ops::Range;
use std::slice::Iter as SliceIter;

use crate::collections::ordered::OrderedCollection;
use crate::util::borrow_all;
use crate::{AssertThat, AssertThatData, Failure};

pub mod abs_diff;
pub mod ord;
pub mod ordered;
pub mod partial_eq;
pub mod partial_ord;

/// A trait for all collections which contain one kind of item, such as slices or sets. This
/// contrasts with maps, which have keys and values, i.e. two kinds of items.
///
/// The content of a collection is defined by an iterator. Although this will imply an ordering, not
/// all collections have to be semantically ordered. Such collections are marked by the
/// [OrderedCollection] trait.
///
/// This trait is required to allow collection-based assertions. It is implemented on all common
/// collection types in the standard library and references thereof.
pub trait Collection {
    /// The type of the items/elements contained in this collection.
    type Item;

    /// The type of the iterators which can iterate over references of this collection's items.
    type Iter<'iter>: Iterator<Item = &'iter Self::Item>
    where
        Self: 'iter;

    /// Indicates whether this collection is empty, i.e. it has the length 0 according to
    /// [Collection::len].
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the number of elements in this collection. By default, this is implemented by
    /// counting the number of items in the iterator. It may be implemented in a more efficient way.
    fn len(&self) -> usize {
        self.iterator().count()
    }

    /// Returns a new iterator over the items in this collection. If the collection is ordered, the
    /// iterator returns the items in the ordering defined by the collection, otherwise the ordering
    /// is not specified.
    fn iterator(&self) -> Self::Iter<'_>;
}

impl<T, const LEN: usize> Collection for [T; LEN] {
    type Item = T;
    type Iter<'iter>
        = SliceIter<'iter, T>
    where
        T: 'iter;

    fn len(&self) -> usize {
        LEN
    }

    fn iterator(&self) -> SliceIter<'_, T> {
        self.iter()
    }
}

macro_rules! impl_collection {
    ($collection_type:ty, $iterator_type:ident) => {
        impl<T> Collection for $collection_type {
            type Item = T;
            type Iter<'iter>
                = $iterator_type<'iter, T>
            where
                T: 'iter;

            fn len(&self) -> usize {
                <$collection_type>::len(self)
            }

            fn iterator(&self) -> $iterator_type<'_, T> {
                self.iter()
            }
        }
    };
}

impl_collection!([T], SliceIter);
impl_collection!(Vec<T>, SliceIter);
impl_collection!(VecDeque<T>, VecDequeIter);
impl_collection!(LinkedList<T>, LinkedListIter);
impl_collection!(BinaryHeap<T>, BinaryHeapIter);
impl_collection!(HashSet<T>, HashSetIter);
impl_collection!(BTreeSet<T>, BTreeSetIter);

impl<T> Collection for &T
where
    T: Collection + ?Sized,
{
    type Item = T::Item;
    type Iter<'iter>
        = T::Iter<'iter>
    where
        Self: 'iter,
        T: 'iter;

    fn len(&self) -> usize {
        (**self).len()
    }

    fn iterator(&self) -> T::Iter<'_> {
        (**self).iterator()
    }
}

impl<T> Collection for &mut T
where
    T: Collection + ?Sized,
{
    type Item = T::Item;
    type Iter<'iter>
        = T::Iter<'iter>
    where
        Self: 'iter,
        T: 'iter;

    fn len(&self) -> usize {
        (**self).len()
    }

    fn iterator(&self) -> T::Iter<'_> {
        (**self).iterator()
    }
}

impl<T> Collection for Box<T>
where
    T: Collection + ?Sized,
{
    type Item = T::Item;
    type Iter<'iter>
        = T::Iter<'iter>
    where
        Self: 'iter,
        T: 'iter;

    fn len(&self) -> usize {
        (**self).len()
    }

    fn iterator(&self) -> Self::Iter<'_> {
        self.as_ref().iterator()
    }
}

fn write_delimiter(f: &mut Formatter, index: usize) -> fmt::Result {
    if index > 0 {
        write!(f, ",")?;
    }

    write!(f, " ")
}

pub(crate) struct CollectionDebug<'wrapper, C> {
    pub(crate) collection: &'wrapper C,
}

impl<C> Debug for CollectionDebug<'_, C>
where
    C: Collection,
    C::Item: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;

        for (index, item) in self.collection.iterator().enumerate() {
            let item: &C::Item = item;

            write_delimiter(f, index)?;
            write!(f, "{:?}", item)?;
        }

        write!(f, " ]")
    }
}

pub(crate) struct HighlightedCollectionDebug<C> {
    pub(crate) collection: C,
    pub(crate) highlighted_sections: Vec<Range<usize>>,
}

impl<C> HighlightedCollectionDebug<C> {
    pub(crate) fn with_single_highlighted_element(
        collection: C,
        highlighted_index: usize,
    ) -> HighlightedCollectionDebug<C> {
        HighlightedCollectionDebug {
            collection,
            highlighted_sections: vec![highlighted_index..(highlighted_index + 1)],
        }
    }
}

fn open_and_close_section_before_item_if_applicable(
    f: &mut Formatter<'_>,
    next_highlighted_section: Option<&Range<usize>>,
    current_index: usize,
) -> Result<bool, fmt::Error> {
    if let Some(next_highlighted_section) = next_highlighted_section {
        if next_highlighted_section.start == current_index {
            write!(f, "[")?;

            if next_highlighted_section.end == current_index {
                write!(f, "] ")?;
                return Ok(true);
            }
        }
    }

    Ok(false)
}

fn close_section_after_item_if_applicable(
    f: &mut Formatter<'_>,
    next_highlighted_section: Option<&Range<usize>>,
    current_index: usize,
) -> Result<bool, fmt::Error> {
    if let Some(next_highlighted_section) = next_highlighted_section {
        let next_index = current_index + 1;

        if next_index == next_highlighted_section.end
            && next_index != next_highlighted_section.start
        {
            write!(f, "]")?;
            return Ok(true);
        }
    }

    Ok(false)
}

impl<C> Debug for HighlightedCollectionDebug<C>
where
    C: Collection,
    C::Item: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut highlighted_sections_iter = self.highlighted_sections.iter();
        let mut next_highlighted_section = highlighted_sections_iter.next();

        write!(f, "[")?;

        for (index, item) in self.collection.iterator().enumerate() {
            let item: &C::Item = item;

            write_delimiter(f, index)?;
            let mut section_closed = open_and_close_section_before_item_if_applicable(
                f,
                next_highlighted_section,
                index,
            )?;
            write!(f, "{:?}", item)?;
            section_closed |=
                close_section_after_item_if_applicable(f, next_highlighted_section, index)?;

            if section_closed {
                next_highlighted_section = highlighted_sections_iter.next();
            }
        }

        if next_highlighted_section.is_some() {
            write!(f, " []")?;
        }

        write!(f, " ]")
    }
}

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with an
/// argument that implements the [Collection] trait. The [Collection::Item] type must implement
/// [Debug].
///
/// Examples:
///
/// ```
/// use kernal::prelude::*;
///
/// use std::collections::HashSet;
///
/// assert_that!(vec![1, 2, 3])
///     .is_not_empty()
///     .has_length(3)
///     .contains_elements_matching(|i| i % 2 == 0);
/// assert_that!(HashSet::<String>::new())
///     .is_empty()
///     .has_length_less_than(10)
///     .contains_only_elements_matching(String::is_empty);
/// ```
pub trait CollectionAssertions<C>
where
    C: Collection,
{
    /// Asserts that the tested collection is empty, i.e. contains no elements.
    fn is_empty(self) -> Self;

    /// Asserts that the tested collection is not empty, i.e. contains at least one element.
    fn is_not_empty(self) -> Self;

    /// Asserts that the number of elements contained in the tested collection is equal to the given
    /// `expected_length`.
    fn has_length(self, expected_length: usize) -> Self;

    /// Asserts that the number of elements contained in the tested collection is less than the
    /// given `length_bound`.
    fn has_length_less_than(self, length_bound: usize) -> Self;

    /// Asserts that the number of elements contained in the tested collection is less than or equal
    /// to the given `length_bound`.
    fn has_length_less_than_or_equal_to(self, length_bound: usize) -> Self;

    /// Asserts that the number of elements contained in the tested collection is greater than the
    /// given `length_bound`.
    fn has_length_greater_than(self, length_bound: usize) -> Self;

    /// Asserts that the number of elements contained in the tested collection is greater than or
    /// equal to the given `length_bound`.
    fn has_length_greater_than_or_equal_to(self, length_bound: usize) -> Self;

    /// Asserts that the number of elements contained in the tested collection is different from the
    /// given `unexpected_length`.
    fn does_not_have_length(self, unexpected_length: usize) -> Self;

    /// Asserts that the collection contains at least one element for which the given `predicate`
    /// returns `true`. In particular, an empty collection cannot satisfy this assertion.
    fn contains_elements_matching<F: FnMut(&C::Item) -> bool>(self, predicate: F) -> Self;

    /// Asserts that for all elements of the tested collection, the given `predicate` returns
    /// `true`. In other words, for no element in the collection, the predicate returns `false`. In
    /// particular, an empty collection always satisfies this assertion.
    fn contains_only_elements_matching<F: FnMut(&C::Item) -> bool>(self, predicate: F) -> Self;

    /// Asserts that the collection contains no elements for which the given `predicate` returns
    /// `true`. In particular, an empty collection always satisfies this assertion.
    fn does_not_contain_elements_matching<F: FnMut(&C::Item) -> bool>(self, predicate: F) -> Self;

    // TODO find a solution that does not require a reference here

    /// Asserts that the tested collection has exactly one element and returns an [AssertThat] for
    /// further assertions on a reference to that element.
    ///
    /// Due to restrictions in the current type setup, this method returns values referencing the
    /// collection. Therefore, it must be executed on a reference of the current [AssertThat]. It is
    /// still intended and recommended to be used in a call chain as all other assertions.
    fn to_single_element(&self) -> AssertThat<&C::Item>;

    /// Asserts that the tested collection contains exactly one element and that element satisfies
    /// the given `predicate`.
    fn is_single_element_matching<F: FnMut(&C::Item) -> bool>(self, predicate: F) -> Self;
}

fn assert_length_predicate<C, F>(
    assert_that: AssertThat<C>,
    length_predicate: F,
    reference_len: usize,
    expected_it_prefix: &str,
) -> AssertThat<C>
where
    C: Collection,
    C::Item: Debug,
    F: Fn(usize) -> bool,
{
    let len = assert_that.data.len();

    if !length_predicate(len) {
        let collection_debug = CollectionDebug {
            collection: &assert_that.data,
        };

        Failure::new(&assert_that)
            .expected_it(format!("{} <{}>", expected_it_prefix, reference_len))
            .but_it(format!(
                "was <{:?}> with length <{}>",
                collection_debug, len
            ))
            .fail();
    }

    assert_that
}

fn assert_all_match_predicate<C, F>(
    assert_that: AssertThat<C>,
    mut item_predicate: F,
    expected_it: &str,
) -> AssertThat<C>
where
    C: Collection,
    C::Item: Debug,
    F: FnMut(&C::Item) -> bool,
{
    let counter_example_with_index = assert_that
        .data
        .iterator()
        .enumerate()
        .find(|(_, item)| !item_predicate(item));

    if let Some((counter_example_index, _)) = counter_example_with_index {
        Failure::new(&assert_that)
            .expected_it(expected_it)
            .but_it(format!(
                "was <{:?}>",
                HighlightedCollectionDebug::with_single_highlighted_element(
                    &assert_that.data,
                    counter_example_index
                )
            ))
            .fail();
    }

    assert_that
}

/// Asserts that each item at position X in the collection of the given `assert_that` (`actual`) and
/// the item at position X in `items` (`expected`) satisfy `comparator(expected, actual)`. If a
/// violation is found, a failure is produced with an `expected_it` of `"to contain exactly in the
/// given order {items}"` suffixed with the given `expected_it_suffix`.
fn assert_contains_exactly_in_given_order_by<C, E, I, F>(
    assert_that: AssertThat<C>,
    items: I,
    comparator: F,
    expected_it_suffix: &str,
) -> AssertThat<C>
where
    C: OrderedCollection,
    C::Item: Debug,
    E: Borrow<C::Item>,
    I: IntoIterator<Item = E>,
    F: Fn(&C::Item, &C::Item) -> bool,
{
    let expected_items_unborrowed = items.into_iter().collect::<Vec<_>>();
    let expected_items: Vec<&C::Item> = borrow_all(&expected_items_unborrowed);
    let collection_len = assert_that.data.len();

    let counter_example_section = match collection_len.cmp(&expected_items.len()) {
        Ordering::Less => Some(collection_len..collection_len),
        Ordering::Greater => Some(expected_items.len()..collection_len),
        Ordering::Equal => expected_items
            .iter()
            .zip(assert_that.data.iterator())
            .enumerate()
            .find(|(_, (expected_item, collection_item))| {
                !comparator(expected_item, collection_item)
            })
            .map(|(index, _)| index..(index + 1)),
    };

    if let Some(counter_example_section) = counter_example_section {
        let expected_items_debug = CollectionDebug {
            collection: &expected_items,
        };
        let collection_debug = HighlightedCollectionDebug {
            collection: &assert_that.data,
            highlighted_sections: vec![counter_example_section],
        };

        Failure::new(&assert_that)
            .expected_it(format!(
                "to contain exactly in the given order <{:?}>{}",
                expected_items_debug, expected_it_suffix
            ))
            .but_it(format!("was <{:?}>", collection_debug))
            .fail();
    }

    assert_that
}

fn extract_single_element<C>(
    assert_that: &AssertThat<C>,
    expected_it: impl Into<String>,
) -> &C::Item
where
    C: Collection,
    C::Item: Debug,
{
    let mut iter = assert_that.data().iterator();
    let Some(first) = iter.next()
    else {
        Failure::new(assert_that)
            .expected_it(expected_it)
            .but_it("was empty")
            .fail()
    };

    let len = assert_that.data().len();

    if len > 1 {
        Failure::new(assert_that)
            .expected_it(expected_it)
            .but_it(format!(
                "was <{:?}>, which has length <{}>",
                CollectionDebug {
                    collection: assert_that.data()
                },
                len
            ))
            .fail();
    }

    first
}

impl<C> CollectionAssertions<C> for AssertThat<C>
where
    C: Collection,
    C::Item: Debug,
{
    fn is_empty(self) -> Self {
        if !self.data.is_empty() {
            Failure::new(&self)
                .expected_it("to be empty")
                .but_it(format!(
                    "was <{:?}>",
                    CollectionDebug {
                        collection: &self.data
                    }
                ))
                .fail();
        }

        self
    }

    fn is_not_empty(self) -> Self {
        if self.data.is_empty() {
            Failure::new(&self)
                .expected_it("not to be empty")
                .but_it("was")
                .fail();
        }

        self
    }

    fn has_length(self, expected_length: usize) -> Self {
        assert_length_predicate(
            self,
            |len| len == expected_length,
            expected_length,
            "to have length",
        )
    }

    fn has_length_less_than(self, length_bound: usize) -> Self {
        assert_length_predicate(
            self,
            |len| len < length_bound,
            length_bound,
            "to have length less than",
        )
    }

    fn has_length_less_than_or_equal_to(self, length_bound: usize) -> Self {
        assert_length_predicate(
            self,
            |len| len <= length_bound,
            length_bound,
            "to have length less than or equal to",
        )
    }

    fn has_length_greater_than(self, length_bound: usize) -> Self {
        assert_length_predicate(
            self,
            |len| len > length_bound,
            length_bound,
            "to have length greater than",
        )
    }

    fn has_length_greater_than_or_equal_to(self, length_bound: usize) -> Self {
        assert_length_predicate(
            self,
            |len| len >= length_bound,
            length_bound,
            "to have length greater than or equal to",
        )
    }

    fn does_not_have_length(self, unexpected_length: usize) -> Self {
        assert_length_predicate(
            self,
            |len| len != unexpected_length,
            unexpected_length,
            "not to have length",
        )
    }

    fn contains_elements_matching<F: FnMut(&C::Item) -> bool>(self, predicate: F) -> Self {
        if !self.data.iterator().any(predicate) {
            Failure::new(&self)
                .expected_it("to contain elements matching predicate")
                .but_it(format!(
                    "was <{:?}>",
                    CollectionDebug {
                        collection: &self.data
                    }
                ))
                .fail();
        }

        self
    }

    fn contains_only_elements_matching<F: FnMut(&C::Item) -> bool>(self, predicate: F) -> Self {
        assert_all_match_predicate(
            self,
            predicate,
            "to contain only elements matching predicate",
        )
    }

    fn does_not_contain_elements_matching<F: FnMut(&C::Item) -> bool>(
        self,
        mut predicate: F,
    ) -> Self {
        assert_all_match_predicate(
            self,
            |item| !predicate(item),
            "not to contain elements matching predicate",
        )
    }

    fn to_single_element(&self) -> AssertThat<&C::Item> {
        AssertThat {
            data: extract_single_element(self, "to contain exactly one element"),
            expression: format!("single element of <{}>", self.expression),
        }
    }

    fn is_single_element_matching<F: FnMut(&C::Item) -> bool>(self, mut predicate: F) -> Self {
        let expected_it = "to contain exactly one element, which matches the given predicate";
        let single_element = extract_single_element(&self, expected_it);

        if !predicate(single_element) {
            Failure::new(&self)
                .expected_it(expected_it)
                .but_it(format!(
                    "contained single element <{:?}>, which does not match the predicate",
                    single_element
                ))
                .fail()
        }

        self
    }
}

fn find_contiguous_subsequence_by<C, F>(
    collection: &C,
    subsequence: &[&C::Item],
    mut matches: F,
) -> Option<Vec<Range<usize>>>
where
    C: OrderedCollection,
    F: FnMut(&C::Item, &C::Item) -> bool,
{
    let collection_vec = collection.iterator().collect::<Vec<_>>();

    if collection_vec.len() < subsequence.len() {
        return None;
    }

    for start in 0..=(collection_vec.len() - subsequence.len()) {
        let range = start..(start + subsequence.len());
        let slice = &collection_vec[range.clone()];

        if slice
            .iter()
            .zip(subsequence.iter())
            .all(|(item_1, item_2)| matches(item_1, item_2))
        {
            return Some(vec![range]);
        }
    }

    None
}

fn find_subsequence_by<C, F>(
    collection: &C,
    subsequence: &[&C::Item],
    mut matches: F,
) -> Option<Vec<Range<usize>>>
where
    C: OrderedCollection,
    F: FnMut(&C::Item, &C::Item) -> bool,
{
    if subsequence.is_empty() {
        return Some(vec![0..0]);
    }

    let mut ranges = Vec::new();
    let mut current_range_start = None;
    let mut subsequence_iterator = subsequence.iter().cloned().peekable();

    for (index, item) in collection.iterator().enumerate() {
        let next = subsequence_iterator.peek();

        if next.is_some_and(|subsequence_item| matches(item, subsequence_item)) {
            current_range_start.get_or_insert(index);
            subsequence_iterator.next();
        }
        else if let Some(current_range_start) = current_range_start.take() {
            ranges.push(current_range_start..index);

            if next.is_none() {
                break;
            }
        }
    }

    if let Some(last_range_start) = current_range_start {
        ranges.push(last_range_start..collection.len());
    }

    if subsequence_iterator.next().is_some() {
        None
    }
    else {
        Some(ranges)
    }
}

fn find_prefix_by<C, F>(
    collection: &C,
    prefix: &[&C::Item],
    mut matches: F,
) -> Option<Vec<Range<usize>>>
where
    C: OrderedCollection,
    F: FnMut(&C::Item, &C::Item) -> bool,
{
    if collection.len() < prefix.len() {
        return None;
    }

    let has_prefix = collection
        .iterator()
        .zip(prefix.iter())
        .all(|(item_1, item_2)| matches(item_1, item_2));

    if has_prefix {
        Some(vec![0..prefix.len()])
    }
    else {
        None
    }
}

fn find_suffix_by<C, F>(
    collection: &C,
    suffix: &[&C::Item],
    mut matches: F,
) -> Option<Vec<Range<usize>>>
where
    C: OrderedCollection,
    F: FnMut(&C::Item, &C::Item) -> bool,
{
    if collection.len() < suffix.len() {
        return None;
    }

    let collection_suffix_start = collection.len() - suffix.len();
    let has_suffix = collection
        .iterator()
        .skip(collection_suffix_start)
        .zip(suffix.iter())
        .all(|(item_1, item_2)| matches(item_1, item_2));

    if has_suffix {
        Some(vec![collection_suffix_start..collection.len()])
    }
    else {
        None
    }
}

#[cfg(test)]
mod tests {
    use std::slice::Iter;

    use super::*;
    use crate::assert_fails;
    use crate::prelude::*;

    struct MockCollection(Vec<u32>);

    impl Collection for MockCollection {
        type Item = u32;
        type Iter<'iter>
            = Iter<'iter, u32>
        where
            Self: 'iter;

        fn iterator(&self) -> Iter<'_, u32> {
            self.0.iter()
        }
    }

    #[test]
    fn default_collection_len_works_for_empty_collection() {
        assert_that!(MockCollection(vec![])).has_length(0);
    }

    #[test]
    fn default_collection_len_works_for_non_empty_collection() {
        assert_that!(MockCollection(vec![1, 2, 3])).has_length(3);
    }

    #[test]
    fn highlighted_collection_debug_prints_collection_without_highlighted_sections() {
        let highlighted_collection_debug = HighlightedCollectionDebug {
            collection: &[1, 2, 3],
            highlighted_sections: vec![],
        };
        let formatted = format!("{:?}", highlighted_collection_debug);

        assert_eq!("[ 1, 2, 3 ]", formatted);
    }

    #[test]
    fn highlighted_collection_debug_works_with_singleton_section() {
        let highlighted_collection_debug = HighlightedCollectionDebug {
            collection: &[1, 2, 3],
            highlighted_sections: vec![1..2],
        };
        let formatted = format!("{:?}", highlighted_collection_debug);

        assert_eq!("[ 1, [2], 3 ]", formatted);
    }

    #[test]
    fn highlighted_collection_debug_works_with_empty_section() {
        let highlighted_collection_debug = HighlightedCollectionDebug {
            collection: &[1, 2, 3],
            highlighted_sections: vec![1..1],
        };
        let formatted = format!("{:?}", highlighted_collection_debug);

        assert_eq!("[ 1, [] 2, 3 ]", formatted);
    }

    #[test]
    fn highlighted_collection_debug_works_with_separated_sections() {
        let highlighted_collection_debug = HighlightedCollectionDebug {
            collection: &[1, 2, 3, 4, 5],
            highlighted_sections: vec![0..1, 2..4],
        };
        let formatted = format!("{:?}", highlighted_collection_debug);

        assert_eq!("[ [1], 2, [3, 4], 5 ]", formatted);
    }

    #[test]
    fn highlighted_collection_debug_works_with_consecutive_sections() {
        let highlighted_collection_debug = HighlightedCollectionDebug {
            collection: &[1, 2, 3],
            highlighted_sections: vec![0..1, 1..2],
        };
        let formatted = format!("{:?}", highlighted_collection_debug);

        assert_eq!("[ [1], [2], 3 ]", formatted);
    }

    #[test]
    fn highlighted_collection_debug_works_with_consecutive_empty_sections() {
        let highlighted_collection_debug = HighlightedCollectionDebug {
            collection: &[1, 2, 3],
            highlighted_sections: vec![0..0, 1..1],
        };
        let formatted = format!("{:?}", highlighted_collection_debug);

        assert_eq!("[ [] 1, [] 2, 3 ]", formatted);
    }

    #[test]
    fn highlighted_collection_debug_correctly_renders_empty_section_in_end() {
        let highlighted_collection_debug = HighlightedCollectionDebug {
            collection: &[1, 2, 3],
            highlighted_sections: vec![3..3],
        };
        let formatted = format!("{:?}", highlighted_collection_debug);

        assert_eq!("[ 1, 2, 3 [] ]", formatted);
    }

    #[test]
    fn highlighted_collection_debug_with_single_highlighted_element_works_correctly() {
        let highlighted_collection_debug =
            HighlightedCollectionDebug::with_single_highlighted_element(&[1, 2, 3], 1);
        let formatted = format!("{:?}", highlighted_collection_debug);

        assert_eq!("[ 1, [2], 3 ]", formatted);
    }

    #[test]
    fn is_empty_passes_for_mutable_ref_to_empty_set() {
        let mut set: HashSet<String> = HashSet::new();

        assert_that!(&mut set).is_empty();
    }

    #[test]
    fn is_empty_fails_for_non_empty_boxed_slice() {
        assert_fails!((vec![1, 2, 3].into_boxed_slice()).is_empty(),
            expected it "to be empty"
            but it "was <[ 1, 2, 3 ]>");
    }

    #[test]
    fn is_not_empty_passes_for_empty_slice() {
        let array: [u32; 2] = [0, 1];

        assert_that!(&array).is_not_empty();
    }

    #[test]
    fn is_not_empty_passes_for_empty_vec() {
        assert_fails!((Vec::<u8>::new()).is_not_empty(),
            expected it "not to be empty"
            but it "was");
    }

    #[test]
    fn has_length_passes_for_tree_set_of_equal_length() {
        let set = [1, 2, 3].into_iter().collect::<BTreeSet<_>>();

        assert_that!(set).has_length(3);
    }

    #[test]
    fn has_length_fails_for_vec_deque_of_greater_length() {
        let deque = [1, 2, 3].into_iter().collect::<VecDeque<_>>();

        assert_fails!((deque).has_length(2),
            expected it "to have length <2>"
            but it "was <[ 1, 2, 3 ]> with length <3>");
    }

    #[test]
    fn has_length_fails_for_linked_list_of_lesser_length() {
        let list = [1, 2, 3].into_iter().collect::<LinkedList<_>>();

        assert_fails!((list).has_length(4),
            expected it "to have length <4>"
            but it "was <[ 1, 2, 3 ]> with length <3>");
    }

    #[test]
    fn has_length_less_than_passes_for_linked_list_of_lesser_length() {
        let list = [1, 2, 3].into_iter().collect::<LinkedList<_>>();

        assert_that!(list).has_length_less_than(4);
    }

    #[test]
    fn has_length_less_than_fails_for_tree_set_of_equal_length() {
        let set = [1, 2, 3].into_iter().collect::<BTreeSet<_>>();

        assert_fails!((set).has_length_less_than(3),
            expected it "to have length less than <3>"
            but it "was <[ 1, 2, 3 ]> with length <3>");
    }

    #[test]
    fn has_length_less_than_fails_for_vec_deque_of_greater_length() {
        let deque = [1, 2, 3].into_iter().collect::<VecDeque<_>>();

        assert_fails!((deque).has_length_less_than(2),
            expected it "to have length less than <2>"
            but it "was <[ 1, 2, 3 ]> with length <3>");
    }

    #[test]
    fn has_length_less_than_or_equal_to_passes_for_linked_list_of_lesser_length() {
        let list = [1, 2, 3].into_iter().collect::<LinkedList<_>>();

        assert_that!(list).has_length_less_than_or_equal_to(4);
    }

    #[test]
    fn has_length_less_than_or_equal_to_passes_for_tree_set_of_equal_length() {
        let set = [1, 2, 3].into_iter().collect::<BTreeSet<_>>();

        assert_that!(set).has_length_less_than_or_equal_to(3);
    }

    #[test]
    fn has_length_less_than_or_equal_to_fails_for_vec_deque_of_greater_length() {
        let deque = [1, 2, 3].into_iter().collect::<VecDeque<_>>();

        assert_fails!((deque).has_length_less_than_or_equal_to(2),
            expected it "to have length less than or equal to <2>"
            but it "was <[ 1, 2, 3 ]> with length <3>");
    }

    #[test]
    fn has_length_greater_than_passes_for_vec_deque_of_greater_length() {
        let deque = [1, 2, 3].into_iter().collect::<VecDeque<_>>();

        assert_that!(deque).has_length_greater_than(2);
    }

    #[test]
    fn has_length_greater_than_fails_for_linked_list_of_lesser_length() {
        let list = [1, 2, 3].into_iter().collect::<LinkedList<_>>();

        assert_fails!((list).has_length_greater_than(4),
            expected it "to have length greater than <4>"
            but it "was <[ 1, 2, 3 ]> with length <3>");
    }

    #[test]
    fn has_length_greater_than_fails_for_tree_set_of_equal_length() {
        let set = [1, 2, 3].into_iter().collect::<BTreeSet<_>>();

        assert_fails!((set).has_length_greater_than(3),
            expected it "to have length greater than <3>"
            but it "was <[ 1, 2, 3 ]> with length <3>");
    }

    #[test]
    fn has_length_greater_than_or_equal_to_passes_for_tree_set_of_equal_length() {
        let set = [1, 2, 3].into_iter().collect::<BTreeSet<_>>();

        assert_that!(set).has_length_greater_than_or_equal_to(3);
    }

    #[test]
    fn has_length_greater_than_or_equal_to_passes_for_vec_deque_of_greater_length() {
        let deque = [1, 2, 3].into_iter().collect::<VecDeque<_>>();

        assert_that!(deque).has_length_greater_than_or_equal_to(2);
    }

    #[test]
    fn has_length_greater_than_or_equal_to_fails_for_linked_list_of_lesser_length() {
        let list = [1, 2, 3].into_iter().collect::<LinkedList<_>>();

        assert_fails!((list).has_length_greater_than_or_equal_to(4),
            expected it "to have length greater than or equal to <4>"
            but it "was <[ 1, 2, 3 ]> with length <3>");
    }

    #[test]
    fn does_not_have_length_passes_for_vec_deque_of_greater_length() {
        let deque = [1, 2, 3].into_iter().collect::<VecDeque<_>>();

        assert_that!(deque).does_not_have_length(2);
    }

    #[test]
    fn does_not_have_length_passes_for_linked_list_of_lesser_length() {
        let list = [1, 2, 3].into_iter().collect::<LinkedList<_>>();

        assert_that!(list).does_not_have_length(4);
    }

    #[test]
    fn does_not_have_length_fails_for_tree_set_of_equal_length() {
        let set = [1, 2, 3].into_iter().collect::<BTreeSet<_>>();

        assert_fails!((set).does_not_have_length(3),
            expected it "not to have length <3>"
            but it "was <[ 1, 2, 3 ]> with length <3>");
    }

    #[test]
    fn contains_elements_matching_passes_for_hash_set_of_single_matching_element() {
        let set = [""].into_iter().collect::<HashSet<_>>();

        assert_that!(set).contains_elements_matching(|&s| s.is_empty());
    }

    #[test]
    fn contains_elements_matching_passes_for_mixed_mut_slice() {
        assert_that!(&mut ["a", ""]).contains_elements_matching(|&s| s.is_empty());
    }

    #[test]
    fn contains_elements_matching_fails_for_empty_slice() {
        assert_fails!((&[] as &[&str]).contains_elements_matching(|&s| s.is_empty()),
            expected it "to contain elements matching predicate"
            but it "was <[ ]>");
    }

    #[test]
    fn contains_elements_matching_fails_for_slice_of_single_non_matching_element() {
        assert_fails!((&["a"]).contains_elements_matching(|&s| s.is_empty()),
            expected it "to contain elements matching predicate"
            but it "was <[ \"a\" ]>");
    }

    #[test]
    fn contains_only_elements_matching_passes_for_empty_slice() {
        assert_that!(&[] as &[&str]).contains_only_elements_matching(|&s| s.is_empty());
    }

    #[test]
    fn contains_only_elements_matching_passes_for_slice_with_single_matching_element() {
        assert_that!(&[""]).contains_only_elements_matching(|&s| s.is_empty());
    }

    #[test]
    fn contains_only_elements_matching_fails_for_slice_with_single_non_matching_element() {
        assert_fails!((&["a"]).contains_only_elements_matching(|&s| s.is_empty()),
            expected it "to contain only elements matching predicate"
            but it "was <[ [\"a\"] ]>");
    }

    #[test]
    fn contains_only_elements_matching_fails_for_slice_with_mixed_elements() {
        assert_fails!((&["", "a"]).contains_only_elements_matching(|&s| s.is_empty()),
            expected it "to contain only elements matching predicate"
            but it "was <[ \"\", [\"a\"] ]>");
    }

    #[test]
    fn does_not_contain_elements_matching_passes_for_empty_slice() {
        assert_that!(&[] as &[&str]).does_not_contain_elements_matching(|&s| s.is_empty());
    }

    #[test]
    fn does_not_contain_elements_matching_passes_for_slice_with_single_non_matching_element() {
        assert_that!(&["a"]).does_not_contain_elements_matching(|&s| s.is_empty());
    }

    #[test]
    fn does_not_contain_elements_matching_fails_for_slice_with_single_matching_element() {
        assert_fails!((&[""]).does_not_contain_elements_matching(|&s| s.is_empty()),
            expected it "not to contain elements matching predicate"
            but it "was <[ [\"\"] ]>");
    }

    #[test]
    fn does_not_contain_elements_matching_fails_for_slice_with_mixed_elements() {
        assert_fails!((&["", "a"]).does_not_contain_elements_matching(|&s| s.is_empty()),
            expected it "not to contain elements matching predicate"
            but it "was <[ [\"\"], \"a\" ]>");
    }

    #[test]
    fn to_single_element_passes() {
        let vec = vec![1];
        let assert = assert_that!(vec);
        let single_element_assert = assert.to_single_element();

        assert_that!(single_element_assert.data).is_equal_to(&1);
        assert_that!(single_element_assert.expression.as_str())
            .is_equal_to("single element of <vec>");
    }

    #[test]
    fn to_single_element_fails_for_empty_collection() {
        assert_fails!((BTreeSet::<String>::new()).to_single_element(),
            expected it "to contain exactly one element"
            but it "was empty");
    }

    #[test]
    fn to_single_element_fails_for_multiple_elements() {
        assert_fails!((vec![1, 2]).to_single_element(),
            expected it "to contain exactly one element"
            but it "was <[ 1, 2 ]>, which has length <2>");
    }

    #[test]
    fn is_single_element_matching_passes() {
        assert_that!(&["hello"]).is_single_element_matching(|s| s.len() == 5);
    }

    #[test]
    fn is_single_element_matching_fails_for_empty_collection() {
        assert_fails!((VecDeque::<String>::new()).is_single_element_matching(|s| s.len() == 5),
            expected it "to contain exactly one element, which matches the given predicate"
            but it "was empty");
    }

    #[test]
    fn is_single_element_matching_fails_for_multiple_elements() {
        assert_fails!((vec![1, 2]).is_single_element_matching(|i| i % 2 == 0),
            expected it "to contain exactly one element, which matches the given predicate"
            but it "was <[ 1, 2 ]>, which has length <2>");
    }

    #[test]
    fn is_single_element_matching_fails_for_single_element_not_matching_predicate() {
        assert_fails!((vec![3]).is_single_element_matching(|i| i % 2 == 0),
            expected it "to contain exactly one element, which matches the given predicate"
            but it "contained single element <3>, which does not match the predicate");
    }
}
