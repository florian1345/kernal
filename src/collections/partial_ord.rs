//! Contains specialized assertions for [Collection]s and [OrderedCollection]s whose items implement
//! [PartialOrd]. See [CollectionPartialOrdAssertions] and [OrderedCollectionPartialOrdAssertions]
//! for more details.

use std::borrow::Borrow;
use std::fmt::Debug;

use crate::collections::ordered::OrderedCollection;
use crate::collections::{Collection, CollectionDebug, HighlightedCollectionDebug};
use crate::{AssertThat, Failure};

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with an
/// argument that implements the [Collection] trait and whose [Collection::Item] type implements
/// [PartialOrd] in addition to [Debug].
///
/// Example:
///
/// ```
/// use kernal::prelude::*;
///
/// assert_that!(&[1, 5, 3])
///     .contains_items_less_than(4)
///     .contains_only_items_greater_than_or_equal_to(1);
/// ```
pub trait CollectionPartialOrdAssertions<C: Collection> {
    /// Asserts that the tested collection contains at least one element that is less than the given
    /// `bound` according to [PartialOrd]. In particular, this always fails for empty collections.
    fn contains_items_less_than<E: Borrow<C::Item>>(self, bound: E) -> Self;

    /// Asserts that the tested collection contains only elements that are less than the given
    /// `bound` according to [PartialOrd]. In particular, this always passes for empty collections.
    fn contains_only_items_less_than<E: Borrow<C::Item>>(self, bound: E) -> Self;

    /// Asserts that the tested collection contains at least one element that is less than or equal
    /// to the given `bound` according to [PartialOrd]. In particular, this always fails for empty
    /// collections.
    fn contains_items_less_than_or_equal_to<E: Borrow<C::Item>>(self, bound: E) -> Self;

    /// Asserts that the tested collection contains only elements that are less than or equal to the
    /// given `bound` according to [PartialOrd]. In particular, this always passes for empty
    /// collections.
    fn contains_only_items_less_than_or_equal_to<E: Borrow<C::Item>>(self, bound: E) -> Self;

    /// Asserts that the tested collection contains at least one element that is greater than the
    /// given `bound` according to [PartialOrd]. In particular, this always fails for empty
    /// collections.
    fn contains_items_greater_than<E: Borrow<C::Item>>(self, bound: E) -> Self;

    /// Asserts that the tested collection contains only elements that are greater than the given
    /// `bound` according to [PartialOrd]. In particular, this always passes for empty collections.
    fn contains_only_items_greater_than<E: Borrow<C::Item>>(self, bound: E) -> Self;

    /// Asserts that the tested collection contains at least one element that is greater than or
    /// equal to the given `bound` according to [PartialOrd]. In particular, this always fails for
    /// empty collections.
    fn contains_items_greater_than_or_equal_to<E: Borrow<C::Item>>(self, bound: E) -> Self;

    /// Asserts that the tested collection contains only elements that are greater than or equal to
    /// the given `bound` according to [PartialOrd]. In particular, this always passes for empty
    /// collections.
    fn contains_only_items_greater_than_or_equal_to<E: Borrow<C::Item>>(self, bound: E) -> Self;
}

fn assert_contains_items_matching_bound<C, E, F>(
    assert_that: AssertThat<C>,
    bound: E,
    mut operation: F,
    operation_name: &str,
) -> AssertThat<C>
where
    C: Collection,
    C::Item: Debug + PartialOrd,
    E: Borrow<C::Item>,
    F: FnMut(&C::Item, &C::Item) -> bool,
{
    let bound = bound.borrow();

    if !assert_that
        .data
        .iterator()
        .any(|item| operation(item, bound))
    {
        Failure::new(&assert_that)
            .expected_it(format!(
                "to contain elements {} <{:?}>",
                operation_name, bound
            ))
            .but_it(format!(
                "was <{:?}>",
                CollectionDebug {
                    collection: &assert_that.data
                }
            ))
            .fail();
    }

    assert_that
}

fn assert_contains_only_items_matching_bound<C, E, F>(
    assert_that: AssertThat<C>,
    bound: E,
    mut operation: F,
    operation_name: &str,
) -> AssertThat<C>
where
    C: Collection,
    C::Item: Debug + PartialOrd,
    E: Borrow<C::Item>,
    F: FnMut(&C::Item, &C::Item) -> bool,
{
    let bound = bound.borrow();
    let counter_example_index = assert_that
        .data
        .iterator()
        .enumerate()
        .find(|(_, item)| !operation(item, bound))
        .map(|(index, _)| index);

    if let Some(counter_example_index) = counter_example_index {
        let collection_debug = HighlightedCollectionDebug::with_single_highlighted_element(
            &assert_that.data,
            counter_example_index,
        );

        Failure::new(&assert_that)
            .expected_it(format!(
                "to contain only elements {} <{:?}>",
                operation_name, bound
            ))
            .but_it(format!("was <{:?}>", collection_debug))
            .fail();
    }

    assert_that
}

impl<C> CollectionPartialOrdAssertions<C> for AssertThat<C>
where
    C: Collection,
    C::Item: Debug + PartialOrd,
{
    fn contains_items_less_than<E: Borrow<C::Item>>(self, bound: E) -> Self {
        assert_contains_items_matching_bound(self, bound, |item, bound| item < bound, "less than")
    }

    fn contains_only_items_less_than<E: Borrow<C::Item>>(self, bound: E) -> Self {
        assert_contains_only_items_matching_bound(
            self,
            bound,
            |item, bound| item < bound,
            "less than",
        )
    }

    fn contains_items_less_than_or_equal_to<E: Borrow<C::Item>>(self, bound: E) -> Self {
        assert_contains_items_matching_bound(
            self,
            bound,
            |item, bound| item <= bound,
            "less than or equal to",
        )
    }

    fn contains_only_items_less_than_or_equal_to<E: Borrow<C::Item>>(self, bound: E) -> Self {
        assert_contains_only_items_matching_bound(
            self,
            bound,
            |item, bound| item <= bound,
            "less than or equal to",
        )
    }

    fn contains_items_greater_than<E: Borrow<C::Item>>(self, bound: E) -> Self {
        assert_contains_items_matching_bound(
            self,
            bound,
            |item, bound| item > bound,
            "greater than",
        )
    }

    fn contains_only_items_greater_than<E: Borrow<C::Item>>(self, bound: E) -> Self {
        assert_contains_only_items_matching_bound(
            self,
            bound,
            |item, bound| item > bound,
            "greater than",
        )
    }

    fn contains_items_greater_than_or_equal_to<E: Borrow<C::Item>>(self, bound: E) -> Self {
        assert_contains_items_matching_bound(
            self,
            bound,
            |item, bound| item >= bound,
            "greater than or equal to",
        )
    }

    fn contains_only_items_greater_than_or_equal_to<E: Borrow<C::Item>>(self, bound: E) -> Self {
        assert_contains_only_items_matching_bound(
            self,
            bound,
            |item, bound| item >= bound,
            "greater than or equal to",
        )
    }
}

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with an
/// argument that implements the [OrderedCollection] trait and whose [Collection::Item] type
/// implements [PartialOrd] in addition to [Debug].
///
/// Examples:
///
/// ```
/// use kernal::prelude::*;
///
/// assert_that!(&[2, 4, 4, 5]).is_sorted_in_ascending_order();
/// assert_that!(&[9, 6, 5, 2]).is_sorted_in_strictly_descending_order();
/// ```
pub trait OrderedCollectionPartialOrdAssertions {
    /// Asserts that the tested collection is sorted in non-strictly ascending order, i.e. each
    /// element's successor is greater than or equal to the element. This always passes for empty or
    /// singleton collections.
    fn is_sorted_in_ascending_order(self) -> Self;

    /// Asserts that the tested collection is sorted in strictly ascending order, i.e. each
    /// element's successor is greater than the element. This always passes for empty or singleton
    /// collections.
    fn is_sorted_in_strictly_ascending_order(self) -> Self;

    /// Asserts that the tested collection is sorted in non-strictly descending order, i.e. each
    /// element's successor is less than or equal to the element. This always passes for empty or
    /// singleton collections.
    fn is_sorted_in_descending_order(self) -> Self;

    /// Asserts that the tested collection is sorted in strictly descending order, i.e. each
    /// element's successor is less than the element. This always passes for empty or singleton
    /// collections.
    fn is_sorted_in_strictly_descending_order(self) -> Self;
}

fn find_sorting_counter_example_index<C, F>(
    collection: &C,
    are_correctly_ordered: F,
) -> Option<usize>
where
    C: OrderedCollection,
    F: Fn(&C::Item, &C::Item) -> bool,
{
    collection
        .iterator()
        .zip(collection.iterator().skip(1))
        .enumerate()
        .find(|(_, (element, successor))| !are_correctly_ordered(element, successor))
        .map(|(index, _)| index)
}

fn assert_is_sorted<C, F>(
    assert_that: AssertThat<C>,
    are_correctly_ordered: F,
    sorting_name: &str,
) -> AssertThat<C>
where
    C: OrderedCollection,
    C::Item: Debug,
    F: Fn(&C::Item, &C::Item) -> bool,
{
    let counter_example_index =
        find_sorting_counter_example_index(&assert_that.data, are_correctly_ordered);

    if let Some(counter_example_index) = counter_example_index {
        let collection_debug = HighlightedCollectionDebug {
            collection: &assert_that.data,
            highlighted_sections: vec![counter_example_index..(counter_example_index + 2)],
        };

        Failure::new(&assert_that)
            .expected_it(format!("to be sorted in {} order", sorting_name))
            .but_it(format!("was <{:?}>", collection_debug))
            .fail();
    }

    assert_that
}

impl<C> OrderedCollectionPartialOrdAssertions for AssertThat<C>
where
    C: OrderedCollection,
    C::Item: Debug + PartialOrd,
{
    fn is_sorted_in_ascending_order(self) -> Self {
        assert_is_sorted(self, |element, successor| element <= successor, "ascending")
    }

    fn is_sorted_in_strictly_ascending_order(self) -> Self {
        assert_is_sorted(
            self,
            |element, successor| element < successor,
            "strictly ascending",
        )
    }

    fn is_sorted_in_descending_order(self) -> Self {
        assert_is_sorted(
            self,
            |element, successor| element >= successor,
            "descending",
        )
    }

    fn is_sorted_in_strictly_descending_order(self) -> Self {
        assert_is_sorted(
            self,
            |element, successor| element > successor,
            "strictly descending",
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{assert_fails, assert_that};

    #[test]
    fn contains_items_less_than_passes_for_single_item_less_than_bound() {
        assert_that!(&[3]).contains_items_less_than(4);
    }

    #[test]
    fn contains_items_less_than_passes_for_multiple_items_less_than_bound() {
        assert_that!(&[2, 3]).contains_items_less_than(4);
    }

    #[test]
    fn contains_items_less_than_passes_for_mixed_collection() {
        assert_that!(&[5, 3]).contains_items_less_than(4);
    }

    #[test]
    fn contains_items_less_than_fails_for_empty_slice() {
        assert_fails!((&[] as &[u32]).contains_items_less_than(10),
            expected it "to contain elements less than <10>"
            but it "was <[ ]>");
    }

    #[test]
    fn contains_items_less_than_fails_for_single_item_equal_to_bound() {
        assert_fails!((&[5]).contains_items_less_than(5),
            expected it "to contain elements less than <5>"
            but it "was <[ 5 ]>");
    }

    #[test]
    fn contains_items_less_than_fails_for_multiple_items_greater_than_or_equal_to_bound() {
        assert_fails!((&[ 4, 6, 3 ]).contains_items_less_than(3),
            expected it "to contain elements less than <3>"
            but it "was <[ 4, 6, 3 ]>");
    }

    #[test]
    fn contains_only_items_less_than_passes_for_empty_slice() {
        assert_that!(&[] as &[u32]).contains_only_items_less_than(10);
    }

    #[test]
    fn contains_only_items_less_than_passes_for_single_item_less_than_bound() {
        assert_that!(&[3]).contains_only_items_less_than(4);
    }

    #[test]
    fn contains_only_items_less_than_passes_for_multiple_items_less_than_bound() {
        assert_that!(&[2, 3]).contains_only_items_less_than(4);
    }

    #[test]
    fn contains_only_items_less_than_fails_for_mixed_collection() {
        assert_fails!((&[5, 3]).contains_only_items_less_than(4),
            expected it "to contain only elements less than <4>"
            but it "was <[ [5], 3 ]>");
    }

    #[test]
    fn contains_only_items_less_than_fails_for_single_item_equal_to_bound() {
        assert_fails!((&[5]).contains_only_items_less_than(5),
            expected it "to contain only elements less than <5>"
            but it "was <[ [5] ]>");
    }

    #[test]
    fn contains_only_items_less_than_fails_for_later_counter_example() {
        assert_fails!((&[ 1, 2, 1, 4, 1 ]).contains_only_items_less_than(3),
            expected it "to contain only elements less than <3>"
            but it "was <[ 1, 2, 1, [4], 1 ]>");
    }

    #[test]
    fn contains_items_less_than_or_equal_to_passes_for_single_item_less_than_bound() {
        assert_that!(&[5]).contains_items_less_than_or_equal_to(10);
    }

    #[test]
    fn contains_items_less_than_or_equal_to_passes_for_single_item_equal_to_bound() {
        assert_that!(&[10]).contains_items_less_than_or_equal_to(10);
    }

    #[test]
    fn contains_items_less_than_or_equal_to_passes_for_mixed_slice() {
        assert_that!(&[12, 8]).contains_items_less_than_or_equal_to(10);
    }

    #[test]
    fn contains_items_less_than_or_equal_to_fails_for_empty_slice() {
        assert_fails!((&[] as &[usize]).contains_items_less_than_or_equal_to(1),
            expected it "to contain elements less than or equal to <1>"
            but it "was <[ ]>");
    }

    #[test]
    fn contains_items_less_than_or_equal_to_fails_for_single_item_greater_than_bound() {
        assert_fails!((&[11]).contains_items_less_than_or_equal_to(10),
            expected it "to contain elements less than or equal to <10>"
            but it "was <[ 11 ]>");
    }

    #[test]
    fn contains_items_less_than_or_equal_to_fails_for_multiple_items_greater_than_bound() {
        assert_fails!((&[12, 13]).contains_items_less_than_or_equal_to(10),
            expected it "to contain elements less than or equal to <10>"
            but it "was <[ 12, 13 ]>");
    }

    #[test]
    fn contains_only_items_less_than_or_equal_to_passes_for_empty_slice() {
        assert_that!(&[] as &[usize]).contains_only_items_less_than_or_equal_to(1);
    }

    #[test]
    fn contains_only_items_less_than_or_equal_to_passes_for_single_item_less_than_bound() {
        assert_that!(&[5]).contains_only_items_less_than_or_equal_to(10);
    }

    #[test]
    fn contains_only_items_less_than_or_equal_to_passes_for_single_item_equal_to_bound() {
        assert_that!(&[10]).contains_only_items_less_than_or_equal_to(10);
    }

    #[test]
    fn contains_only_items_less_than_or_equal_to_passes_for_multiple_matching_items() {
        assert_that!(&[8, 10]).contains_only_items_less_than_or_equal_to(10);
    }

    #[test]
    fn contains_only_items_less_than_or_equal_to_fails_for_single_item_greater_than_bound() {
        assert_fails!((&[11]).contains_only_items_less_than_or_equal_to(10),
            expected it "to contain only elements less than or equal to <10>"
            but it "was <[ [11] ]>");
    }

    #[test]
    fn contains_only_items_less_than_or_equal_to_fails_for_mixed_slice() {
        assert_fails!((&[8, 12]).contains_only_items_less_than_or_equal_to(10),
            expected it "to contain only elements less than or equal to <10>"
            but it "was <[ 8, [12] ]>");
    }

    #[test]
    fn contains_items_greater_than_passes_for_single_item_greater_than_bound() {
        assert_that!(&[5]).contains_items_greater_than(4);
    }

    #[test]
    fn contains_items_greater_than_passes_for_multiple_items_greater_than_bound() {
        assert_that!(&[5, 6]).contains_items_greater_than(4);
    }

    #[test]
    fn contains_items_greater_than_passes_for_mixed_collection() {
        assert_that!(&[3, 5]).contains_items_greater_than(4);
    }

    #[test]
    fn contains_items_greater_than_fails_for_empty_slice() {
        assert_fails!((&[] as &[u32]).contains_items_greater_than(10),
            expected it "to contain elements greater than <10>"
            but it "was <[ ]>");
    }

    #[test]
    fn contains_items_greater_than_fails_for_single_item_equal_to_bound() {
        assert_fails!((&[5]).contains_items_greater_than(5),
            expected it "to contain elements greater than <5>"
            but it "was <[ 5 ]>");
    }

    #[test]
    fn contains_items_greater_than_fails_for_multiple_items_less_than_or_equal_to_bound() {
        assert_fails!((&[ 2, 1, 3 ]).contains_items_greater_than(3),
            expected it "to contain elements greater than <3>"
            but it "was <[ 2, 1, 3 ]>");
    }

    #[test]
    fn contains_only_items_greater_than_passes_for_empty_slice() {
        assert_that!(&[] as &[u32]).contains_only_items_greater_than(10);
    }

    #[test]
    fn contains_only_items_greater_than_passes_for_single_item_greater_than_bound() {
        assert_that!(&[5]).contains_only_items_greater_than(4);
    }

    #[test]
    fn contains_only_items_greater_than_passes_for_multiple_items_greater_than_bound() {
        assert_that!(&[5, 6]).contains_only_items_greater_than(4);
    }

    #[test]
    fn contains_only_items_greater_than_fails_for_mixed_collection() {
        assert_fails!((&[3, 5]).contains_only_items_greater_than(4),
            expected it "to contain only elements greater than <4>"
            but it "was <[ [3], 5 ]>");
    }

    #[test]
    fn contains_only_items_greater_than_fails_for_single_item_equal_to_bound() {
        assert_fails!((&[5]).contains_only_items_greater_than(5),
            expected it "to contain only elements greater than <5>"
            but it "was <[ [5] ]>");
    }

    #[test]
    fn contains_only_items_greater_than_fails_for_later_counter_example() {
        assert_fails!((&[ 4, 5, 4, 2, 6 ]).contains_only_items_greater_than(3),
            expected it "to contain only elements greater than <3>"
            but it "was <[ 4, 5, 4, [2], 6 ]>");
    }

    #[test]
    fn contains_items_greater_than_or_equal_to_passes_for_single_item_greater_than_bound() {
        assert_that!(&[10]).contains_items_greater_than_or_equal_to(5);
    }

    #[test]
    fn contains_items_greater_than_or_equal_to_passes_for_single_item_equal_to_bound() {
        assert_that!(&[10]).contains_items_greater_than_or_equal_to(10);
    }

    #[test]
    fn contains_items_greater_than_or_equal_to_passes_for_mixed_slice() {
        assert_that!(&[8, 12]).contains_items_greater_than_or_equal_to(10);
    }

    #[test]
    fn contains_items_greater_than_or_equal_to_fails_for_empty_slice() {
        assert_fails!((&[] as &[usize]).contains_items_greater_than_or_equal_to(1),
            expected it "to contain elements greater than or equal to <1>"
            but it "was <[ ]>");
    }

    #[test]
    fn contains_items_greater_than_or_equal_to_fails_for_single_item_less_than_bound() {
        assert_fails!((&[9]).contains_items_greater_than_or_equal_to(10),
            expected it "to contain elements greater than or equal to <10>"
            but it "was <[ 9 ]>");
    }

    #[test]
    fn contains_items_greater_than_or_equal_to_fails_for_multiple_items_less_than_bound() {
        assert_fails!((&[8, 9]).contains_items_greater_than_or_equal_to(10),
            expected it "to contain elements greater than or equal to <10>"
            but it "was <[ 8, 9 ]>");
    }

    #[test]
    fn contains_only_items_greater_than_or_equal_to_passes_for_empty_slice() {
        assert_that!(&[] as &[usize]).contains_only_items_greater_than_or_equal_to(1);
    }

    #[test]
    fn contains_only_items_greater_than_or_equal_to_passes_for_single_item_greater_than_bound() {
        assert_that!(&[10]).contains_only_items_greater_than_or_equal_to(5);
    }

    #[test]
    fn contains_only_items_greater_than_or_equal_to_passes_for_single_item_equal_to_bound() {
        assert_that!(&[10]).contains_only_items_greater_than_or_equal_to(10);
    }

    #[test]
    fn contains_only_items_greater_than_or_equal_to_passes_for_multiple_matching_items() {
        assert_that!(&[12, 10]).contains_only_items_greater_than_or_equal_to(10);
    }

    #[test]
    fn contains_only_items_greater_than_or_equal_to_fails_for_single_item_greater_than_bound() {
        assert_fails!((&[9]).contains_only_items_greater_than_or_equal_to(10),
            expected it "to contain only elements greater than or equal to <10>"
            but it "was <[ [9] ]>");
    }

    #[test]
    fn contains_only_items_greater_than_or_equal_to_fails_for_mixed_slice() {
        assert_fails!((&[12, 8]).contains_only_items_greater_than_or_equal_to(10),
            expected it "to contain only elements greater than or equal to <10>"
            but it "was <[ 12, [8] ]>");
    }

    #[test]
    fn is_sorted_in_ascending_order_passes_for_empty_slice() {
        assert_that!(&[] as &[u32]).is_sorted_in_ascending_order();
    }

    #[test]
    fn is_sorted_in_ascending_order_passes_for_singleton() {
        assert_that!(&[1]).is_sorted_in_ascending_order();
    }

    #[test]
    fn is_sorted_in_ascending_order_passes_for_strictly_ascending_slice() {
        assert_that!(&[1, 3, 4]).is_sorted_in_ascending_order();
    }

    #[test]
    fn is_sorted_in_ascending_order_passes_for_non_strictly_ascending_slice() {
        assert_that!(&[1, 3, 3, 7]).is_sorted_in_ascending_order();
    }

    #[test]
    fn is_sorted_in_ascending_order_fails_for_descending_pair() {
        assert_fails!((&[2, 1]).is_sorted_in_ascending_order(),
            expected it "to be sorted in ascending order"
            but it "was <[ [2, 1] ]>");
    }

    #[test]
    fn is_sorted_in_ascending_order_fails_for_later_descending_slice() {
        assert_fails!((&[1, 3, 2]).is_sorted_in_ascending_order(),
            expected it "to be sorted in ascending order"
            but it "was <[ 1, [3, 2] ]>");
    }

    #[test]
    fn is_sorted_in_strictly_ascending_order_passes_for_empty_slice() {
        assert_that!(&[] as &[u32]).is_sorted_in_strictly_ascending_order();
    }

    #[test]
    fn is_sorted_in_strictly_ascending_order_passes_for_singleton() {
        assert_that!(&[1]).is_sorted_in_strictly_ascending_order();
    }

    #[test]
    fn is_sorted_in_strictly_ascending_order_passes_for_strictly_ascending_slice() {
        assert_that!(&[1, 3, 4]).is_sorted_in_strictly_ascending_order();
    }

    #[test]
    fn is_sorted_in_strictly_ascending_order_fails_for_non_strictly_ascending_slice() {
        assert_fails!((&[1, 3, 3, 7]).is_sorted_in_strictly_ascending_order(),
            expected it "to be sorted in strictly ascending order"
            but it "was <[ 1, [3, 3], 7 ]>");
    }

    #[test]
    fn is_sorted_in_strictly_ascending_order_fails_for_descending_pair() {
        assert_fails!((&[2, 1]).is_sorted_in_strictly_ascending_order(),
            expected it "to be sorted in strictly ascending order"
            but it "was <[ [2, 1] ]>");
    }

    #[test]
    fn is_sorted_in_strictly_ascending_order_fails_for_later_descending_slice() {
        assert_fails!((&[1, 3, 2]).is_sorted_in_strictly_ascending_order(),
            expected it "to be sorted in strictly ascending order"
            but it "was <[ 1, [3, 2] ]>");
    }

    #[test]
    fn is_sorted_in_descending_order_passes_for_empty_slice() {
        assert_that!(&[] as &[u32]).is_sorted_in_descending_order();
    }

    #[test]
    fn is_sorted_in_descending_order_passes_for_singleton() {
        assert_that!(&[1]).is_sorted_in_descending_order();
    }

    #[test]
    fn is_sorted_in_descending_order_passes_for_strictly_descending_slice() {
        assert_that!(&[4, 3, 1]).is_sorted_in_descending_order();
    }

    #[test]
    fn is_sorted_in_descending_order_passes_for_non_strictly_descending_slice() {
        assert_that!(&[7, 3, 3, 1]).is_sorted_in_descending_order();
    }

    #[test]
    fn is_sorted_in_descending_order_fails_for_ascending_pair() {
        assert_fails!((&[1, 2]).is_sorted_in_descending_order(),
            expected it "to be sorted in descending order"
            but it "was <[ [1, 2] ]>");
    }

    #[test]
    fn is_sorted_in_descending_order_fails_for_later_ascending_slice() {
        assert_fails!((&[3, 2, 4]).is_sorted_in_descending_order(),
            expected it "to be sorted in descending order"
            but it "was <[ 3, [2, 4] ]>");
    }

    #[test]
    fn is_sorted_in_strictly_descending_order_passes_for_empty_slice() {
        assert_that!(&[] as &[u32]).is_sorted_in_strictly_descending_order();
    }

    #[test]
    fn is_sorted_in_strictly_descending_order_passes_for_singleton() {
        assert_that!(&[1]).is_sorted_in_strictly_descending_order();
    }

    #[test]
    fn is_sorted_in_strictly_descending_order_passes_for_strictly_descending_slice() {
        assert_that!(&[4, 3, 1]).is_sorted_in_strictly_descending_order();
    }

    #[test]
    fn is_sorted_in_strictly_descending_order_fails_for_non_strictly_descending_slice() {
        assert_fails!((&[7, 3, 3, 1]).is_sorted_in_strictly_descending_order(),
            expected it "to be sorted in strictly descending order"
            but it "was <[ 7, [3, 3], 1 ]>");
    }

    #[test]
    fn is_sorted_in_strictly_descending_order_fails_for_ascending_pair() {
        assert_fails!((&[1, 2]).is_sorted_in_strictly_descending_order(),
            expected it "to be sorted in strictly descending order"
            but it "was <[ [1, 2] ]>");
    }

    #[test]
    fn is_sorted_in_strictly_descending_order_fails_for_later_ascending_slice() {
        assert_fails!((&[3, 2, 4]).is_sorted_in_strictly_descending_order(),
            expected it "to be sorted in strictly descending order"
            but it "was <[ 3, [2, 4] ]>");
    }
}
