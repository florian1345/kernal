//! Contains specialized assertions for [Collection]s whose items implement [AbsDiff]. See
//! [CollectionAbsDiffAssertions] for more details.

use std::borrow::Borrow;
use std::fmt::Debug;

use crate::abs_diff::AbsDiff;
use crate::{AssertThat, Failure};
use crate::collections::{Collection, CollectionDebug, HighlightedCollectionDebug};
use crate::util::borrow_all;

fn highlight_violating_index<'collection, 'reference, C, P>(collection: &'reference C, predicate: P)
    -> Option<HighlightedCollectionDebug<Vec<&'reference C::Item>>>
where
    C: Collection<'collection>,
    P: Fn(&C::Item) -> bool,
    'collection: 'reference
{
    let items: Vec<&C::Item> = collection.iterator().collect::<Vec<_>>();

    let violating_index = items.iter().enumerate()
        .find(|(_, &item)| !predicate(item))
        .map(|(index, _)| index);

    violating_index.map(|violating_index|
        HighlightedCollectionDebug::with_single_highlighted_element(items, violating_index))
}

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with an
/// argument that implements the [Collection] trait and whose [Collection::Item] type implements
/// [AbsDiff] with a [AbsDiff::ReturnType] that implements [PartialOrd]. It can be seen as an
/// approximate version of
/// [CollectionPartialEqAssertions](crate::collections::partial_eq::CollectionPartialEqAssertions).
///
/// Examples:
///
/// ```
/// use kernal::prelude::*;
///
/// assert_that!([1.0, 1.5, 2.0])
///     .contains_items_close_to(0.9, 0.2)
///     .does_not_contain_items_close_to(5.0, 0.2);
/// ```
pub trait CollectionAbsDiffAssertions<'collection, C>
where
    C: Collection<'collection>,
    C::Item: AbsDiff,
    <C::Item as AbsDiff>::ReturnType: Debug + PartialOrd
{

    /// Asserts that the tested collection contains at least one item that is within `offset` of
    /// `expected` according to [AbsDiff] and [PartialOrd]. More formally, for some item `e` it
    /// holds that `e.abs_diff(expected) <= offset`.
    fn contains_items_close_to<E, O>(self, expected: E, offset: O) -> Self
    where
        E: Borrow<C::Item>,
        O: Borrow<<C::Item as AbsDiff>::ReturnType>;

    /// Asserts that all items of the tested collection are within `offset` of `expected` according
    /// to [AbsDiff] and [PartialOrd]. More formally, for all items `e` it holds that
    /// `e.abs_diff(expected) <= offset`.
    fn contains_only_items_close_to<E, O>(self, expected: E, offset: O) -> Self
    where
        E: Borrow<C::Item>,
        O: Borrow<<C::Item as AbsDiff>::ReturnType>;

    /// Asserts that the tested collection does not contain items that are within `offset` of
    /// `expected` according to [AbsDiff] and [PartialOrd]. More formally, for all items `e` it
    /// holds that `e.abs_diff(expected) > offset`.
    fn does_not_contain_items_close_to<E, O>(self, expected: E, offset: O) -> Self
    where
        E: Borrow<C::Item>,
        O: Borrow<<C::Item as AbsDiff>::ReturnType>;

    /// Asserts there is a 1:1 matching of items in the tested collection and the given expected
    /// `items` such that each matched pair is within `offset` of each other according to [AbsDiff]
    /// and [PartialOrd]. This can be seen as a version of
    /// [CollectionPartialEqAssertions::contains_exactly_in_any_order](crate::collections::partial_eq::CollectionPartialEqAssertions::contains_exactly_in_any_order)
    /// where equality is only approximate, controlled by `offset`.
    fn contains_exactly_in_any_order_close_to<E, I, O>(self, items: I, offset: O) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>,
        O: Borrow<<C::Item as AbsDiff>::ReturnType> + Debug;
}

fn can_match_item_to_expected_rec<T, F>(items: &[T], expected: &[T], index_to_match: usize,
    visited: &mut [bool], matched_indices: &mut [Option<usize>], is_match: &F) -> bool
where
    F: Fn(&T, &T) -> bool
{
    let item = &items[index_to_match];

    for (option_idx, option) in expected.iter().enumerate() {
        if is_match(item, option) && !visited[option_idx] {
            visited[option_idx] = true;

            let can_match_with_expected = match matched_indices[option_idx] {
                None => true,
                Some(matched_idx) => can_match_item_to_expected_rec(
                    items, expected, matched_idx, visited, matched_indices, is_match)
            };

            if can_match_with_expected {
                matched_indices[option_idx] = Some(index_to_match);
                return true;
            }
        }
    }

    false
}

fn can_match_item_to_expected<T, F>(items: &[T], expected: &[T], index_to_match: usize,
    matched_indices: &mut [Option<usize>], is_match: &F) -> bool
where
    F: Fn(&T, &T) -> bool
{
    let mut visited = vec![false; expected.len()];

    can_match_item_to_expected_rec(
        items, expected, index_to_match, &mut visited, matched_indices, is_match)
}

fn count_items_matchable_to_expected<T, F>(items: &[T], expected: &[T], is_match: F) -> usize
where
    F: Fn(&T, &T) -> bool
{
    let mut matched_indices = vec![None; expected.len()];
    let mut result = 0;

    for index_to_match in 0..items.len() {
        if can_match_item_to_expected(
                items, expected, index_to_match, &mut matched_indices, &is_match) {
            result += 1;
        }
    }

    result
}

impl<'collection, C> CollectionAbsDiffAssertions<'collection, C> for AssertThat<C>
where
    C: Collection<'collection>,
    C::Item: AbsDiff + Debug,
    <C::Item as AbsDiff>::ReturnType: Debug + PartialOrd
{
    fn contains_items_close_to<E, O>(self, expected: E, offset: O) -> Self
    where
        E: Borrow<C::Item>,
        O: Borrow<<C::Item as AbsDiff>::ReturnType>
    {
        let expected = expected.borrow();
        let offset = offset.borrow();

        if !self.data.iterator().any(|item| &item.abs_diff(expected) <= offset) {
            Failure::new(&self)
                .expected_it(
                    format!("to contain an element within <{:?}> of <{:?}>", offset, expected))
                .but_it(format!("was <{:?}>", CollectionDebug { collection: &self.data }))
                .fail();
        }

        self
    }

    fn contains_only_items_close_to<E, O>(self, expected: E, offset: O) -> Self
    where
        E: Borrow<C::Item>,
        O: Borrow<<C::Item as AbsDiff>::ReturnType>
    {
        let expected = expected.borrow();
        let offset = offset.borrow();
        let highlighted_collection_debug =
            highlight_violating_index(&self.data, |item| &item.abs_diff(expected) <= offset);

        if let Some(highlighted_collection_debug) = highlighted_collection_debug {
            Failure::new(&self)
                .expected_it(
                    format!("to only contain elements within <{:?}> of <{:?}>", offset, expected))
                .but_it(format!("was <{:?}>", highlighted_collection_debug))
                .fail()
        }

        self
    }

    fn does_not_contain_items_close_to<E, O>(self, expected: E, offset: O) -> Self
    where
        E: Borrow<C::Item>,
        O: Borrow<<C::Item as AbsDiff>::ReturnType>
    {
        let expected = expected.borrow();
        let offset = offset.borrow();
        let highlighted_collection_debug =
            highlight_violating_index(&self.data, |item| &item.abs_diff(expected) > offset);

        if let Some(highlighted_collection_debug) = highlighted_collection_debug {
            Failure::new(&self)
                .expected_it(
                    format!("to contain no elements within <{:?}> of <{:?}>", offset, expected))
                .but_it(format!("was <{:?}>", highlighted_collection_debug))
                .fail()
        }

        self
    }

    fn contains_exactly_in_any_order_close_to<E, I, O>(self, items: I, offset: O) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>,
        O: Borrow<<C::Item as AbsDiff>::ReturnType>
    {
        let actual_items: Vec<&C::Item> = self.data.iterator().collect();
        let expected_items_unborrowed = items.into_iter().collect::<Vec<_>>();
        let expected_items: Vec<&C::Item> = borrow_all(&expected_items_unborrowed);
        let offset = offset.borrow();
        let is_match = |actual_item: &&C::Item, expected_item: &&C::Item|
            &actual_item.abs_diff(expected_item) <= offset;
        let len = actual_items.len();

        if len != expected_items.len() ||
                count_items_matchable_to_expected(&actual_items, &expected_items, is_match) != len {
            Failure::new(&self)
                .expected_it(format!(
                    "to contain exactly elements <{:?}> in any order within a margin of <{:?}>",
                    CollectionDebug { collection: &expected_items }, offset))
                .but_it(format!("was <{:?}>", CollectionDebug { collection: &self.data }))
                .fail();
        }

        self
    }
}

#[cfg(test)]
mod tests {

    use crate::{assert_that, assert_fails};
    use super::*;

    #[test]
    fn contains_elements_close_to_passes_for_singleton_of_close_element() {
        assert_that!([2.5]).contains_items_close_to(2.4, 0.2);
    }

    #[test]
    fn contains_elements_close_to_passes_for_later_close_element() {
        assert_that!([-1.0, -1.5, 0.0]).contains_items_close_to(-1.6, 0.15);
    }

    #[test]
    fn contains_elements_close_to_passes_element_just_inside_of_range() {
        assert_that!([1]).contains_items_close_to(0, 1u32);
    }

    #[test]
    fn contains_elements_close_to_fails_for_empty_list() {
        assert_fails!(([] as [f32; 0]).contains_items_close_to(1.0, 1_000_000.0),
            expected it "to contain an element within <1000000.0> of <1.0>"
            but it "was <[ ]>");
    }

    #[test]
    fn contains_elements_close_to_fails_for_values_just_outside_of_range() {
        assert_fails!(([5, 9, 13]).contains_items_close_to(11, 1u32),
            expected it "to contain an element within <1> of <11>"
            but it "was <[ 5, 9, 13 ]>");
    }

    #[test]
    fn contains_only_elements_close_to_passes_for_empty_list() {
        assert_that!([] as [f32; 0]).contains_only_items_close_to(5.0, 0.01);
    }

    #[test]
    fn contains_only_elements_close_to_passes_for_singleton_equal_to_expected() {
        assert_that!([5u32]).contains_only_items_close_to(5u32, 1u32);
    }

    #[test]
    fn contains_only_elements_close_to_passes_for_values_just_inside_of_range() {
        assert_that!([2u32, 5u32, 8u32]).contains_only_items_close_to(5u32, 3u32);
    }

    #[test]
    fn contains_only_elements_close_to_fails_for_singleton_outside_of_range() {
        assert_fails!(([0.0]).contains_only_items_close_to(1.0, 0.5),
            expected it "to only contain elements within <0.5> of <1.0>"
            but it "was <[ [0.0] ]>");
    }

    #[test]
    fn contains_only_elements_close_to_fails_for_later_element_just_outside_of_range() {
        assert_fails!(([2u32, 3u32, 4u32]).contains_only_items_close_to(1, 2),
            expected it "to only contain elements within <2> of <1>"
            but it "was <[ 2, 3, [4] ]>");
    }

    #[test]
    fn contains_exactly_in_any_order_close_to_passes_for_empty_items_empty_expected() {
        assert_that!([] as [f32; 0])
            .contains_exactly_in_any_order_close_to([] as [f32; 0], 0.01f32);
    }

    #[test]
    fn contains_exactly_in_any_order_close_to_passes_for_singleton_item_within_range() {
        assert_that!([2.5]).contains_exactly_in_any_order_close_to([2.25], 0.25);
    }

    #[test]
    fn contains_exactly_in_any_order_close_to_passes_for_two_items_in_disjunctive_ranges() {
        assert_that!([-1.25, 2.25]).contains_exactly_in_any_order_close_to([-1.0, 2.0], 0.25);
    }

    #[test]
    fn contains_exactly_in_any_order_close_to_passes_for_two_items_in_intersection_of_ranges() {
        assert_that!([0.45, 0.55]).contains_exactly_in_any_order_close_to([0.0, 1.0], 0.75);
    }

    #[test]
    fn contains_exactly_in_any_order_close_to_passes_for_items_with_non_trivial_matching() {
        assert_that!([0.0, 1.0, 2.0])
            .contains_exactly_in_any_order_close_to([0.5, -0.5, 1.5], 0.75);
    }

    #[test]
    fn contains_exactly_in_any_order_close_to_passes_for_items_with_large_non_trivial_matching() {
        assert_that!([0.0, 1.0, 2.0, 1.0, 2.5, 0.5])
            .contains_exactly_in_any_order_close_to([0.0, 0.5, 0.5, 2.5, 1.5, -0.5], 0.75);
    }

    #[test]
    fn contains_exactly_in_any_order_close_to_fails_for_singleton_item_below_range() {
        assert_fails!(([2.5]).contains_exactly_in_any_order_close_to([3.5], 0.75),
            expected it
                "to contain exactly elements <[ 3.5 ]> in any order within a margin of <0.75>"
            but it "was <[ 2.5 ]>");
    }

    #[test]
    fn contains_exactly_in_any_order_close_to_fails_for_singleton_item_above_range() {
        assert_fails!(([4.5]).contains_exactly_in_any_order_close_to([3.5], 0.75),
            expected it
                "to contain exactly elements <[ 3.5 ]> in any order within a margin of <0.75>"
            but it "was <[ 4.5 ]>");
    }

    #[test]
    fn contains_exactly_in_any_order_close_to_fails_for_missing_item() {
        assert_fails!(([1.0, 2.0, 3.0])
            .contains_exactly_in_any_order_close_to([0.9, 2.1, 1.6, 3.0], 0.25),
            expected it "to contain exactly elements <[ 0.9, 2.1, 1.6, 3.0 ]> in any order within \
                a margin of <0.25>"
            but it "was <[ 1.0, 2.0, 3.0 ]>");
    }

    #[test]
    fn contains_exactly_in_any_order_close_to_fails_for_superfluous_item() {
        assert_fails!(([1.0, 2.0, 3.0])
            .contains_exactly_in_any_order_close_to([0.9, 3.0], 0.25),
            expected it "to contain exactly elements <[ 0.9, 3.0 ]> in any order within a margin \
                of <0.25>"
            but it "was <[ 1.0, 2.0, 3.0 ]>");
    }

    #[test]
    fn contains_exactly_in_any_order_close_to_fails_when_overloading_single_expected_item() {
        assert_fails!(([2.1, 2.2, 3.0])
            .contains_exactly_in_any_order_close_to([3.1, 2.0, 2.9], 0.3),
            expected it "to contain exactly elements <[ 3.1, 2.0, 2.9 ]> in any order within a \
                margin of <0.3>"
            but it "was <[ 2.1, 2.2, 3.0 ]>");
    }

    #[test]
    fn contains_exactly_in_any_order_close_to_fails_when_overloading_multiple_expected_items() {
        assert_fails!(([2.9, 3.1, 3.0, 2.0])
            .contains_exactly_in_any_order_close_to([3.1, 2.0, 2.9, 2.1], 0.3),
            expected it "to contain exactly elements <[ 3.1, 2.0, 2.9, 2.1 ]> in any order within \
                a margin of <0.3>"
            but it "was <[ 2.9, 3.1, 3.0, 2.0 ]>");
    }
}
