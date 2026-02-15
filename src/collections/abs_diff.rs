//! Contains specialized assertions for [Collection]s and [OrderedCollection]s whose items implement
//! [AbsDiff] with [AbsDiff::ReturnType] that implements [PartialOrd]. See
//! [CollectionAbsDiffAssertions] and [OrderedCollectionAbsDiffAssertions] for more details.

use std::borrow::Borrow;
use std::fmt::Debug;
use std::ops::Range;

use crate::abs_diff::AbsDiff;
use crate::collections::ordered::OrderedCollection;
use crate::collections::{
    Collection,
    CollectionDebug,
    HighlightedCollectionDebug,
    assert_contains_exactly_in_given_order_by,
    find_contiguous_subsequence_by,
    find_prefix_by,
    find_subsequence_by,
    find_suffix_by,
};
use crate::util::borrow_all;
use crate::{AssertThat, Failure};

fn highlight_violating_index<C, P>(
    collection: &C,
    predicate: P,
) -> Option<HighlightedCollectionDebug<Vec<&C::Item>>>
where
    C: Collection,
    P: Fn(&C::Item) -> bool,
{
    let items: Vec<&C::Item> = collection.iterator().collect::<Vec<_>>();

    let violating_index = items
        .iter()
        .enumerate()
        .find(|(_, item)| !predicate(item))
        .map(|(index, _)| index);

    violating_index.map(|violating_index| {
        HighlightedCollectionDebug::with_single_highlighted_element(items, violating_index)
    })
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
pub trait CollectionAbsDiffAssertions<C>
where
    C: Collection,
    C::Item: AbsDiff,
    <C::Item as AbsDiff>::ReturnType: Debug + PartialOrd,
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

fn can_match_item_to_expected_rec<T, F>(
    items: &[T],
    expected: &[T],
    index_to_match: usize,
    visited: &mut [bool],
    matched_indices: &mut [Option<usize>],
    is_match: &F,
) -> bool
where
    F: Fn(&T, &T) -> bool,
{
    let item = &items[index_to_match];

    for (option_idx, option) in expected.iter().enumerate() {
        if is_match(item, option) && !visited[option_idx] {
            visited[option_idx] = true;

            let can_match_with_expected = match matched_indices[option_idx] {
                None => true,
                Some(matched_idx) => can_match_item_to_expected_rec(
                    items,
                    expected,
                    matched_idx,
                    visited,
                    matched_indices,
                    is_match,
                ),
            };

            if can_match_with_expected {
                matched_indices[option_idx] = Some(index_to_match);
                return true;
            }
        }
    }

    false
}

fn can_match_item_to_expected<T, F>(
    items: &[T],
    expected: &[T],
    index_to_match: usize,
    matched_indices: &mut [Option<usize>],
    is_match: &F,
) -> bool
where
    F: Fn(&T, &T) -> bool,
{
    let mut visited = vec![false; expected.len()];

    can_match_item_to_expected_rec(
        items,
        expected,
        index_to_match,
        &mut visited,
        matched_indices,
        is_match,
    )
}

fn count_items_matchable_to_expected<T, F>(items: &[T], expected: &[T], is_match: F) -> usize
where
    F: Fn(&T, &T) -> bool,
{
    let mut matched_indices = vec![None; expected.len()];
    let mut result = 0;

    for index_to_match in 0..items.len() {
        if can_match_item_to_expected(
            items,
            expected,
            index_to_match,
            &mut matched_indices,
            &is_match,
        ) {
            result += 1;
        }
    }

    result
}

impl<C> CollectionAbsDiffAssertions<C> for AssertThat<C>
where
    C: Collection,
    C::Item: AbsDiff + Debug,
    <C::Item as AbsDiff>::ReturnType: Debug + PartialOrd,
{
    fn contains_items_close_to<E, O>(self, expected: E, offset: O) -> Self
    where
        E: Borrow<C::Item>,
        O: Borrow<<C::Item as AbsDiff>::ReturnType>,
    {
        let expected = expected.borrow();
        let offset = offset.borrow();

        if !self
            .data
            .iterator()
            .any(|item| &item.abs_diff(expected) <= offset)
        {
            Failure::new(&self)
                .expected_it(format!(
                    "to contain an element within <{:?}> of <{:?}>",
                    offset, expected
                ))
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

    fn contains_only_items_close_to<E, O>(self, expected: E, offset: O) -> Self
    where
        E: Borrow<C::Item>,
        O: Borrow<<C::Item as AbsDiff>::ReturnType>,
    {
        let expected = expected.borrow();
        let offset = offset.borrow();
        let highlighted_collection_debug =
            highlight_violating_index(&self.data, |item| &item.abs_diff(expected) <= offset);

        if let Some(highlighted_collection_debug) = highlighted_collection_debug {
            Failure::new(&self)
                .expected_it(format!(
                    "to only contain elements within <{:?}> of <{:?}>",
                    offset, expected
                ))
                .but_it(format!("was <{:?}>", highlighted_collection_debug))
                .fail()
        }

        self
    }

    fn does_not_contain_items_close_to<E, O>(self, expected: E, offset: O) -> Self
    where
        E: Borrow<C::Item>,
        O: Borrow<<C::Item as AbsDiff>::ReturnType>,
    {
        let expected = expected.borrow();
        let offset = offset.borrow();
        let highlighted_collection_debug =
            highlight_violating_index(&self.data, |item| &item.abs_diff(expected) > offset);

        if let Some(highlighted_collection_debug) = highlighted_collection_debug {
            Failure::new(&self)
                .expected_it(format!(
                    "to contain no elements within <{:?}> of <{:?}>",
                    offset, expected
                ))
                .but_it(format!("was <{:?}>", highlighted_collection_debug))
                .fail()
        }

        self
    }

    fn contains_exactly_in_any_order_close_to<E, I, O>(self, items: I, offset: O) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>,
        O: Borrow<<C::Item as AbsDiff>::ReturnType>,
    {
        let actual_items: Vec<&C::Item> = self.data.iterator().collect();
        let expected_items_unborrowed = items.into_iter().collect::<Vec<_>>();
        let expected_items: Vec<&C::Item> = borrow_all(&expected_items_unborrowed);
        let offset = offset.borrow();
        let is_match = |actual_item: &&C::Item, expected_item: &&C::Item| {
            &actual_item.abs_diff(expected_item) <= offset
        };
        let len = actual_items.len();

        if len != expected_items.len()
            || count_items_matchable_to_expected(&actual_items, &expected_items, is_match) != len
        {
            Failure::new(&self)
                .expected_it(format!(
                    "to contain exactly elements <{:?}> in any order within a margin of <{:?}>",
                    CollectionDebug {
                        collection: &expected_items
                    },
                    offset
                ))
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
}

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with an
/// argument that implements the [OrderedCollection] trait and whose [Collection::Item] type
/// implements [AbsDiff] with a [AbsDiff::ReturnType] that implements [PartialOrd]. It can be seen
/// as an approximate version of
/// [OrderedCollectionPartialEqAssertions](crate::collections::partial_eq::OrderedCollectionPartialEqAssertions).
///
/// Examples:
///
/// ```
/// use kernal::prelude::*;
///
/// assert_that!([1.0, 1.5, 2.0, 2.5, 3.0])
///     .contains_contiguous_subsequence_close_to([1.6, 1.9, 2.6], 0.2)
///     .does_not_end_with_close_to([2.0, 2.5], 0.1);
/// ```
pub trait OrderedCollectionAbsDiffAssertions<C>
where
    C: OrderedCollection,
    C::Item: AbsDiff,
{
    /// Asserts that there is a contiguous subsequence in the tested collection in which each item
    /// is within `offset` of the item at the same position in the given `subsequence` according to
    /// [AbsDiff] and [PartialOrd]. More formally, given `subsequence` has a length of `n`, for some
    /// contiguous subsequence `e_0, ..., e_{n-1}` of the tested collection it holds that
    /// `e_0.abs_diff(subsequence[0]) <= offset && ... && e_{n-1}.abs_diff(subsequence[n-1]) <=
    /// offset`.
    fn contains_contiguous_subsequence_close_to<E, I, O>(self, subsequence: I, offset: O) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>,
        O: Borrow<<C::Item as AbsDiff>::ReturnType>;

    /// Asserts that there is **no** contiguous subsequence in the tested collection in which each
    /// item is within `offset` of the item at the same position in the given `subsequence`
    /// according to [AbsDiff] and [PartialOrd]. More formally, given `subsequence` has a length of
    /// `n`, there is **no** contiguous subsequence `e_0, ..., e_{n-1}` of the tested collection
    /// such that `e_0.abs_diff(subsequence[0]) <= offset && ... &&
    /// e_{n-1}.abs_diff(subsequence[n-1]) <= offset`.
    fn does_not_contain_contiguous_subsequence_close_to<E, I, O>(
        self,
        subsequence: I,
        offset: O,
    ) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>,
        O: Borrow<<C::Item as AbsDiff>::ReturnType>;

    /// Asserts that there is a (not necessarily contiguous) subsequence in the tested collection in
    /// which each item is within `offset` of the item at the same position in the given
    /// `subsequence` according to [AbsDiff] and [PartialOrd]. More formally, given `subsequence`
    /// has a length of `n`, for some subsequence `e_0, ..., e_{n-1}` of the tested collection it
    /// holds that `e_0.abs_diff(subsequence[0]) <= offset && ... &&
    /// e_{n-1}.abs_diff(subsequence[n-1]) <= offset`.
    fn contains_subsequence_close_to<E, I, O>(self, subsequence: I, offset: O) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>,
        O: Borrow<<C::Item as AbsDiff>::ReturnType>;

    /// Asserts that there is **no** subsequence (not even a non-contiguous one) in the tested
    /// collection in which each item is within `offset` of the item at the same position in the
    /// given `subsequence` according to [AbsDiff] and [PartialOrd]. More formally, given
    /// `subsequence` has a length of `n`, there is **no** subsequence `e_0, ..., e_{n-1}` of the
    /// tested collection such that `e_0.abs_diff(subsequence[0]) <= offset && ... &&
    /// e_{n-1}.abs_diff(subsequence[n-1]) <= offset`.
    fn does_not_contain_subsequence_close_to<E, I, O>(self, subsequence: I, offset: O) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>,
        O: Borrow<<C::Item as AbsDiff>::ReturnType>;

    /// Asserts that the tested collection has a prefix in which each item is within `offset` of the
    /// item at the same position in the given `prefix` according to [AbsDiff] and [PartialOrd].
    /// More formally, given `prefix` has a length of `n`, the tested collection is of the form
    /// `e_0, ..., e_{n-1}, ...` with `e_0.abs_diff(prefix[0]) <= offset && ... &&
    /// e_{n-1}.abs_diff(prefix[n-1]) <= offset`.
    fn starts_with_close_to<E, I, O>(self, prefix: I, offset: O) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>,
        O: Borrow<<C::Item as AbsDiff>::ReturnType>;

    /// Asserts that the tested collection **does not have** a prefix in which each item is within
    /// `offset` of the item at the same position in the given `prefix` according to [AbsDiff] and
    /// [PartialOrd]. More formally, given `prefix` has a length of `n`, the tested collection is
    /// shorter than `n` or of the form `e_0, ..., e_{n-1}, ...` with `e_0.abs_diff(prefix[0]) >
    /// offset || ... || e_{n-1}.abs_diff(prefix[n-1]) > offset`.
    fn does_not_start_with_close_to<E, I, O>(self, prefix: I, offset: O) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>,
        O: Borrow<<C::Item as AbsDiff>::ReturnType>;

    /// Asserts that the tested collection has a suffix in which each item is within `offset` of the
    /// item at the same position in the given `suffix` according to [AbsDiff] and [PartialOrd].
    /// More formally, given `suffix` has a length of `n`, the tested collection is of the form
    /// `..., e_0, ..., e_{n-1}` with `e_0.abs_diff(suffix[0]) <= offset && ... &&
    /// e_{n-1}.abs_diff(suffix[n-1]) <= offset`.
    fn ends_with_close_to<E, I, O>(self, suffix: I, offset: O) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>,
        O: Borrow<<C::Item as AbsDiff>::ReturnType>;

    /// Asserts that the tested collection **does not have** a suffix in which each item is within
    /// `offset` of the item at the same position in the given `suffix` according to [AbsDiff] and
    /// [PartialOrd]. More formally, given `suffix` has a length of `n`, the tested collection is
    /// shorter than `n` or of the form `..., e_0, ..., e_{n-1}` with `e_0.abs_diff(suffix[0]) >
    /// offset || ... || e_{n-1}.abs_diff(suffix[n-1]) > offset`.
    fn does_not_end_with_close_to<E, I, O>(self, suffix: I, offset: O) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>,
        O: Borrow<<C::Item as AbsDiff>::ReturnType>;

    /// Asserts that each item in the tested collection is within `offset` of the item at the same
    /// position in the given expected `items` according to [AbsDiff] and [PartialOrd]. More
    /// formally, given `items` has a length of `n`, the tested collection is of the form `e_0, ...,
    /// e_{n-1}` and `e_0.abs_diff(items[0]) <= offset && ... && e_{n-1}.abs_diff(items[n-1]) <=
    /// offset`.
    fn contains_exactly_in_given_order_close_to<E, I, O>(self, items: I, offset: O) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>,
        O: Borrow<<C::Item as AbsDiff>::ReturnType>;
}

fn find_contiguous_subsequence_close_to<C>(
    collection: &C,
    subsequence: &[&C::Item],
    offset: &<C::Item as AbsDiff>::ReturnType,
) -> Option<Vec<Range<usize>>>
where
    C: OrderedCollection,
    C::Item: AbsDiff,
    <C::Item as AbsDiff>::ReturnType: PartialOrd,
{
    find_contiguous_subsequence_by(collection, subsequence, |item_1, item_2| {
        &item_1.abs_diff(item_2) <= offset
    })
}

fn find_subsequence_close_to<C>(
    collection: &C,
    subsequence: &[&C::Item],
    offset: &<C::Item as AbsDiff>::ReturnType,
) -> Option<Vec<Range<usize>>>
where
    C: OrderedCollection,
    C::Item: AbsDiff,
    <C::Item as AbsDiff>::ReturnType: PartialOrd,
{
    find_subsequence_by(collection, subsequence, |item_1, item_2| {
        &item_1.abs_diff(item_2) <= offset
    })
}

fn find_prefix_close_to<C>(
    collection: &C,
    prefix: &[&C::Item],
    offset: &<C::Item as AbsDiff>::ReturnType,
) -> Option<Vec<Range<usize>>>
where
    C: OrderedCollection,
    C::Item: AbsDiff,
    <C::Item as AbsDiff>::ReturnType: PartialOrd,
{
    find_prefix_by(collection, prefix, |item_1, item_2| {
        &item_1.abs_diff(item_2) <= offset
    })
}

fn find_suffix_close_to<C>(
    collection: &C,
    suffix: &[&C::Item],
    offset: &<C::Item as AbsDiff>::ReturnType,
) -> Option<Vec<Range<usize>>>
where
    C: OrderedCollection,
    C::Item: AbsDiff,
    <C::Item as AbsDiff>::ReturnType: PartialOrd,
{
    find_suffix_by(collection, suffix, |item_1, item_2| {
        &item_1.abs_diff(item_2) <= offset
    })
}

fn assert_contains_subsequence_kind<C, E, I, O, F>(
    assert_that: AssertThat<C>,
    subsequence_of_kind: I,
    offset: O,
    find_subsequence_of_kind: F,
    expected_it_prefix: &str,
) -> AssertThat<C>
where
    C: OrderedCollection,
    C::Item: AbsDiff + Debug,
    <C::Item as AbsDiff>::ReturnType: Debug,
    E: Borrow<C::Item>,
    I: IntoIterator<Item = E>,
    O: Borrow<<C::Item as AbsDiff>::ReturnType>,
    F: FnOnce(&C, &[&C::Item], &<C::Item as AbsDiff>::ReturnType) -> Option<Vec<Range<usize>>>,
{
    let subsequence_of_kind_vec_unborrowed = subsequence_of_kind.into_iter().collect::<Vec<_>>();
    let subsequence_of_kind_vec: Vec<&C::Item> = borrow_all(&subsequence_of_kind_vec_unborrowed);
    let offset = offset.borrow();

    if find_subsequence_of_kind(&assert_that.data, &subsequence_of_kind_vec, offset).is_none() {
        let subsequence_of_kind_debug = CollectionDebug {
            collection: &subsequence_of_kind_vec,
        };
        let collection_debug = CollectionDebug {
            collection: &assert_that.data,
        };

        Failure::new(&assert_that)
            .expected_it(format!(
                "{} <{:?}> within a margin of <{:?}>",
                expected_it_prefix, subsequence_of_kind_debug, offset
            ))
            .but_it(format!("was <{:?}>", collection_debug))
            .fail();
    }

    assert_that
}

fn assert_does_not_contain_subsequence_kind<C, E, I, O, F>(
    assert_that: AssertThat<C>,
    subsequence_of_kind: I,
    offset: O,
    find_subsequence_of_kind: F,
    expected_it_prefix: &str,
) -> AssertThat<C>
where
    C: OrderedCollection,
    C::Item: AbsDiff + Debug,
    <C::Item as AbsDiff>::ReturnType: Debug,
    E: Borrow<C::Item>,
    I: IntoIterator<Item = E>,
    O: Borrow<<C::Item as AbsDiff>::ReturnType>,
    F: FnOnce(&C, &[&C::Item], &<C::Item as AbsDiff>::ReturnType) -> Option<Vec<Range<usize>>>,
{
    let subsequence_of_kind_vec_unborrowed = subsequence_of_kind.into_iter().collect::<Vec<_>>();
    let subsequence_of_kind_vec: Vec<&C::Item> = borrow_all(&subsequence_of_kind_vec_unborrowed);
    let offset = offset.borrow();

    if let Some(first_occurrence_ranges) =
        find_subsequence_of_kind(&assert_that.data, &subsequence_of_kind_vec, offset)
    {
        let subsequence_of_kind_debug = CollectionDebug {
            collection: &subsequence_of_kind_vec,
        };
        let collection_debug = HighlightedCollectionDebug {
            collection: &assert_that.data,
            highlighted_sections: first_occurrence_ranges,
        };

        Failure::new(&assert_that)
            .expected_it(format!(
                "{} <{:?}> within a margin of <{:?}>",
                expected_it_prefix, subsequence_of_kind_debug, offset
            ))
            .but_it(format!("was <{:?}>", collection_debug))
            .fail();
    }

    assert_that
}

impl<C> OrderedCollectionAbsDiffAssertions<C> for AssertThat<C>
where
    C: OrderedCollection,
    C::Item: AbsDiff + Debug,
    <C::Item as AbsDiff>::ReturnType: Debug + PartialOrd,
{
    fn contains_contiguous_subsequence_close_to<E, I, O>(self, subsequence: I, offset: O) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>,
        O: Borrow<<C::Item as AbsDiff>::ReturnType>,
    {
        assert_contains_subsequence_kind(
            self,
            subsequence,
            offset,
            find_contiguous_subsequence_close_to,
            "to contain the contiguous subsequence",
        )
    }

    fn does_not_contain_contiguous_subsequence_close_to<E, I, O>(
        self,
        subsequence: I,
        offset: O,
    ) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>,
        O: Borrow<<C::Item as AbsDiff>::ReturnType>,
    {
        assert_does_not_contain_subsequence_kind(
            self,
            subsequence,
            offset,
            find_contiguous_subsequence_close_to,
            "not to contain the contiguous subsequence",
        )
    }

    fn contains_subsequence_close_to<E, I, O>(self, subsequence: I, offset: O) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>,
        O: Borrow<<C::Item as AbsDiff>::ReturnType>,
    {
        assert_contains_subsequence_kind(
            self,
            subsequence,
            offset,
            find_subsequence_close_to,
            "to contain the subsequence",
        )
    }

    fn does_not_contain_subsequence_close_to<E, I, O>(self, subsequence: I, offset: O) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>,
        O: Borrow<<C::Item as AbsDiff>::ReturnType>,
    {
        assert_does_not_contain_subsequence_kind(
            self,
            subsequence,
            offset,
            find_subsequence_close_to,
            "not to contain the subsequence",
        )
    }

    fn starts_with_close_to<E, I, O>(self, prefix: I, offset: O) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>,
        O: Borrow<<C::Item as AbsDiff>::ReturnType>,
    {
        assert_contains_subsequence_kind(
            self,
            prefix,
            offset,
            find_prefix_close_to,
            "to start with the prefix",
        )
    }

    fn does_not_start_with_close_to<E, I, O>(self, prefix: I, offset: O) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>,
        O: Borrow<<C::Item as AbsDiff>::ReturnType>,
    {
        assert_does_not_contain_subsequence_kind(
            self,
            prefix,
            offset,
            find_prefix_close_to,
            "not to start with the prefix",
        )
    }

    fn ends_with_close_to<E, I, O>(self, suffix: I, offset: O) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>,
        O: Borrow<<C::Item as AbsDiff>::ReturnType>,
    {
        assert_contains_subsequence_kind(
            self,
            suffix,
            offset,
            find_suffix_close_to,
            "to end with the suffix",
        )
    }

    fn does_not_end_with_close_to<E, I, O>(self, suffix: I, offset: O) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>,
        O: Borrow<<C::Item as AbsDiff>::ReturnType>,
    {
        assert_does_not_contain_subsequence_kind(
            self,
            suffix,
            offset,
            find_suffix_close_to,
            "not to end with the suffix",
        )
    }

    fn contains_exactly_in_given_order_close_to<E, I, O>(self, items: I, offset: O) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>,
        O: Borrow<<C::Item as AbsDiff>::ReturnType>,
    {
        let offset = offset.borrow();
        let expected_it_suffix = format!(" within a margin of <{:?}>", offset);

        assert_contains_exactly_in_given_order_by(
            self,
            items,
            |expected, actual| &actual.abs_diff(expected) <= offset,
            &expected_it_suffix,
        )
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::{assert_fails, assert_that};

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

    #[test]
    fn contains_contiguous_subsequence_close_to_passes_for_empty_sequences() {
        assert_that!([] as [f32; 0]).contains_contiguous_subsequence_close_to([] as [f32; 0], 0.0);
    }

    #[test]
    fn contains_contiguous_subsequence_close_to_passes_for_empty_subsequence() {
        assert_that!([1.5]).contains_contiguous_subsequence_close_to([] as [f32; 0], 0.0);
    }

    #[test]
    fn contains_contiguous_subsequence_close_to_passes_for_same_sequence() {
        assert_that!([1.5, 1.7, 1.9])
            .contains_contiguous_subsequence_close_to([1.5, 1.7, 1.9], 0.0);
    }

    #[test]
    fn contains_contiguous_subsequence_close_to_passes_for_approximate_prefix() {
        assert_that!([1.414, 1.732, 2.000, 2.236])
            .contains_contiguous_subsequence_close_to([1.42, 1.73], 0.1);
    }

    #[test]
    fn contains_contiguous_subsequence_close_to_passes_for_approximate_infix() {
        assert_that!([1.414, 1.732, 2.000, 2.236])
            .contains_contiguous_subsequence_close_to([1.73, 2.0], 0.1);
    }

    #[test]
    fn contains_contiguous_subsequence_close_to_passes_for_approximate_suffix() {
        assert_that!([1.414, 1.732, 2.000, 2.236])
            .contains_contiguous_subsequence_close_to([2.0, 2.24], 0.1);
    }

    #[test]
    fn contains_contiguous_subsequence_close_to_fails_for_empty_sequence() {
        assert_fails!(([] as [f32; 0]).contains_contiguous_subsequence_close_to([1.5], 100.0),
            expected it "to contain the contiguous subsequence <[ 1.5 ]> within a margin of <100.0>"
            but it "was <[ ]>");
    }

    #[test]
    fn contains_contiguous_subsequence_close_to_fails_for_singleton_not_contained_in_sequence() {
        assert_fails!(([1.2, 1.3, 1.7]).contains_contiguous_subsequence_close_to([1.5], 0.1),
            expected it "to contain the contiguous subsequence <[ 1.5 ]> within a margin of <0.1>"
            but it "was <[ 1.2, 1.3, 1.7 ]>");
    }

    #[test]
    fn contains_contiguous_subsequence_close_to_fails_for_single_item_just_above_range() {
        assert_fails!(([1.2, 1.3, 1.4, 1.5])
            .contains_contiguous_subsequence_close_to([1.15, 1.36, 1.4], 0.05),
            expected it "to contain the contiguous subsequence <[ 1.15, 1.36, 1.4 ]> within a \
                margin of <0.05>"
            but it "was <[ 1.2, 1.3, 1.4, 1.5 ]>");
    }

    #[test]
    fn contains_contiguous_subsequence_close_to_fails_for_single_item_just_below_range() {
        assert_fails!(([1.2, 1.3, 1.4, 1.5])
            .contains_contiguous_subsequence_close_to([1.15, 1.24, 1.4], 0.05),
            expected it "to contain the contiguous subsequence <[ 1.15, 1.24, 1.4 ]> within a \
                margin of <0.05>"
            but it "was <[ 1.2, 1.3, 1.4, 1.5 ]>");
    }

    #[test]
    fn contains_contiguous_subsequence_close_to_fails_for_disjointed_subsequence() {
        assert_fails!(([1.414, 1.732, 2.000, 2.236])
            .contains_contiguous_subsequence_close_to([1.41, 2.0, 2.24], 0.01),
            expected it "to contain the contiguous subsequence <[ 1.41, 2.0, 2.24 ]> within a \
                margin of <0.01>"
            but it "was <[ 1.414, 1.732, 2.0, 2.236 ]>");
    }

    #[test]
    fn does_not_contain_contiguous_subsequence_close_to_passes_for_empty_sequence() {
        assert_that!([] as [f32; 0]).does_not_contain_contiguous_subsequence_close_to([1.5], 100.0);
    }

    #[test]
    fn does_not_contain_contiguous_subsequence_close_to_passes_for_singleton_not_contained_in_sequence()
     {
        assert_that!([1.2, 1.3, 1.7]).does_not_contain_contiguous_subsequence_close_to([1.5], 0.1);
    }

    #[test]
    fn does_not_contain_contiguous_subsequence_close_to_passes_for_single_item_just_above_range() {
        assert_that!([1.2, 1.3, 1.4, 1.5])
            .does_not_contain_contiguous_subsequence_close_to([1.15, 1.36, 1.4], 0.05);
    }

    #[test]
    fn does_not_contain_contiguous_subsequence_close_to_passes_for_single_item_just_below_range() {
        assert_that!([1.2, 1.3, 1.4, 1.5])
            .does_not_contain_contiguous_subsequence_close_to([1.15, 1.24, 1.4], 0.05);
    }

    #[test]
    fn does_not_contain_contiguous_subsequence_close_to_passes_for_disjointed_subsequence() {
        assert_that!([1.414, 1.732, 2.000, 2.236])
            .does_not_contain_contiguous_subsequence_close_to([1.41, 2.0, 2.24], 0.01);
    }

    #[test]
    fn does_not_contain_contiguous_subsequence_close_to_fails_for_empty_sequences() {
        assert_fails!(([] as [f32; 0])
            .does_not_contain_contiguous_subsequence_close_to([] as [f32; 0], 100.0),
            expected it "not to contain the contiguous subsequence <[ ]> within a margin of <100.0>"
            but it "was <[ [] ]>");
    }

    #[test]
    fn does_not_contain_contiguous_subsequence_close_to_fails_for_empty_subsequence() {
        assert_fails!(([1.5]).does_not_contain_contiguous_subsequence_close_to([] as [f32; 0], 0.0),
            expected it "not to contain the contiguous subsequence <[ ]> within a margin of <0.0>"
            but it "was <[ [] 1.5 ]>");
    }

    #[test]
    fn does_not_contain_contiguous_subsequence_close_to_fails_for_same_sequence() {
        assert_fails!(([1.5, 1.7, 1.9])
            .does_not_contain_contiguous_subsequence_close_to([1.5, 1.7, 1.9], 0.0),
            expected it "not to contain the contiguous subsequence <[ 1.5, 1.7, 1.9 ]> within a \
                margin of <0.0>"
            but it "was <[ [1.5, 1.7, 1.9] ]>");
    }

    #[test]
    fn does_not_contain_contiguous_subsequence_close_to_fails_for_approximate_prefix() {
        assert_fails!(([1.414, 1.732, 2.000, 2.236])
            .does_not_contain_contiguous_subsequence_close_to([1.42, 1.73], 0.01),
            expected it "not to contain the contiguous subsequence <[ 1.42, 1.73 ]> within a \
                margin of <0.01>"
            but it "was <[ [1.414, 1.732], 2.0, 2.236 ]>");
    }

    #[test]
    fn does_not_contain_contiguous_subsequence_close_to_fails_for_approximate_infix() {
        assert_fails!(([1.414, 1.732, 2.000, 2.236])
            .does_not_contain_contiguous_subsequence_close_to([1.73, 2.0], 0.01),
            expected it "not to contain the contiguous subsequence <[ 1.73, 2.0 ]> within a margin \
                of <0.01>"
            but it "was <[ 1.414, [1.732, 2.0], 2.236 ]>");
    }

    #[test]
    fn does_not_contain_contiguous_subsequence_close_to_fails_for_approximate_suffix() {
        assert_fails!(([1.414, 1.732, 2.000, 2.236])
            .does_not_contain_contiguous_subsequence_close_to([2.0, 2.24], 0.01),
            expected it "not to contain the contiguous subsequence <[ 2.0, 2.24 ]> within a margin \
                of <0.01>"
            but it "was <[ 1.414, 1.732, [2.0, 2.236] ]>");
    }

    #[test]
    fn contains_subsequence_close_to_passes_for_empty_sequences() {
        assert_that!([] as [f32; 0]).contains_subsequence_close_to([] as [f32; 0], 0.0);
    }

    #[test]
    fn contains_subsequence_close_to_passes_for_empty_subsequence() {
        assert_that!([1.4, 1.6, 1.8]).contains_subsequence_close_to([] as [f32; 0], 0.0);
    }

    #[test]
    fn contains_subsequence_close_to_passes_for_exact_sequence() {
        assert_that!([1.4, 1.6, 1.8]).contains_subsequence_close_to([1.4, 1.6, 1.8], 0.0);
    }

    #[test]
    fn contains_subsequence_close_to_passes_for_approximate_contiguous_subsequence() {
        assert_that!([1.414, 1.732, 2.000, 2.236])
            .contains_subsequence_close_to([1.73, 2.00], 0.01);
    }

    #[test]
    fn contains_subsequence_close_to_passes_for_approximate_non_contiguous_subsequence() {
        assert_that!([1.414, 1.732, 2.000, 2.236])
            .contains_subsequence_close_to([1.41, 2.24], 0.01);
    }

    #[test]
    fn contains_subsequence_close_to_fails_for_empty_sequence() {
        assert_fails!(([] as [f32; 0]).contains_subsequence_close_to([1.0], 100.0),
            expected it "to contain the subsequence <[ 1.0 ]> within a margin of <100.0>"
            but it "was <[ ]>");
    }

    #[test]
    fn contains_subsequence_close_to_fails_for_out_of_order_sequence() {
        assert_fails!(([1.2, 1.4, 1.6]).contains_subsequence_close_to([1.6, 1.2], 0.1),
            expected it "to contain the subsequence <[ 1.6, 1.2 ]> within a margin of <0.1>"
            but it "was <[ 1.2, 1.4, 1.6 ]>");
    }

    #[test]
    fn contains_subsequence_close_to_fails_for_sequence_with_element_just_above_range() {
        assert_fails!(([1.414, 1.732, 2.000, 2.236])
            .contains_subsequence_close_to([1.41, 2.247], 0.01),
            expected it "to contain the subsequence <[ 1.41, 2.247 ]> within a margin of <0.01>"
            but it "was <[ 1.414, 1.732, 2.0, 2.236 ]>");
    }

    #[test]
    fn contains_subsequence_close_to_fails_for_sequence_with_element_just_below_range() {
        assert_fails!(([1.414, 1.732, 2.000, 2.236])
            .contains_subsequence_close_to([1.403, 2.0], 0.01),
            expected it "to contain the subsequence <[ 1.403, 2.0 ]> within a margin of <0.01>"
            but it "was <[ 1.414, 1.732, 2.0, 2.236 ]>");
    }

    #[test]
    fn does_not_contain_subsequence_close_to_passes_for_empty_sequence() {
        assert_that!([] as [f32; 0]).does_not_contain_subsequence_close_to([1.0], 100.0);
    }

    #[test]
    fn does_not_contain_subsequence_close_to_passes_for_out_of_order_sequence() {
        assert_that!([1.2, 1.4, 1.6]).does_not_contain_subsequence_close_to([1.6, 1.2], 0.1);
    }

    #[test]
    fn does_not_contain_subsequence_close_to_passes_for_sequence_with_element_just_above_range() {
        assert_that!([1.414, 1.732, 2.000, 2.236])
            .does_not_contain_subsequence_close_to([1.41, 2.247], 0.01);
    }

    #[test]
    fn does_not_contain_subsequence_close_to_passes_for_sequence_with_element_just_below_range() {
        assert_that!([1.414, 1.732, 2.000, 2.236])
            .does_not_contain_subsequence_close_to([1.403, 2.0], 0.01);
    }

    #[test]
    fn does_not_contain_subsequence_close_to_fails_for_empty_sequences() {
        assert_fails!(([] as [f32; 0]).does_not_contain_subsequence_close_to([] as [f32; 0], 100.0),
            expected it "not to contain the subsequence <[ ]> within a margin of <100.0>"
            but it "was <[ [] ]>");
    }

    #[test]
    fn does_not_contain_subsequence_close_to_fails_for_empty_subsequence() {
        assert_fails!(([1.4, 1.6, 1.8]).does_not_contain_subsequence_close_to([] as [f32; 0], 0.0),
            expected it "not to contain the subsequence <[ ]> within a margin of <0.0>"
            but it "was <[ [] 1.4, 1.6, 1.8 ]>");
    }

    #[test]
    fn does_not_contain_subsequence_close_to_fails_for_exact_sequence() {
        assert_fails!(([1.4, 1.6, 1.8]).does_not_contain_subsequence_close_to([1.4, 1.6, 1.8], 0.0),
            expected it "not to contain the subsequence <[ 1.4, 1.6, 1.8 ]> within a margin of \
                <0.0>"
            but it "was <[ [1.4, 1.6, 1.8] ]>");
    }

    #[test]
    fn does_not_contain_subsequence_close_to_fails_for_approximate_contiguous_subsequence() {
        assert_fails!(([1.414, 1.732, 2.000, 2.236])
            .does_not_contain_subsequence_close_to([1.73, 2.00], 0.01),
            expected it "not to contain the subsequence <[ 1.73, 2.0 ]> within a margin of <0.01>"
            but it "was <[ 1.414, [1.732, 2.0], 2.236 ]>");
    }

    #[test]
    fn does_not_contain_subsequence_close_to_fails_for_approximate_non_contiguous_subsequence() {
        assert_fails!(([1.414, 1.732, 2.000, 2.236])
            .does_not_contain_subsequence_close_to([1.41, 2.24], 0.01),
            expected it "not to contain the subsequence <[ 1.41, 2.24 ]> within a margin of <0.01>"
            but it "was <[ [1.414], 1.732, 2.0, [2.236] ]>");
    }

    #[test]
    fn starts_with_close_to_passes_for_empty_sequences() {
        assert_that!([] as [f32; 0]).starts_with_close_to([] as [f32; 0], 0.0);
    }

    #[test]
    fn starts_with_close_to_passes_for_empty_subsequence() {
        assert_that!([1.2, 1.3]).starts_with_close_to([] as [f32; 0], 0.0);
    }

    #[test]
    fn starts_with_close_to_passes_for_exact_prefix() {
        assert_that!([1.414, 1.732, 2.000, 2.236]).starts_with_close_to([1.414, 1.732], 0.0);
    }

    #[test]
    fn starts_with_close_to_passes_for_approximate_prefix() {
        assert_that!([1.414, 1.732, 2.000, 2.236]).starts_with_close_to([1.41, 1.73], 0.01);
    }

    #[test]
    fn starts_with_close_to_fails_for_empty_tested_sequence() {
        assert_fails!(([] as [f32; 0]).starts_with_close_to([0.0], 100.0),
            expected it "to start with the prefix <[ 0.0 ]> within a margin of <100.0>"
            but it "was <[ ]>");
    }

    #[test]
    fn starts_with_close_to_fails_for_value_just_below_range() {
        assert_fails!(([1.414, 1.732, 2.000, 2.236]).starts_with_close_to([1.42, 1.74], 0.007),
            expected it "to start with the prefix <[ 1.42, 1.74 ]> within a margin of <0.007>"
            but it "was <[ 1.414, 1.732, 2.0, 2.236 ]>");
    }

    #[test]
    fn starts_with_close_to_fails_for_value_just_above_range() {
        assert_fails!(([1.414, 1.732, 2.000, 2.236]).starts_with_close_to([1.41, 1.73], 0.003),
            expected it "to start with the prefix <[ 1.41, 1.73 ]> within a margin of <0.003>"
            but it "was <[ 1.414, 1.732, 2.0, 2.236 ]>");
    }

    #[test]
    fn starts_with_close_to_fails_for_infix() {
        assert_fails!(([1.414, 1.732, 2.000, 2.236]).starts_with_close_to([1.73, 2.00], 0.01),
            expected it "to start with the prefix <[ 1.73, 2.0 ]> within a margin of <0.01>"
            but it "was <[ 1.414, 1.732, 2.0, 2.236 ]>");
    }

    #[test]
    fn starts_with_close_to_fails_for_suffix() {
        assert_fails!(([1.414, 1.732, 2.000, 2.236]).starts_with_close_to([2.00, 2.24], 0.01),
            expected it "to start with the prefix <[ 2.0, 2.24 ]> within a margin of <0.01>"
            but it "was <[ 1.414, 1.732, 2.0, 2.236 ]>");
    }

    #[test]
    fn starts_with_close_to_fails_for_non_contiguous_subsequence() {
        assert_fails!(([1.414, 1.732, 2.000, 2.236]).starts_with_close_to([1.42, 2.0], 0.01),
            expected it "to start with the prefix <[ 1.42, 2.0 ]> within a margin of <0.01>"
            but it "was <[ 1.414, 1.732, 2.0, 2.236 ]>");
    }

    #[test]
    fn does_not_start_with_close_to_passes_for_empty_tested_sequence() {
        assert_that!([] as [f32; 0]).does_not_start_with_close_to([0.0], 100.0);
    }

    #[test]
    fn does_not_start_with_close_to_passes_for_value_just_below_range() {
        assert_that!([1.414, 1.732, 2.000, 2.236])
            .does_not_start_with_close_to([1.42, 1.74], 0.007);
    }

    #[test]
    fn does_not_start_with_close_to_passes_for_value_just_above_range() {
        assert_that!([1.414, 1.732, 2.000, 2.236])
            .does_not_start_with_close_to([1.41, 1.73], 0.003);
    }

    #[test]
    fn does_not_start_with_close_to_passes_for_infix() {
        assert_that!([1.414, 1.732, 2.000, 2.236]).does_not_start_with_close_to([1.73, 2.00], 0.01);
    }

    #[test]
    fn does_not_start_with_close_to_passes_for_suffix() {
        assert_that!([1.414, 1.732, 2.000, 2.236]).does_not_start_with_close_to([2.00, 2.24], 0.01);
    }

    #[test]
    fn does_not_start_with_close_to_passes_for_non_contiguous_subsequence() {
        assert_that!([1.414, 1.732, 2.000, 2.236]).does_not_start_with_close_to([1.42, 2.0], 0.01);
    }

    #[test]
    fn does_not_start_with_close_to_fails_for_empty_sequences() {
        assert_fails!(([] as [f32; 0]).does_not_start_with_close_to([] as [f32; 0], 0.0),
            expected it "not to start with the prefix <[ ]> within a margin of <0.0>"
            but it "was <[ [] ]>");
    }

    #[test]
    fn does_not_start_with_close_to_fails_for_empty_subsequence() {
        assert_fails!(([1.2, 1.3]).does_not_start_with_close_to([] as [f32; 0], 0.0),
            expected it "not to start with the prefix <[ ]> within a margin of <0.0>"
            but it "was <[ [] 1.2, 1.3 ]>");
    }

    #[test]
    fn does_not_start_with_close_to_fails_for_exact_prefix() {
        assert_fails!(([1.414, 1.732, 2.000, 2.236])
            .does_not_start_with_close_to([1.414, 1.732], 0.0),
            expected it "not to start with the prefix <[ 1.414, 1.732 ]> within a margin of <0.0>"
            but it "was <[ [1.414, 1.732], 2.0, 2.236 ]>");
    }

    #[test]
    fn does_not_start_with_close_to_fails_for_approximate_prefix() {
        assert_fails!(([1.414, 1.732, 2.000, 2.236])
            .does_not_start_with_close_to([1.41, 1.74], 0.01),
            expected it "not to start with the prefix <[ 1.41, 1.74 ]> within a margin of <0.01>"
            but it "was <[ [1.414, 1.732], 2.0, 2.236 ]>");
    }

    #[test]
    fn ends_with_close_to_passes_for_empty_sequences() {
        assert_that!([] as [f32; 0]).ends_with_close_to([] as [f32; 0], 0.0);
    }

    #[test]
    fn ends_with_close_to_passes_for_empty_subsequence() {
        assert_that!([1.2, 1.3]).ends_with_close_to([] as [f32; 0], 0.0);
    }

    #[test]
    fn ends_with_close_to_passes_for_exact_suffix() {
        assert_that!([1.414, 1.732, 2.000, 2.236]).ends_with_close_to([2.0, 2.236], 0.0);
    }

    #[test]
    fn ends_with_close_to_passes_for_approximate_suffix() {
        assert_that!([1.414, 1.732, 2.000, 2.236]).ends_with_close_to([2.01, 2.24], 0.02);
    }

    #[test]
    fn ends_with_close_to_fails_for_empty_tested_sequence() {
        assert_fails!(([] as [f32; 0]).ends_with_close_to([0.0], 100.0),
            expected it "to end with the suffix <[ 0.0 ]> within a margin of <100.0>"
            but it "was <[ ]>");
    }

    #[test]
    fn ends_with_close_to_fails_for_value_just_below_range() {
        assert_fails!(([1.414, 1.732, 2.000, 2.236]).ends_with_close_to([2.0, 2.23], 0.005),
            expected it "to end with the suffix <[ 2.0, 2.23 ]> within a margin of <0.005>"
            but it "was <[ 1.414, 1.732, 2.0, 2.236 ]>");
    }

    #[test]
    fn ends_with_close_to_fails_for_value_just_above_range() {
        assert_fails!(([1.414, 1.732, 2.000, 2.236]).ends_with_close_to([2.0, 2.24], 0.003),
            expected it "to end with the suffix <[ 2.0, 2.24 ]> within a margin of <0.003>"
            but it "was <[ 1.414, 1.732, 2.0, 2.236 ]>");
    }

    #[test]
    fn ends_with_close_to_fails_for_infix() {
        assert_fails!(([1.414, 1.732, 2.000, 2.236]).ends_with_close_to([1.73, 2.00], 0.01),
            expected it "to end with the suffix <[ 1.73, 2.0 ]> within a margin of <0.01>"
            but it "was <[ 1.414, 1.732, 2.0, 2.236 ]>");
    }

    #[test]
    fn ends_with_close_to_fails_for_prefix() {
        assert_fails!(([1.414, 1.732, 2.000, 2.236]).ends_with_close_to([1.41, 1.73], 0.01),
            expected it "to end with the suffix <[ 1.41, 1.73 ]> within a margin of <0.01>"
            but it "was <[ 1.414, 1.732, 2.0, 2.236 ]>");
    }

    #[test]
    fn ends_with_close_to_fails_for_non_contiguous_subsequence() {
        assert_fails!(([1.414, 1.732, 2.000, 2.236]).ends_with_close_to([1.73, 2.23], 0.01),
            expected it "to end with the suffix <[ 1.73, 2.23 ]> within a margin of <0.01>"
            but it "was <[ 1.414, 1.732, 2.0, 2.236 ]>");
    }

    #[test]
    fn does_not_end_with_close_to_passes_for_empty_tested_sequence() {
        assert_that!([] as [f32; 0]).does_not_end_with_close_to([0.0], 100.0);
    }

    #[test]
    fn does_not_end_with_close_to_passes_for_value_just_below_range() {
        assert_that!([1.414, 1.732, 2.000, 2.236]).does_not_end_with_close_to([2.0, 2.24], 0.003);
    }

    #[test]
    fn does_not_end_with_close_to_passes_for_value_just_above_range() {
        assert_that!([1.414, 1.732, 2.000, 2.236]).does_not_end_with_close_to([2.0, 2.23], 0.005);
    }

    #[test]
    fn does_not_end_with_close_to_passes_for_infix() {
        assert_that!([1.414, 1.732, 2.000, 2.236]).does_not_end_with_close_to([1.73, 2.00], 0.01);
    }

    #[test]
    fn does_not_end_with_close_to_passes_for_prefix() {
        assert_that!([1.414, 1.732, 2.000, 2.236]).does_not_end_with_close_to([1.41, 1.73], 0.01);
    }

    #[test]
    fn does_not_end_with_close_to_passes_for_non_contiguous_subsequence() {
        assert_that!([1.414, 1.732, 2.000, 2.236]).does_not_end_with_close_to([1.73, 2.24], 0.01);
    }

    #[test]
    fn does_not_end_with_close_to_fails_for_empty_sequences() {
        assert_fails!(([] as [f32; 0]).does_not_end_with_close_to([] as [f32; 0], 0.0),
            expected it "not to end with the suffix <[ ]> within a margin of <0.0>"
            but it "was <[ [] ]>");
    }

    #[test]
    fn does_not_end_with_close_to_fails_for_empty_subsequence() {
        assert_fails!(([1.2, 1.3]).does_not_end_with_close_to([] as [f32; 0], 0.0),
            expected it "not to end with the suffix <[ ]> within a margin of <0.0>"
            but it "was <[ 1.2, 1.3 [] ]>");
    }

    #[test]
    fn does_not_end_with_close_to_fails_for_exact_suffix() {
        assert_fails!(([1.414, 1.732, 2.000, 2.236]).does_not_end_with_close_to([2.0, 2.236], 0.0),
            expected it "not to end with the suffix <[ 2.0, 2.236 ]> within a margin of <0.0>"
            but it "was <[ 1.414, 1.732, [2.0, 2.236] ]>");
    }

    #[test]
    fn does_not_end_with_close_to_fails_for_approximate_suffix() {
        assert_fails!(([1.414, 1.732, 2.000, 2.236])
            .does_not_end_with_close_to([1.99, 2.25], 0.02),
            expected it "not to end with the suffix <[ 1.99, 2.25 ]> within a margin of <0.02>"
            but it "was <[ 1.414, 1.732, [2.0, 2.236] ]>");
    }

    #[test]
    fn contains_exactly_in_given_order_close_to_passes_for_empty_sequences() {
        assert_that!([] as [f32; 0]).contains_exactly_in_given_order_close_to([] as [f32; 0], 0.0);
    }

    #[test]
    fn contains_exactly_in_given_order_close_to_passes_for_exact_sequence() {
        assert_that!([1.2, 1.3]).contains_exactly_in_given_order_close_to([1.2, 1.3], 0.0);
    }

    #[test]
    fn contains_exactly_in_given_order_close_to_passes_for_approximate_sequence() {
        assert_that!([1.414, 1.732, 2.000, 2.236])
            .contains_exactly_in_given_order_close_to([1.41, 1.73, 2.0, 2.24], 0.005);
    }

    #[test]
    fn contains_exactly_in_given_order_close_to_fails_for_empty_sequence() {
        assert_fails!(([] as [f32; 0]).contains_exactly_in_given_order_close_to([0.0], 100.0),
            expected it "to contain exactly in the given order <[ 0.0 ]> within a margin of <100.0>"
            but it "was <[ [] ]>");
    }

    #[test]
    fn contains_exactly_in_given_order_close_to_fails_for_empty_subsequence() {
        assert_fails!(([1.0]).contains_exactly_in_given_order_close_to([] as [f32; 0], 100.0),
            expected it "to contain exactly in the given order <[ ]> within a margin of <100.0>"
            but it "was <[ [1.0] ]>");
    }

    #[test]
    fn contains_exactly_in_given_order_close_to_fails_for_collection_missing_last_element() {
        assert_fails!(([1.414, 1.732, 2.000])
            .contains_exactly_in_given_order_close_to([1.41, 1.73, 2.0, 2.24], 0.005),
            expected it "to contain exactly in the given order <[ 1.41, 1.73, 2.0, 2.24 ]> within \
                a margin of <0.005>"
            but it "was <[ 1.414, 1.732, 2.0 [] ]>");
    }

    #[test]
    fn contains_exactly_in_given_order_close_to_fails_for_collection_with_extra_element() {
        assert_fails!(([1.414, 1.732, 2.000, 2.236])
            .contains_exactly_in_given_order_close_to([1.41, 1.73, 2.0], 0.005),
            expected it "to contain exactly in the given order <[ 1.41, 1.73, 2.0 ]> within a \
                margin of <0.005>"
            but it "was <[ 1.414, 1.732, 2.0, [2.236] ]>");
    }

    #[test]
    fn contains_exactly_in_given_order_close_to_fails_for_item_just_below_range() {
        assert_fails!(([1.414, 1.732, 2.000, 2.236])
            .contains_exactly_in_given_order_close_to([1.41, 1.73, 2.0, 2.25], 0.013),
            expected it "to contain exactly in the given order <[ 1.41, 1.73, 2.0, 2.25 ]> within \
                a margin of <0.013>"
            but it "was <[ 1.414, 1.732, 2.0, [2.236] ]>");
    }

    #[test]
    fn contains_exactly_in_given_order_close_to_fails_for_item_just_above_range() {
        assert_fails!(([1.414, 1.732, 2.000, 2.236])
            .contains_exactly_in_given_order_close_to([1.41, 1.73, 2.0, 2.23], 0.005),
            expected it "to contain exactly in the given order <[ 1.41, 1.73, 2.0, 2.23 ]> within \
                a margin of <0.005>"
            but it "was <[ 1.414, 1.732, 2.0, [2.236] ]>");
    }
}
