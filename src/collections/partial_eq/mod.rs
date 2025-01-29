//! Contains specialized assertions for [Collection]s and [OrderedCollection]s whose items implement
//! [PartialEq]. See [CollectionPartialEqAssertions] and [OrderedCollectionPartialEqAssertions] for
//! more details.

use std::borrow::Borrow;
use std::fmt::Debug;
use std::ops::Range;

use crate::{AssertThat, Failure};
use crate::collections::{
    assert_all_match_predicate,
    assert_contains_exactly_in_given_order_by,
    Collection,
    CollectionDebug,
    HighlightedCollectionDebug
};
use crate::util::multiset::vec::VecMultiset;
use crate::collections::{
    find_contiguous_subsequence_by,
    find_prefix_by,
    find_subsequence_by,
    find_suffix_by
};
use crate::collections::ordered::OrderedCollection;
use crate::util::{borrow_all, Set};
use crate::util::multiset::Multiset;

pub mod btree;
pub mod hash;

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with an
/// argument that implements the [Collection] trait where the [Collection::Item] type implements
/// [PartialEq] in addition to the required [Debug] trait.
///
/// Examples:
///
/// ```
/// use kernal::prelude::*;
///
/// assert_that!(&["hello", "world"]).contains("hello").contains_none_of(&["apple", "banana"]);
/// assert_that!(&[1, 2, 3]).does_not_contain(4).contains_exactly_in_any_order(&[3, 2, 1]);
/// ```
pub trait CollectionPartialEqAssertions<'collection, C>
where
    C: Collection<'collection>
{
    /// Asserts that the tested collection contains at least one element which is equal to the given
    /// `item` according to [PartialEq].
    fn contains<E: Borrow<C::Item>>(self, item: E) -> Self;

    /// Asserts that the tested collection contains no element which is equal to the given `item`
    /// according to [PartialEq].
    fn does_not_contain<E: Borrow<C::Item>>(self, item: E) -> Self;

    /// Asserts that for each of the given `items`, the tested collection contains an equal element
    /// according to [PartialEq]. If the provided iterator contains multiple equal elements, this
    /// function asserts that the tested collection contains at least that number of equal elements,
    /// so `[1, 1, 2]` contains all of `[1, 1]`, but not all of `[1, 1, 1]`.
    ///
    /// This operation might be slow for large collections. If this is an issue, consider using
    /// [CollectionEqHashAssertions::contains_all_of_using_hash](hash::CollectionEqHashAssertions::contains_all_of_using_hash)
    /// or
    /// [CollectionEqOrdAssertions::contains_all_of_using_ord](btree::CollectionEqOrdAssertions::contains_all_of_using_ord)
    /// instead, if applicable for the item type.
    fn contains_all_of<E: Borrow<C::Item>, I: IntoIterator<Item = E>>(self, items: I) -> Self;

    /// Asserts that the tested collection contains no element which is equal to one the given
    /// `items` according to [PartialEq].
    ///
    /// This operation might be slow for large collections. If this is an issue, consider using
    /// [CollectionEqHashAssertions::contains_none_of_using_hash](hash::CollectionEqHashAssertions::contains_none_of_using_hash)
    /// or
    /// [CollectionEqOrdAssertions::contains_none_of_using_ord](btree::CollectionEqOrdAssertions::contains_none_of_using_ord)
    /// instead, if applicable for the item type.
    fn contains_none_of<E: Borrow<C::Item>, I: IntoIterator<Item = E>>(self, items: I) -> Self;

    /// Asserts that there is a one-to-one matching of the given `items` and the elements of the
    /// tested collection such that matched elements are equal according to [PartialEq].
    ///
    /// This operation might be slow for large collections. If this is an issue, consider using
    /// [CollectionEqHashAssertions::contains_exactly_in_any_order_using_hash](hash::CollectionEqHashAssertions::contains_exactly_in_any_order_using_hash)
    /// or
    /// [CollectionEqOrdAssertions::contains_exactly_in_any_order_using_ord](btree::CollectionEqOrdAssertions::contains_exactly_in_any_order_using_ord)
    /// instead, if applicable for the item type.
    fn contains_exactly_in_any_order<E, I>(self, items: I) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>;
}

pub(crate) fn compute_missing_and_superfluous<'item, T, M, I>(actual_items: I,
    expected_items: &'item [&T]) -> (M, M)
where
    T: Debug + 'item,
    M: Multiset<&'item T>,
    I: Iterator<Item = &'item T>
{
    let expected_items: Vec<&T> = borrow_all(expected_items);
    let mut missing_multiset = expected_items.iter().cloned().collect::<M>();
    let mut superfluous_multiset = M::new();

    for item in actual_items {
        if !missing_multiset.remove(&item) {
            superfluous_multiset.add(item);
        }
    }

    (missing_multiset, superfluous_multiset)
}

pub(crate) fn format_error_for_missing_and_superfluous<T, M>(missing_items: &M,
    superfluous_items: &M) -> String
where
    T: Debug,
    M: Multiset<T>
{
    let mut errors = Vec::new();

    if !missing_items.is_empty() {
        errors.push(format!("lacks {:?}", missing_items));
    }

    if !superfluous_items.is_empty() {
        errors.push(format!("additionally has {:?}", superfluous_items));
    }

    errors.join(" and ")
}

pub(crate) fn check_contains_all_of<'collection, 'item, C, I, M>(
    assert_that: &AssertThat<C>, actual_items: I, expected_items: &'item [&C::Item])
where
    C: Collection<'collection>,
    C::Item: Debug + 'item,
    I: Iterator<Item = &'item C::Item>,
    M: Multiset<&'item C::Item>
{
    let (missing_multiset, _) =
        compute_missing_and_superfluous::<_, M, _>(
            actual_items, expected_items);

    if !missing_multiset.is_empty() {
        let expected_items_debug = CollectionDebug { collection: &expected_items };
        let collection_debug = CollectionDebug { collection: &assert_that.data };

        Failure::new(assert_that)
            .expected_it(format!("to contain all of <{:?}>", expected_items_debug))
            .but_it(format!("was <{:?}>, which lacks {:?}",
                collection_debug, &missing_multiset))
            .fail();
    }
}

pub(crate) fn check_contains_none_of<'collection, 'item, C, I, S>(
    assert_that: &AssertThat<C>, actual_items: I, unexpected_items: Vec<&'item C::Item>)
where
    C: Collection<'collection>,
    C::Item: Debug + 'item,
    I: Iterator<Item = &'item C::Item>,
    S: Set<&'item C::Item>
{
    let unexpected_items_set = S::from_iter(unexpected_items.iter().cloned());

    for (index, item) in actual_items.enumerate() {
        if unexpected_items_set.contains(&item) {
            let unexpected_items_debug = CollectionDebug { collection: &unexpected_items };

            Failure::new(assert_that)
                .expected_it(format!("not to contain any of <{:?}>", unexpected_items_debug))
                .but_it(format!("was <{:?}>",
                    HighlightedCollectionDebug::with_single_highlighted_element(
                        &assert_that.data, index)))
                .fail();
        }
    }
}

pub(crate) fn check_contains_exactly_in_any_order<'collection, 'item, C, I, M>(
    assert_that: &AssertThat<C>, actual_items: I, expected_items: &'item [&C::Item])
where
    C: Collection<'collection>,
    C::Item: Debug + 'item,
    I: Iterator<Item = &'item C::Item>,
    M: Multiset<&'item C::Item>
{
    let (missing_multiset, superfluous_multiset) =
        compute_missing_and_superfluous::<_, M, _>(actual_items, expected_items);

    if !missing_multiset.is_empty() || !superfluous_multiset.is_empty() {
        let expected_items_debug = CollectionDebug { collection: &expected_items };
        let collection_debug = CollectionDebug { collection: &assert_that.data };
        let error =
            format_error_for_missing_and_superfluous(&missing_multiset, &superfluous_multiset);

        Failure::new(assert_that)
            .expected_it(format!("to contain exactly in any order <{:?}>", expected_items_debug))
            .but_it(format!("was <{:?}>, which {}", collection_debug, error))
            .fail();
    }
}

impl<'collection, C> CollectionPartialEqAssertions<'collection, C> for AssertThat<C>
where
    C: Collection<'collection>,
    C::Item: Debug + PartialEq
{
    fn contains<E: Borrow<C::Item>>(self, item: E) -> Self {
        let item = item.borrow();

        if !self.data.iterator().any(|collection_item| collection_item == item) {
            Failure::new(&self)
                .expected_it(format!("to contain <{:?}>", item))
                .but_it(format!("was <{:?}>", CollectionDebug { collection: &self.data }))
                .fail();
        }

        self
    }

    fn does_not_contain<E: Borrow<C::Item>>(self, item: E) -> Self {
        let item = item.borrow();
        let expected_it = format!("not to contain <{:?}>", item);

        assert_all_match_predicate(self, |collection_item| collection_item != item, &expected_it)
    }

    fn contains_all_of<E: Borrow<C::Item>, I: IntoIterator<Item = E>>(self, items: I) -> Self {
        let expected_items_unborrowed = items.into_iter().collect::<Vec<_>>();
        let expected_items: Vec<&C::Item> = borrow_all(&expected_items_unborrowed);

        check_contains_all_of::<_, _, VecMultiset<_>>(&self, self.data.iterator(), &expected_items);

        self
    }

    fn contains_none_of<E: Borrow<C::Item>, I: IntoIterator<Item = E>>(self, items: I) -> Self {
        let unexpected_items_unborrowed = items.into_iter().collect::<Vec<_>>();
        let unexpected_items: Vec<&C::Item> = borrow_all(&unexpected_items_unborrowed);

        check_contains_none_of::<_, _, Vec<_>>(&self, self.data.iterator(), unexpected_items);

        self
    }

    fn contains_exactly_in_any_order<E, I>(self, items: I) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>
    {
        let expected_items_unborrowed = items.into_iter().collect::<Vec<_>>();
        let expected_items: Vec<&C::Item> = borrow_all(&expected_items_unborrowed);

        check_contains_exactly_in_any_order::<_, _, VecMultiset<_>>(
            &self, self.data.iterator(), &expected_items);

        self
    }
}

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with an
/// argument that implements the [OrderedCollection] trait where the [Collection::Item] type
/// implements [PartialEq] in addition to the required [Debug] trait.
///
/// Examples:
///
/// ```
/// use kernal::prelude::*;
///
/// assert_that!(&[1, 2, 3, 4])
///     .does_not_contain_contiguous_subsequence(&[1, 3])
///     .contains_subsequence(&[1, 2, 4])
///     .starts_with(&[1, 2])
///     .does_not_end_with(&[2, 3]);
/// ```
pub trait OrderedCollectionPartialEqAssertions<'collection, C>
where
    C: OrderedCollection<'collection>
{
    /// Asserts that there is a contiguous subsequence in the tested collection that equals the
    /// given `subsequence` in order according to [PartialEq].
    fn contains_contiguous_subsequence<E, I>(self, subsequence: I) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>;

    /// Asserts that there is no contiguous subsequence in the tested collection that equals the
    /// given `subsequence` in order according to [PartialEq].
    fn does_not_contain_contiguous_subsequence<E, I>(self, subsequence: I) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>;

    /// Asserts that there is a subsequence (any subset that retains the ordering) of the tested
    /// collection that equals toe given `subsequence` in order according to [PartialEq].
    fn contains_subsequence<E, I>(self, subsequence: I) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>;

    /// Asserts that there is no subsequence (any subset that retains the ordering) of the tested
    /// collection that equals toe given `subsequence` in order according to [PartialEq].
    fn does_not_contain_subsequence<E, I>(self, subsequence: I) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>;

    /// Given a `prefix` of length `n`, asserts that the subsequence consisting of the first `n`
    /// elements of the tested collection is equal to the given `prefix` in order according to
    /// [PartialEq].
    fn starts_with<E: Borrow<C::Item>, I: IntoIterator<Item = E>>(self, prefix: I) -> Self;

    /// Given a `prefix` of length `n`, asserts that the subsequence consisting of the first `n`
    /// elements of the tested collection is not equal to the given `prefix` at at least one
    /// position according to [PartialEq].
    fn does_not_start_with<E: Borrow<C::Item>, I: IntoIterator<Item = E>>(self, prefix: I) -> Self;

    /// Given a `suffix` of length `n`, asserts that the subsequence consisting of the last `n`
    /// elements of the tested collection is equal to the given `suffix` in order according to
    /// [PartialEq].
    fn ends_with<E: Borrow<C::Item>, I: IntoIterator<Item = E>>(self, suffix: I) -> Self;

    /// Given a `suffix` of length `n`, asserts that the subsequence consisting of the last `n`
    /// elements of the tested collection is not equal to the given `suffix` at at least one
    /// position according to [PartialEq].
    fn does_not_end_with<E: Borrow<C::Item>, I: IntoIterator<Item = E>>(self, suffix: I) -> Self;

    /// Asserts that the elements contained in the tested collection are equal to the given `items`
    /// according to [PartialEq] and occur in the same order. In other words, the iterators obtained
    /// by both `items` and the tested collection contain equal elements at the same positions.
    fn contains_exactly_in_given_order<E, I>(self, items: I) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>;
}

fn find_contiguous_subsequence<'collection, C>(collection: &C, subsequence: &[&C::Item])
    -> Option<Vec<Range<usize>>>
where
    C: OrderedCollection<'collection>,
    C::Item: Debug + PartialEq
{
    find_contiguous_subsequence_by(collection, subsequence, PartialEq::eq)
}

fn find_subsequence<'collection, C>(collection: &C, subsequence: &[&C::Item])
    -> Option<Vec<Range<usize>>>
where
    C: OrderedCollection<'collection>,
    C::Item: Debug + PartialEq
{
    find_subsequence_by(collection, subsequence, PartialEq::eq)
}

fn find_prefix<'collection, C>(collection: &C, prefix: &[&C::Item]) -> Option<Vec<Range<usize>>>
where
    C: OrderedCollection<'collection>,
    C::Item: Debug + PartialEq
{
    find_prefix_by(collection, prefix, PartialEq::eq)
}

fn find_suffix<'collection, C>(collection: &C, suffix: &[&C::Item]) -> Option<Vec<Range<usize>>>
where
    C: OrderedCollection<'collection>,
    C::Item: Debug + PartialEq
{
    find_suffix_by(collection, suffix, PartialEq::eq)
}

fn assert_contains_subsequence_kind<'collection, C, E, I, F>(assert_that: AssertThat<C>,
    subsequence_of_kind: I, find_subsequence_of_kind: F, expected_it_prefix: &str) -> AssertThat<C>
where
    C: OrderedCollection<'collection>,
    C::Item: Debug + PartialEq,
    E: Borrow<C::Item>,
    I: IntoIterator<Item = E>,
    F: FnOnce(&C, &[&C::Item]) -> Option<Vec<Range<usize>>>
{
    let subsequence_of_kind_vec_unborrowed = subsequence_of_kind.into_iter().collect::<Vec<_>>();
    let subsequence_of_kind_vec: Vec<&C::Item> = borrow_all(&subsequence_of_kind_vec_unborrowed);

    if find_subsequence_of_kind(&assert_that.data, &subsequence_of_kind_vec).is_none() {
        let subsequence_of_kind_debug = CollectionDebug { collection: &subsequence_of_kind_vec };
        let collection_debug = CollectionDebug { collection: &assert_that.data };

        Failure::new(&assert_that)
            .expected_it(
                format!("{} <{:?}>", expected_it_prefix, subsequence_of_kind_debug))
            .but_it(format!("was <{:?}>", collection_debug))
            .fail();
    }

    assert_that
}

fn assert_does_not_contain_subsequence_kind<'collection, C, E, I, F>(assert_that: AssertThat<C>,
    subsequence_of_kind: I, find_subsequence_of_kind: F, expected_it_prefix: &str) -> AssertThat<C>
where
    C: OrderedCollection<'collection>,
    C::Item: Debug + PartialEq,
    E: Borrow<C::Item>,
    I: IntoIterator<Item = E>,
    F: FnOnce(&C, &[&C::Item]) -> Option<Vec<Range<usize>>>
{
    let subsequence_of_kind_vec_unborrowed = subsequence_of_kind.into_iter().collect::<Vec<_>>();
    let subsequence_of_kind_vec: Vec<&C::Item> = borrow_all(&subsequence_of_kind_vec_unborrowed);

    if let Some(first_occurrence_ranges) =
        find_subsequence_of_kind(&assert_that.data, &subsequence_of_kind_vec) {
        let subsequence_of_kind_debug = CollectionDebug { collection: &subsequence_of_kind_vec };
        let collection_debug = HighlightedCollectionDebug {
            collection: &assert_that.data,
            highlighted_sections: first_occurrence_ranges
        };

        Failure::new(&assert_that)
            .expected_it(format!("{} <{:?}>",
                expected_it_prefix, subsequence_of_kind_debug))
            .but_it(format!("was <{:?}>", collection_debug))
            .fail();
    }

    assert_that
}

impl<'collection, C> OrderedCollectionPartialEqAssertions<'collection, C> for AssertThat<C>
where
    C: OrderedCollection<'collection>,
    C::Item: Debug + PartialEq
{
    fn contains_contiguous_subsequence<E, I>(self, subsequence: I) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>
    {
        assert_contains_subsequence_kind(self,
            subsequence, find_contiguous_subsequence, "to contain the contiguous subsequence")
    }

    fn does_not_contain_contiguous_subsequence<E, I>(self, subsequence: I) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>
    {
        assert_does_not_contain_subsequence_kind(self,
            subsequence, find_contiguous_subsequence, "not to contain the contiguous subsequence")
    }

    fn contains_subsequence<E, I>(self, subsequence: I) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>
    {
        assert_contains_subsequence_kind(
            self, subsequence, find_subsequence, "to contain the subsequence")
    }

    fn does_not_contain_subsequence<E, I>(self, subsequence: I) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>
    {
        assert_does_not_contain_subsequence_kind(
            self, subsequence, find_subsequence, "not to contain the subsequence")
    }

    fn starts_with<E, I>(self, prefix: I) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>
    {
        assert_contains_subsequence_kind(self, prefix, find_prefix, "to start with the prefix")
    }

    fn does_not_start_with<E, I>(self, prefix: I) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>
    {
        assert_does_not_contain_subsequence_kind(
            self, prefix, find_prefix, "not to start with the prefix")
    }

    fn ends_with<E, I>(self, suffix: I) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>
    {
        assert_contains_subsequence_kind(self, suffix, find_suffix, "to end with the suffix")
    }

    fn does_not_end_with<E, I>(self, suffix: I) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>
    {
        assert_does_not_contain_subsequence_kind(
            self, suffix, find_suffix, "not to end with the suffix")
    }

    fn contains_exactly_in_given_order<E, I>(self, items: I) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>
    {
        assert_contains_exactly_in_given_order_by(self, items, PartialEq::eq, "")
    }
}

#[cfg(test)]
mod tests {
    use crate::assert_fails;
    use crate::prelude::*;

    use super::*;

    #[test]
    fn contains_passes_for_array_containing_only_item() {
        assert_that!([5]).contains(5);
    }

    #[test]
    fn contains_passes_for_array_containing_item_later() {
        assert_that!([2, 3, 5]).contains(5);
    }

    #[test]
    fn contains_fails_for_empty_array() {
        assert_fails!(([] as [u32; 0]).contains(5),
            expected it "to contain <5>"
            but it "was <[ ]>");
    }

    #[test]
    fn contains_fails_for_array_containing_one_other_item() {
        assert_fails!(([2] as [u32; 1]).contains(5),
            expected it "to contain <5>"
            but it "was <[ 2 ]>");
    }

    #[test]
    fn contains_fails_for_array_containing_multiple_other_items() {
        assert_fails!(([2, 3] as [u32; 2]).contains(5),
            expected it "to contain <5>"
            but it "was <[ 2, 3 ]>");
    }

    #[test]
    fn does_not_contain_fails_for_empty_array() {
        assert_that!([] as [u32; 0]).does_not_contain(5);
    }

    #[test]
    fn does_not_contain_fails_for_array_containing_one_other_item() {
        assert_that!([2] as [u32; 1]).does_not_contain(5);
    }

    #[test]
    fn does_not_contain_fails_for_array_containing_multiple_other_items() {
        assert_that!([2, 3] as [u32; 2]).does_not_contain(5);
    }

    #[test]
    fn does_not_contain_fails_for_array_containing_only_item() {
        assert_fails!(([5]).does_not_contain(5),
            expected it "not to contain <5>"
            but it "was <[ [5] ]>");
    }

    #[test]
    fn does_not_contain_fails_for_array_containing_item_later() {
        assert_fails!(([2, 3, 5]).does_not_contain(5),
            expected it "not to contain <5>"
            but it "was <[ 2, 3, [5] ]>");
    }

    /// Test-case generator for assertions of the kind "contains_all_of", potentially with different
    /// implementations (such as HashSet/BTreeSet/...).
    ///
    /// # Arguments
    ///
    /// * $assertion: The identifier of the assertion method.
    #[macro_export]
    macro_rules! test_contains_all_of {
        ($assertion:ident) => {
            #[test]
            fn contains_all_of_passes_for_empty_expected_items() {
                assert_that!(Vec::<u32>::new()).$assertion(&[]);
            }

            #[test]
            fn contains_all_of_passes_for_same_slices() {
                assert_that!(&[1, 2, 3]).$assertion(&[1, 2, 3]);
            }

            #[test]
            fn contains_all_of_passes_for_same_slices_in_different_order() {
                assert_that!(&[1, 2, 3]).$assertion(&[3, 2, 1]);
            }

            #[test]
            fn contains_all_of_passes_for_true_sub_multiset() {
                assert_that!(&[1, 2, 3]).$assertion(&[1, 3]);
            }

            #[test]
            fn contains_all_of_fails_for_single_non_contained_item() {
                assert_fails!((&[1, 2, 3]).$assertion(&[4]),
                    expected it "to contain all of <[ 4 ]>"
                    but it "was <[ 1, 2, 3 ]>, which lacks 1 of <4>");
            }

            #[test]
            fn contains_all_of_fails_for_more_often_contained_item() {
                assert_fails!((&[1, 2, 3]).$assertion(&[1, 2, 2, 2]),
                    expected it "to contain all of <[ 1, 2, 2, 2 ]>"
                    but it "was <[ 1, 2, 3 ]>, which lacks 2 of <2>");
            }

            #[test]
            fn contains_all_of_fails_for_multiple_non_contained_items() {
                assert_that!(|| assert_that!(&[1, 2, 3]).$assertion(&[1, 1, 4, 4, 5]))
                    .panics_with_message_matching(|msg|
                        msg.contains("to contain all of <[ 1, 1, 4, 4, 5 ]>") &&
                        msg.contains("was <[ 1, 2, 3 ]>, which lacks") &&
                        msg.contains("1 of <1>") &&
                        msg.contains("2 of <4>") &&
                        msg.contains("1 of <5>"));
            }
        }
    }

    test_contains_all_of!(contains_all_of);

    /// Test-case generator for assertions of the kind "contains_none_of", potentially with
    /// different implementations (such as HashSet/BTreeSet/...).
    ///
    /// # Arguments
    ///
    /// * $assertion: The identifier of the assertion method.
    #[macro_export]
    macro_rules! test_contains_none_of {
        ($assertion:ident) => {
            #[test]
            fn contains_none_of_passes_for_empty_expected_items() {
                assert_that!(&["apple"]).$assertion(&[] as &[&str]);
            }

            #[test]
            fn contains_none_of_passes_for_single_non_contained_item() {
                assert_that!(&["apple", "banana"]).$assertion(&["cherry"]);
            }

            #[test]
            fn contains_none_of_passes_for_multiple_non_contained_items() {
                assert_that!(&["apple", "banana"]).$assertion(&["cherry", "dragon fruit"]);
            }

            #[test]
            fn contains_none_of_fails_for_single_contained_element() {
                assert_fails!((&["apple", "banana", "cherry"]).$assertion(&["banana"]),
                    expected it "not to contain any of <[ \"banana\" ]>"
                    but it "was <[ \"apple\", [\"banana\"], \"cherry\" ]>");
            }

            #[test]
            fn contains_none_of_fails_for_mixed_elements() {
                assert_fails!((&["apple", "banana", "cherry"])
                    .$assertion(&["dragon fruit", "apple"]),
                    expected it "not to contain any of <[ \"dragon fruit\", \"apple\" ]>"
                    but it "was <[ [\"apple\"], \"banana\", \"cherry\" ]>");
            }
        }
    }

    test_contains_none_of!(contains_none_of);

    /// Test-case generator for assertions of the kind "contains_exactly_in_any_order", potentially
    /// with different implementations (such as HashSet/BTreeSet/...).
    ///
    /// # Arguments
    ///
    /// * $assertion: The identifier of the assertion method.
    #[macro_export]
    macro_rules! test_contains_exactly_in_any_order {
        ($assertion:ident) => {
            #[test]
            fn contains_exactly_in_any_order_passes_for_empty_slices() {
                assert_that!(&[] as &[&str]).$assertion(&[] as &[&str]);
            }

            #[test]
            fn contains_exactly_in_any_order_passes_for_slices_with_single_element() {
                assert_that!(&[1]).$assertion(&[1]);
            }

            #[test]
            fn contains_exactly_in_any_order_passes_for_same_elements_in_different_order() {
                assert_that!(&[1, 2, 3]).$assertion(&[2, 3, 1]);
            }

            #[test]
            fn contains_exactly_in_any_order_passes_for_correct_multiplicity() {
                assert_that!(&[2, 1, 2]).$assertion(&[1, 2, 2]);
            }

            #[test]
            fn contains_exactly_in_any_order_fails_for_missing_element() {
                assert_fails!((&[1]).$assertion(&[1, 2]),
                    expected it "to contain exactly in any order <[ 1, 2 ]>"
                    but it "was <[ 1 ]>, which lacks 1 of <2>");
            }

            #[test]
            fn contains_exactly_in_any_order_fails_for_superfluous_element() {
                assert_fails!((&[1, 2]).$assertion(&[2]),
                    expected it "to contain exactly in any order <[ 2 ]>"
                    but it "was <[ 1, 2 ]>, which additionally has 1 of <1>");
            }

            #[test]
            fn contains_exactly_in_any_order_fails_for_missing_and_superfluous_elements() {
                assert_fails!((&[2, 1, 2]).$assertion(&[1, 3, 3]),
                    expected it "to contain exactly in any order <[ 1, 3, 3 ]>"
                    but it "was <[ 2, 1, 2 ]>, which lacks 2 of <3> and additionally has 2 of <2>");
            }

            #[test]
            fn contains_exactly_in_any_order_fails_for_too_few_equal_elements() {
                assert_fails!((&[1, 2]).$assertion(&[1, 2, 2]),
                    expected it "to contain exactly in any order <[ 1, 2, 2 ]>"
                    but it "was <[ 1, 2 ]>, which lacks 1 of <2>");
            }

            #[test]
            fn contains_exactly_in_any_order_fails_for_too_many_equal_elements() {
                assert_fails!((&[1, 1, 1, 2]).$assertion(&[1, 2]),
                    expected it "to contain exactly in any order <[ 1, 2 ]>"
                    but it "was <[ 1, 1, 1, 2 ]>, which additionally has 2 of <1>");
            }
        }
    }

    test_contains_exactly_in_any_order!(contains_exactly_in_any_order);

    #[test]
    fn contains_contiguous_subsequence_passes_for_empty_subsequence() {
        assert_that!(&[1]).contains_contiguous_subsequence(&[]);
    }

    #[test]
    fn contains_contiguous_subsequence_passes_for_entire_collection() {
        assert_that!(&[1, 2, 3]).contains_contiguous_subsequence(&[1, 2, 3]);
    }

    #[test]
    fn contains_contiguous_subsequence_passes_for_prefix() {
        assert_that!(&[1, 2, 3]).contains_contiguous_subsequence(&[1, 2]);
    }

    #[test]
    fn contains_contiguous_subsequence_passes_for_suffix() {
        assert_that!(&[1, 2, 3]).contains_contiguous_subsequence(&[2, 3]);
    }

    #[test]
    fn contains_contiguous_subsequence_passes_for_inner_subsequence() {
        assert_that!(&[1, 2, 3, 4, 5]).contains_contiguous_subsequence(&[2, 3, 4]);
    }

    #[test]
    fn contains_contiguous_subsequence_passes_for_overlapping_occurrences() {
        assert_that!(&[1, 2, 1, 2, 1]).contains_contiguous_subsequence(&[1, 2, 1]);
    }

    #[test]
    fn contains_contiguous_subsequence_fails_for_empty_test_sequence() {
        assert_fails!(([] as [i32; 0]).contains_contiguous_subsequence(&[4]),
            expected it "to contain the contiguous subsequence <[ 4 ]>"
            but it "was <[ ]>");
    }

    #[test]
    fn contains_contiguous_subsequence_fails_for_non_contained_element() {
        assert_fails!((&[1, 2, 3]).contains_contiguous_subsequence(&[4]),
            expected it "to contain the contiguous subsequence <[ 4 ]>"
            but it "was <[ 1, 2, 3 ]>");
    }

    #[test]
    fn contains_contiguous_subsequence_fails_for_almost_completely_contained_subsequence() {
        assert_fails!((&[1, 2, 1, 2]).contains_contiguous_subsequence(&[2, 1, 1]),
            expected it "to contain the contiguous subsequence <[ 2, 1, 1 ]>"
            but it "was <[ 1, 2, 1, 2 ]>");
    }

    #[test]
    fn contains_contiguous_subsequence_fails_for_subsequence_that_is_not_subsequence() {
        assert_fails!((&[1, 2, 3]).contains_contiguous_subsequence(&[1, 3]),
            expected it "to contain the contiguous subsequence <[ 1, 3 ]>"
            but it "was <[ 1, 2, 3 ]>");
    }

    #[test]
    fn does_not_contain_contiguous_subsequence_fails_for_empty_subsequence() {
        assert_fails!((&[1]).does_not_contain_contiguous_subsequence(&[]),
            expected it "not to contain the contiguous subsequence <[ ]>"
            but it "was <[ [] 1 ]>");
    }

    #[test]
    fn does_not_contain_contiguous_subsequence_fails_for_entire_collection() {
        assert_fails!((&[1, 2, 3]).does_not_contain_contiguous_subsequence(&[1, 2, 3]),
            expected it "not to contain the contiguous subsequence <[ 1, 2, 3 ]>"
            but it "was <[ [1, 2, 3] ]>");
    }

    #[test]
    fn does_not_contain_contiguous_subsequence_fails_for_prefix() {
        assert_fails!((&[1, 2, 3]).does_not_contain_contiguous_subsequence(&[1, 2]),
            expected it "not to contain the contiguous subsequence <[ 1, 2 ]>"
            but it "was <[ [1, 2], 3 ]>");
    }

    #[test]
    fn does_not_contain_contiguous_subsequence_fails_for_suffix() {
        assert_fails!((&[1, 2, 3]).does_not_contain_contiguous_subsequence(&[2, 3]),
            expected it "not to contain the contiguous subsequence <[ 2, 3 ]>"
            but it "was <[ 1, [2, 3] ]>");
    }

    #[test]
    fn does_not_contain_contiguous_subsequence_fails_for_inner_subsequence() {
        assert_fails!((&[1, 2, 3, 4, 5]).does_not_contain_contiguous_subsequence(&[2, 3, 4]),
            expected it "not to contain the contiguous subsequence <[ 2, 3, 4 ]>"
            but it "was <[ 1, [2, 3, 4], 5 ]>");
    }

    #[test]
    fn does_not_contain_contiguous_subsequence_fails_for_overlapping_occurrences() {
        assert_fails!((&[1, 2, 1, 2, 1]).does_not_contain_contiguous_subsequence(&[1, 2, 1]),
            expected it "not to contain the contiguous subsequence <[ 1, 2, 1 ]>"
            but it "was <[ [1, 2, 1], 2, 1 ]>");
    }

    #[test]
    fn does_not_contain_contiguous_subsequence_passes_for_non_contained_element() {
        assert_that!(&[1, 2, 3]).does_not_contain_contiguous_subsequence(&[4]);
    }

    #[test]
    fn does_not_contain_contiguous_subsequence_passes_for_almost_completely_contained_subsequence()
    {
        assert_that!(&[1, 2, 1, 2]).does_not_contain_contiguous_subsequence(&[2, 1, 1]);
    }

    #[test]
    fn does_not_contain_contiguous_subsequence_passes_for_subsequence_that_is_not_subsequence() {
        assert_that!(&[1, 2, 3]).does_not_contain_contiguous_subsequence(&[1, 3]);
    }

    #[test]
    fn does_not_contain_contiguous_subsequence_passes_for_empty_test_sequence() {
        assert_that!([] as [i32; 0]).does_not_contain_contiguous_subsequence(&[4]);
    }

    #[test]
    fn contains_subsequence_passes_for_empty_subsequence() {
        assert_that!(&[1]).contains_subsequence(&[]);
    }

    #[test]
    fn contains_subsequence_passes_for_entire_collection() {
        assert_that!(&[1, 2, 3]).contains_subsequence(&[1, 2, 3]);
    }

    #[test]
    fn contains_subsequence_passes_for_contiguous_subsequence() {
        assert_that!(&[1, 2, 3, 4, 5]).contains_subsequence(&[2, 3, 4]);
    }

    #[test]
    fn contains_subsequence_passes_for_non_contiguous_subsequence() {
        assert_that!(&[1, 2, 3, 4, 5]).contains_subsequence(&[1, 3, 5]);
    }

    #[test]
    fn contains_subsequence_fails_for_non_contained_element() {
        assert_fails!((&[1, 2, 3]).contains_subsequence(&[4]),
            expected it "to contain the subsequence <[ 4 ]>"
            but it "was <[ 1, 2, 3 ]>");
    }

    #[test]
    fn contains_subsequence_fails_for_subset_in_wrong_order() {
        assert_fails!((&[1, 2, 3, 4, 5]).contains_subsequence(&[1, 3, 2]),
            expected it "to contain the subsequence <[ 1, 3, 2 ]>"
            but it "was <[ 1, 2, 3, 4, 5 ]>");
    }

    #[test]
    fn does_not_contain_subsequence_passes_for_non_contained_element() {
        assert_that!(&[1, 2, 3]).does_not_contain_subsequence(&[4]);
    }

    #[test]
    fn does_not_contain_subsequence_passes_for_subset_in_wrong_order() {
        assert_that!(&[1, 2, 3, 4, 5]).does_not_contain_subsequence(&[1, 3, 2]);
    }

    #[test]
    fn does_not_contain_subsequence_fails_for_empty_subsequence() {
        assert_fails!((&[1]).does_not_contain_subsequence(&[]),
            expected it "not to contain the subsequence <[ ]>"
            but it "was <[ [] 1 ]>");
    }

    #[test]
    fn does_not_contain_subsequence_fails_for_entire_collection() {
        assert_fails!((&[1, 2, 3]).does_not_contain_subsequence(&[1, 2, 3]),
            expected it "not to contain the subsequence <[ 1, 2, 3 ]>"
            but it "was <[ [1, 2, 3] ]>");
    }

    #[test]
    fn does_not_contain_subsequence_fails_for_contiguous_subsequence() {
        assert_fails!((&[1, 2, 3, 4, 5]).does_not_contain_subsequence(&[2, 3, 4]),
            expected it "not to contain the subsequence <[ 2, 3, 4 ]>"
            but it "was <[ 1, [2, 3, 4], 5 ]>");
    }

    #[test]
    fn does_not_contain_subsequence_fails_for_non_contiguous_subsequence() {
        assert_fails!((&[1, 2, 3, 4, 5]).does_not_contain_subsequence(&[1, 3, 5]),
            expected it "not to contain the subsequence <[ 1, 3, 5 ]>"
            but it "was <[ [1], 2, [3], 4, [5] ]>");
    }

    #[test]
    fn starts_with_passes_for_empty_prefix() {
        assert_that!(&[1]).starts_with(&[]);
    }

    #[test]
    fn starts_with_passes_for_entire_collection() {
        assert_that!(&[1, 2, 3]).starts_with(&[1, 2, 3]);
    }

    #[test]
    fn starts_with_passes_for_proper_prefix() {
        assert_that!(&[1, 2, 3]).starts_with(&[1, 2]);
    }

    #[test]
    fn starts_with_fails_for_single_element_not_contained_in_collection() {
        assert_fails!((&[1, 2, 3]).starts_with(&[4]),
            expected it "to start with the prefix <[ 4 ]>"
            but it "was <[ 1, 2, 3 ]>");
    }

    #[test]
    fn starts_with_fails_for_non_prefix_contiguous_subsequence() {
        assert_fails!((&[1, 2, 3]).starts_with(&[2, 3]),
            expected it "to start with the prefix <[ 2, 3 ]>"
            but it "was <[ 1, 2, 3 ]>");
    }

    #[test]
    fn starts_with_fails_for_initially_correct_but_later_incorrect_prefix() {
        assert_fails!((&[1, 2, 3]).starts_with(&[1, 3]),
            expected it "to start with the prefix <[ 1, 3 ]>"
            but it "was <[ 1, 2, 3 ]>");
    }

    #[test]
    fn starts_with_fails_for_prefix_longer_than_collection() {
        assert_fails!((&[1, 2, 3]).starts_with(&[1, 2, 3, 4]),
            expected it "to start with the prefix <[ 1, 2, 3, 4 ]>"
            but it "was <[ 1, 2, 3 ]>");
    }

    #[test]
    fn does_not_start_with_passes_for_single_element_not_contained_in_collection() {
        assert_that!(&[1, 2, 3]).does_not_start_with(&[4]);
    }

    #[test]
    fn does_not_start_with_passes_for_non_prefix_contiguous_subsequence() {
        assert_that!(&[1, 2, 3]).does_not_start_with(&[2, 3]);
    }

    #[test]
    fn does_not_start_with_passes_for_initially_correct_but_later_incorrect_prefix() {
        assert_that!(&[1, 2, 3]).does_not_start_with(&[1, 3]);
    }

    #[test]
    fn does_not_start_with_passes_for_prefix_longer_than_collection() {
        assert_that!(&[1, 2, 3]).does_not_start_with(&[1, 2, 3, 4]);
    }

    #[test]
    fn does_not_start_with_fails_for_empty_prefix() {
        assert_fails!((&[1]).does_not_start_with(&[]),
            expected it "not to start with the prefix <[ ]>"
            but it "was <[ [] 1 ]>");
    }

    #[test]
    fn does_not_start_with_fails_for_entire_collection() {
        assert_fails!((&[1, 2, 3]).does_not_start_with(&[1, 2, 3]),
            expected it "not to start with the prefix <[ 1, 2, 3 ]>"
            but it "was <[ [1, 2, 3] ]>");
    }

    #[test]
    fn does_not_start_with_fails_for_proper_prefix() {
        assert_fails!((&[1, 2, 3]).does_not_start_with(&[1, 2]),
            expected it "not to start with the prefix <[ 1, 2 ]>"
            but it "was <[ [1, 2], 3 ]>");
    }

    #[test]
    fn ends_with_passes_for_empty_suffix() {
        assert_that!(&[1]).ends_with(&[]);
    }

    #[test]
    fn ends_with_passes_for_entire_collection() {
        assert_that!(&[1, 2, 3]).ends_with(&[1, 2, 3]);
    }

    #[test]
    fn ends_with_passes_for_proper_suffix() {
        assert_that!(&[1, 2, 3]).ends_with(&[2, 3]);
    }

    #[test]
    fn ends_with_fails_for_single_element_not_contained_in_collection() {
        assert_fails!((&[1, 2, 3]).ends_with(&[4]),
            expected it "to end with the suffix <[ 4 ]>"
            but it "was <[ 1, 2, 3 ]>");
    }

    #[test]
    fn ends_with_fails_for_non_suffix_contiguous_subsequence() {
        assert_fails!((&[1, 2, 3]).ends_with(&[1, 2]),
            expected it "to end with the suffix <[ 1, 2 ]>"
            but it "was <[ 1, 2, 3 ]>");
    }

    #[test]
    fn ends_with_fails_for_initially_correct_but_later_incorrect_suffix() {
        assert_fails!((&[1, 2, 3]).ends_with(&[2, 2]),
            expected it "to end with the suffix <[ 2, 2 ]>"
            but it "was <[ 1, 2, 3 ]>");
    }

    #[test]
    fn ends_with_fails_for_suffix_longer_than_collection() {
        assert_fails!((&[1, 2, 3]).ends_with(&[1, 2, 3, 4]),
            expected it "to end with the suffix <[ 1, 2, 3, 4 ]>"
            but it "was <[ 1, 2, 3 ]>");
    }

    #[test]
    fn does_not_end_with_passes_for_single_element_not_contained_in_collection() {
        assert_that!(&[1, 2, 3]).does_not_end_with(&[4]);
    }

    #[test]
    fn does_not_end_with_passes_for_non_suffix_contiguous_subsequence() {
        assert_that!(&[1, 2, 3]).does_not_end_with(&[1, 2]);
    }

    #[test]
    fn does_not_end_with_passes_for_initially_correct_but_later_incorrect_suffix() {
        assert_that!(&[1, 2, 3]).does_not_end_with(&[2, 2]);
    }

    #[test]
    fn does_not_end_with_passes_for_suffix_longer_than_collection() {
        assert_that!(&[1, 2, 3]).does_not_end_with(&[1, 2, 3, 4]);
    }

    #[test]
    fn does_not_end_with_fails_for_empty_suffix() {
        assert_fails!((&[1]).does_not_end_with(&[]),
            expected it "not to end with the suffix <[ ]>"
            but it "was <[ 1 [] ]>");
    }

    #[test]
    fn does_not_end_with_fails_for_entire_collection() {
        assert_fails!((&[1, 2, 3]).does_not_end_with(&[1, 2, 3]),
            expected it "not to end with the suffix <[ 1, 2, 3 ]>"
            but it "was <[ [1, 2, 3] ]>");
    }

    #[test]
    fn does_not_end_with_fails_for_proper_suffix() {
        assert_fails!((&[1, 2, 3]).does_not_end_with(&[2, 3]),
            expected it "not to end with the suffix <[ 2, 3 ]>"
            but it "was <[ 1, [2, 3] ]>");
    }

    #[test]
    fn contains_exactly_in_given_order_passes_for_empty_collection() {
        assert_that!(&[] as &[String]).contains_exactly_in_given_order(&[]);
    }

    #[test]
    fn contains_exactly_in_given_order_passes_for_singleton() {
        assert_that!(&["hello"]).contains_exactly_in_given_order(&["hello"]);
    }

    #[test]
    fn contains_exactly_in_given_order_passes_for_multi_element_collection() {
        assert_that!(&["hello", "world", "!"])
            .contains_exactly_in_given_order(&["hello", "world", "!"]);
    }

    #[test]
    fn contains_exactly_in_given_order_fails_for_collection_with_extra_element() {
        assert_fails!((&["hello", "world", "!"])
            .contains_exactly_in_given_order(&["hello", "world"]),
            expected it "to contain exactly in the given order <[ \"hello\", \"world\" ]>"
            but it "was <[ \"hello\", \"world\", [\"!\"] ]>");
    }

    #[test]
    fn contains_exactly_in_given_order_fails_for_collection_with_error() {
        assert_fails!((&["hello", "world", "!"])
            .contains_exactly_in_given_order(&["hello", "bob", "!"]),
            expected it "to contain exactly in the given order <[ \"hello\", \"bob\", \"!\" ]>"
            but it "was <[ \"hello\", [\"world\"], \"!\" ]>");
    }

    #[test]
    fn contains_exactly_in_given_order_fails_for_collection_missing_last_element() {
        assert_fails!((&["hello", "world"])
            .contains_exactly_in_given_order(&["hello", "world", "!"]),
            expected it "to contain exactly in the given order <[ \"hello\", \"world\", \"!\" ]>"
            but it "was <[ \"hello\", \"world\" [] ]>");
    }

    #[test]
    fn contains_exactly_in_given_order_fails_for_empty_collection_compared_to_singleton() {
        assert_fails!((&[] as &[u32]).contains_exactly_in_given_order(&[0]),
            expected it "to contain exactly in the given order <[ 0 ]>"
            but it "was <[ [] ]>");
    }

    #[test]
    fn contains_exactly_in_given_order_fails_for_singleton_compared_to_empty_collection() {
        assert_fails!((&[0]).contains_exactly_in_given_order(&[]),
            expected it "to contain exactly in the given order <[ ]>"
            but it "was <[ [0] ]>");
    }
}
