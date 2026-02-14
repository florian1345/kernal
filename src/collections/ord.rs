//! Contains assertions for [Collection]s whose items implement the [Ord] trait in addition to
//! [Debug]. See [CollectionOrdAssertions] for more details.

use std::borrow::Borrow;
use std::fmt::Debug;

use crate::collections::{Collection, CollectionDebug, HighlightedCollectionDebug};
use crate::{AssertThat, Failure};

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with an
/// argument that implements the [Collection] trait and whose [Collection::Item] type implements
/// [Ord] in addition to [Debug].
///
/// Examples:
///
/// ```
/// use kernal::prelude::*;
///
/// assert_that!([3, 1, 4, 1]).has_maximum(4).does_not_have_minimum(0);
/// ```
pub trait CollectionOrdAssertions<C: Collection> {
    /// Asserts that the tested collection contains an item equal to `max` according to [PartialEq]
    /// and that all other items are less than or equal to that value according to [Ord].
    fn has_maximum<M: Borrow<C::Item>>(self, max: M) -> Self;

    /// Asserts that the tested collection does not contain an item equal to `max` according to
    /// [PartialEq] or that some item is greater than that value according to [Ord].
    fn does_not_have_maximum<M: Borrow<C::Item>>(self, max: M) -> Self;

    /// Asserts that the tested collection contains an item equal to `min` according to [PartialEq]
    /// and that all other items are greater than or equal to that value according to [Ord].
    fn has_minimum<M: Borrow<C::Item>>(self, min: M) -> Self;

    /// Asserts that the tested collection does not contain an item equal to `min` according to
    /// [PartialEq] or that some item is less than that value according to [Ord].
    fn does_not_have_minimum<M: Borrow<C::Item>>(self, min: M) -> Self;
}

fn verify_has_extreme<C, M>(
    assert_that: &AssertThat<C>,
    expected_extreme: M,
    actual_extreme: Option<&C::Item>,
    extreme_name: &str,
) where
    C: Collection,
    C::Item: Debug + Ord,
    M: Borrow<C::Item>,
{
    let expected_extreme = expected_extreme.borrow();
    let failure = Failure::new(assert_that).expected_it(format!(
        "to have the {} <{:?}>",
        extreme_name, expected_extreme
    ));

    match actual_extreme {
        Some(extreme) if extreme == expected_extreme => {},
        Some(extreme) => {
            let collection_debug = CollectionDebug {
                collection: &assert_that.data,
            };

            failure
                .but_it(format!(
                    "was <{:?}>, which has the {} <{:?}>",
                    collection_debug, extreme_name, extreme
                ))
                .fail()
        },
        None => failure.but_it("was empty").fail(),
    }
}

fn verify_does_not_have_extreme<C, M>(
    assert_that: &AssertThat<C>,
    unexpected_extreme: M,
    actual_extreme: Option<&C::Item>,
    extreme_name: &str,
) where
    C: Collection,
    C::Item: Debug + Ord,
    M: Borrow<C::Item>,
{
    let unexpected_extreme = unexpected_extreme.borrow();

    if actual_extreme == Some(unexpected_extreme) {
        let actual_extreme = actual_extreme.unwrap();
        let actual_extreme_index = assert_that
            .data
            .iterator()
            .enumerate()
            .find(|&(_, item)| item == actual_extreme)
            .map(|(index, _)| index)
            .unwrap();
        let highlighted_collection_debug =
            HighlightedCollectionDebug::with_single_highlighted_element(
                &assert_that.data,
                actual_extreme_index,
            );

        Failure::new(assert_that)
            .expected_it(format!(
                "not to have the {} <{:?}>",
                extreme_name, unexpected_extreme
            ))
            .but_it(format!("was <{:?}>", highlighted_collection_debug))
            .fail()
    }
}

impl<C> CollectionOrdAssertions<C> for AssertThat<C>
where
    C: Collection,
    C::Item: Debug + Ord,
{
    fn has_maximum<M: Borrow<C::Item>>(self, max: M) -> Self {
        verify_has_extreme(&self, max, self.data.iterator().max(), "maximum");

        self
    }

    fn does_not_have_maximum<M: Borrow<C::Item>>(self, max: M) -> Self {
        verify_does_not_have_extreme(&self, max, self.data.iterator().max(), "maximum");

        self
    }

    fn has_minimum<M: Borrow<C::Item>>(self, min: M) -> Self {
        verify_has_extreme(&self, min, self.data.iterator().min(), "minimum");

        self
    }

    fn does_not_have_minimum<M: Borrow<C::Item>>(self, min: M) -> Self {
        verify_does_not_have_extreme(&self, min, self.data.iterator().min(), "minimum");

        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{assert_fails, assert_that};

    #[test]
    fn has_maximum_passes_for_correct_maximum() {
        assert_that!(&[5, 1, 6, 2]).has_maximum(6);
    }

    #[test]
    fn has_maximum_fails_for_empty_collection() {
        assert_fails!((&[] as &[i32]).has_maximum(0),
            expected it "to have the maximum <0>"
            but it "was empty");
    }

    #[test]
    fn has_maximum_fails_for_lower_maximum() {
        assert_fails!((&[3, 1, 4, 2]).has_maximum(5),
            expected it "to have the maximum <5>"
            but it "was <[ 3, 1, 4, 2 ]>, which has the maximum <4>");
    }

    #[test]
    fn has_maximum_fails_for_higher_maximum() {
        assert_fails!((&[5, 7, 4, 1]).has_maximum(5),
            expected it "to have the maximum <5>"
            but it "was <[ 5, 7, 4, 1 ]>, which has the maximum <7>");
    }

    #[test]
    fn does_not_have_maximum_passes_for_empty_collection() {
        assert_that!(&[] as &[i32]).does_not_have_maximum(0);
    }

    #[test]
    fn does_not_have_maximum_passes_for_lower_maximum() {
        assert_that!(&[3, 1, 4, 2]).does_not_have_maximum(5);
    }

    #[test]
    fn does_not_have_maximum_passes_for_higher_maximum() {
        assert_that!(&[5, 7, 4, 1]).does_not_have_maximum(5);
    }

    #[test]
    fn does_not_have_maximum_fails_for_correct_maximum() {
        assert_fails!((&[5, 1, 6, 2]).does_not_have_maximum(6),
            expected it "not to have the maximum <6>"
            but it "was <[ 5, 1, [6], 2 ]>");
    }

    #[test]
    fn has_minimum_passes_for_correct_minimum() {
        assert_that!(&[5, 1, 6, 2]).has_minimum(1);
    }

    #[test]
    fn has_minimum_fails_for_empty_collection() {
        assert_fails!((&[] as &[i32]).has_minimum(0),
            expected it "to have the minimum <0>"
            but it "was empty");
    }

    #[test]
    fn has_minimum_fails_for_higher_minimum() {
        assert_fails!((&[3, 1, 4, 2]).has_minimum(0),
            expected it "to have the minimum <0>"
            but it "was <[ 3, 1, 4, 2 ]>, which has the minimum <1>");
    }

    #[test]
    fn has_minimum_fails_for_lower_minimum() {
        assert_fails!((&[5, 7, 4, 1]).has_minimum(4),
            expected it "to have the minimum <4>"
            but it "was <[ 5, 7, 4, 1 ]>, which has the minimum <1>");
    }

    #[test]
    fn does_not_have_minimum_passes_for_empty_collection() {
        assert_that!(&[] as &[i32]).does_not_have_minimum(0);
    }

    #[test]
    fn does_not_have_minimum_passes_for_higher_minimum() {
        assert_that!(&[3, 1, 4, 2]).does_not_have_minimum(0);
    }

    #[test]
    fn does_not_have_minimum_passes_for_lower_minimum() {
        assert_that!(&[5, 7, 4, 1]).does_not_have_minimum(4);
    }

    #[test]
    fn does_not_have_minimum_fails_for_correct_minimum() {
        assert_fails!((&[5, 1, 6, 2]).does_not_have_minimum(1),
            expected it "not to have the minimum <1>"
            but it "was <[ 5, [1], 6, 2 ]>");
    }
}
