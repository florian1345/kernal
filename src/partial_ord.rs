//! Contains assertions for values which implement [PartialOrd]. See [PartialOrdAssertions] for more
//! details.

use std::borrow::Borrow;
use std::cmp::Ordering;
use std::fmt::Debug;

use crate::{AssertThat, Failure};

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with an
/// argument that implements the [PartialOrd] trait.
///
/// Examples:
///
/// ```
/// use kernal::prelude::*;
///
/// assert_that!(1.0)
///     .is_less_than(1.5)
///     .is_greater_than_or_equal_to(1.0)
///     .is_not_comparable_to(f32::NAN);
/// ```
pub trait PartialOrdAssertions<T> {
    /// Asserts that the tested value is less than the given `other` value according to
    /// [PartialOrd::partial_cmp], i.e. [Ordering::Less].
    fn is_less_than<E: Borrow<T>>(self, other: E) -> Self;

    /// Asserts that the tested value is less than or equal to the given `other` value according to
    /// [PartialOrd::partial_cmp], i.e. [Ordering::Less] or [Ordering::Equal].
    fn is_less_than_or_equal_to<E: Borrow<T>>(self, other: E) -> Self;

    /// Asserts that the tested value is greater than the given `other` value according to
    /// [PartialOrd::partial_cmp], i.e. [Ordering::Greater].
    fn is_greater_than<E: Borrow<T>>(self, other: E) -> Self;

    /// Asserts that the tested value is greater than or equal to the given `other` value according
    /// to [PartialOrd::partial_cmp], i.e. [Ordering::Greater] or [Ordering::Equal].
    fn is_greater_than_or_equal_to<E: Borrow<T>>(self, other: E) -> Self;

    /// Asserts that the tested value is comparable to the given `other` value according to
    /// [PartialOrd::partial_cmp], i.e. it returns a [Some] variant.
    fn is_comparable_to<E: Borrow<T>>(self, other: E) -> Self;

    /// Asserts that the tested value is not comparable to the given `other` value according to
    /// [PartialOrd::partial_cmp], i.e. it returns [None].
    fn is_not_comparable_to<E: Borrow<T>>(self, other: E) -> Self;
}

fn describe_ordering(ordering: Option<Ordering>) -> &'static str {
    match ordering {
        Some(Ordering::Less) => "less",
        Some(Ordering::Equal) => "equal",
        Some(Ordering::Greater) => "greater",
        None => "not comparable",
    }
}

fn assert_ordering_of_data_compared_to_other_to_be_in_list<T, E>(
    assert_that: AssertThat<T>,
    other: E,
    accepted_orderings: &[Option<Ordering>],
    description: &str,
) -> AssertThat<T>
where
    T: Debug + PartialOrd,
    E: Borrow<T>,
{
    let other = other.borrow();
    let ordering = assert_that.data.partial_cmp(other);

    if !accepted_orderings.contains(&ordering) {
        let ordering_description = describe_ordering(ordering);

        Failure::new(&assert_that)
            .expected_it(format!("to be {} <{:?}>", description, other))
            .but_it(format!(
                "was <{:?}>, which is {}",
                &assert_that.data, ordering_description
            ))
            .fail();
    }

    assert_that
}

impl<T: Debug + PartialOrd> PartialOrdAssertions<T> for AssertThat<T> {
    fn is_less_than<E: Borrow<T>>(self, other: E) -> Self {
        assert_ordering_of_data_compared_to_other_to_be_in_list(
            self,
            other,
            &[Some(Ordering::Less)],
            "less than",
        )
    }

    fn is_less_than_or_equal_to<E: Borrow<T>>(self, other: E) -> Self {
        assert_ordering_of_data_compared_to_other_to_be_in_list(
            self,
            other,
            &[Some(Ordering::Less), Some(Ordering::Equal)],
            "less than or equal to",
        )
    }

    fn is_greater_than<E: Borrow<T>>(self, other: E) -> Self {
        assert_ordering_of_data_compared_to_other_to_be_in_list(
            self,
            other,
            &[Some(Ordering::Greater)],
            "greater than",
        )
    }

    fn is_greater_than_or_equal_to<E: Borrow<T>>(self, other: E) -> Self {
        assert_ordering_of_data_compared_to_other_to_be_in_list(
            self,
            other,
            &[Some(Ordering::Greater), Some(Ordering::Equal)],
            "greater than or equal to",
        )
    }

    fn is_comparable_to<E: Borrow<T>>(self, other: E) -> Self {
        assert_ordering_of_data_compared_to_other_to_be_in_list(
            self,
            other,
            &[
                Some(Ordering::Greater),
                Some(Ordering::Equal),
                Some(Ordering::Less),
            ],
            "comparable to",
        )
    }

    fn is_not_comparable_to<E: Borrow<T>>(self, other: E) -> Self {
        assert_ordering_of_data_compared_to_other_to_be_in_list(
            self,
            other,
            &[None],
            "uncomparable to",
        )
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::{assert_fails, assert_that};

    #[test]
    fn is_less_than_passes_for_lower_integer() {
        assert_that!(3).is_less_than(4);
    }

    #[test]
    fn is_less_than_fails_for_equal_integer() {
        assert_fails!((2 + 2).is_less_than(4),
            expected it "to be less than <4>"
            but it "was <4>, which is equal");
    }

    #[test]
    fn is_less_than_fails_for_greater_integer() {
        assert_fails!((2 + 3).is_less_than(4),
            expected it "to be less than <4>"
            but it "was <5>, which is greater");
    }

    #[test]
    fn is_less_than_fails_for_nan() {
        assert_fails!((f32::NAN).is_less_than(1.0),
            expected it "to be less than <1.0>"
            but it "was <NaN>, which is not comparable");
    }

    #[test]
    fn is_less_than_or_equal_to_passes_for_lower_integer() {
        assert_that!(3).is_less_than_or_equal_to(4);
    }

    #[test]
    fn is_less_than_or_equal_to_passes_for_equal_integer() {
        assert_that!(4).is_less_than_or_equal_to(4);
    }

    #[test]
    fn is_less_than_or_equal_to_fails_for_greater_integer() {
        assert_fails!((2 + 3).is_less_than_or_equal_to(4),
            expected it "to be less than or equal to <4>"
            but it "was <5>, which is greater");
    }

    #[test]
    fn is_less_than_or_equal_to_fails_for_nan() {
        assert_fails!((f32::NAN).is_less_than_or_equal_to(1.0),
            expected it "to be less than or equal to <1.0>"
            but it "was <NaN>, which is not comparable");
    }

    #[test]
    fn is_greater_than_passes_for_greater_integer() {
        assert_that!(5).is_greater_than(4);
    }

    #[test]
    fn is_greater_than_fails_for_equal_integer() {
        assert_fails!((2 + 2).is_greater_than(4),
            expected it "to be greater than <4>"
            but it "was <4>, which is equal");
    }

    #[test]
    fn is_greater_than_fails_for_lower_integer() {
        assert_fails!((2 + 1).is_greater_than(4),
            expected it "to be greater than <4>"
            but it "was <3>, which is less");
    }

    #[test]
    fn is_greater_than_fails_for_nan() {
        assert_fails!((f32::NAN).is_greater_than(1.0),
            expected it "to be greater than <1.0>"
            but it "was <NaN>, which is not comparable");
    }

    #[test]
    fn is_greater_than_or_equal_to_passes_for_greater_integer() {
        assert_that!(5).is_greater_than_or_equal_to(4);
    }

    #[test]
    fn is_greater_than_or_equal_to_passes_for_equal_integer() {
        assert_that!(4).is_greater_than_or_equal_to(4);
    }

    #[test]
    fn is_greater_than_or_equal_to_fails_for_lower_integer() {
        assert_fails!((2 + 1).is_greater_than_or_equal_to(4),
            expected it "to be greater than or equal to <4>"
            but it "was <3>, which is less");
    }

    #[test]
    fn is_greater_than_or_equal_to_fails_for_nan() {
        assert_fails!((f32::NAN).is_greater_than_or_equal_to(1.0),
            expected it "to be greater than or equal to <1.0>"
            but it "was <NaN>, which is not comparable");
    }

    #[test]
    fn is_comparable_to_passes_for_lower_float() {
        assert_that!(1.0).is_comparable_to(2.0);
    }

    #[test]
    fn is_comparable_to_passes_for_equal_float() {
        assert_that!(2.0).is_comparable_to(2.0);
    }

    #[test]
    fn is_comparable_to_passes_for_greater_float() {
        assert_that!(3.0).is_comparable_to(2.0);
    }

    #[test]
    fn is_comparable_to_fails_for_nan() {
        assert_fails!((f32::NAN).is_comparable_to(2.0),
            expected it "to be comparable to <2.0>"
            but it "was <NaN>, which is not comparable");
    }

    #[test]
    fn is_not_comparable_to_passes_for_nan() {
        assert_that!(f32::NAN).is_not_comparable_to(2.0);
    }

    #[test]
    fn is_not_comparable_to_fails_for_lower_float() {
        assert_fails!((0.5 + 0.5).is_not_comparable_to(2.0),
            expected it "to be uncomparable to <2.0>"
            but it "was <1.0>, which is less");
    }

    #[test]
    fn is_not_comparable_to_fails_for_equal_float() {
        assert_fails!((0.5 + 1.5).is_not_comparable_to(2.0),
            expected it "to be uncomparable to <2.0>"
            but it "was <2.0>, which is equal");
    }

    #[test]
    fn is_not_comparable_to_fails_for_greater_float() {
        assert_fails!((0.5 + 2.5).is_not_comparable_to(2.0),
            expected it "to be uncomparable to <2.0>"
            but it "was <3.0>, which is greater");
    }
}
