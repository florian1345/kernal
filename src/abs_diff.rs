//! Contains assertions for values whose distance to each other can be measured, to check whether
//! values are close. Such types are grouped by the [AbsDiff] trait. See
//! [AbsDiffPartialOrdAssertions] for more details.

use std::borrow::Borrow;
use std::cmp::Ordering;
use std::fmt::Debug;

use crate::{AssertThat, Failure};

/// A trait for all types supporting the computation of an absolute difference between two
/// instances, i.e. the "distance" between the two values. This is implemented on all primitive
/// number types of the standard library. Used to allow assertions defined by
/// [AbsDiffPartialOrdAssertions].
pub trait AbsDiff {

    /// The type returned by the absolute difference operation.
    type ReturnType;

    /// Computes the absolute difference between this and the given `other` intance, i.e. the
    /// "distance" between the two values.
    fn abs_diff(&self, other: &Self) -> Self::ReturnType;
}

macro_rules! impl_abs_diff {
    ($type:ty, $return_type:ty) => {
        impl AbsDiff for $type {

            type ReturnType = $return_type;

            fn abs_diff(&self, other: &$type) -> $return_type {
                <$type>::abs_diff(*self, *other)
            }
        }
    }
}

impl_abs_diff!(u8, u8);
impl_abs_diff!(u16, u16);
impl_abs_diff!(u32, u32);
impl_abs_diff!(u64, u64);
impl_abs_diff!(u128, u128);
impl_abs_diff!(usize, usize);
impl_abs_diff!(i8, u8);
impl_abs_diff!(i16, u16);
impl_abs_diff!(i32, u32);
impl_abs_diff!(i64, u64);
impl_abs_diff!(i128, u128);
impl_abs_diff!(isize, usize);

impl AbsDiff for f32 {

    type ReturnType = f32;

    fn abs_diff(&self, other: &f32) -> f32 {
        (*self - *other).abs()
    }
}

impl AbsDiff for f64 {

    type ReturnType = f64;

    fn abs_diff(&self, other: &f64) -> f64 {
        (*self - *other).abs()
    }
}

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with arguments
/// that support the computation of absolute differences (by the [AbsDiff] trait) and implement the
/// [PartialOrd] trait.
///
/// Examples:
///
/// ```
/// use kernal::prelude::*;
///
/// assert_that!(0.5)
///     .is_close_to(0.45, 0.1)
///     .is_not_close_to(0.3, 0.1);
/// ```
pub trait AbsDiffPartialOrdAssertions<T: AbsDiff> {

    /// Asserts that the tested value is within `offset` of the given `expected` value. That is,
    /// the difference between the tested value and `expected` must be less than or equal to
    /// `offset`.
    fn is_close_to<E, O>(self, expected: E, offset: O) -> Self
    where
        E: Borrow<T>,
        O: Borrow<T::ReturnType>;

    /// Asserts that the tested value is not within `offset` of the given `expected` value. That
    /// is, the difference between the tested value and `expected` must not be less than or equal
    /// to `offset`. Note that this may not be equivalent to stating that the difference must be
    /// greater than `offset`, as this test will pass if the two values are uncomparable.
    fn is_not_close_to<E, O>(self, expected: E, offset: O) -> Self
    where
        E: Borrow<T>,
        O: Borrow<T::ReturnType>;
}

impl<T> AbsDiffPartialOrdAssertions<T> for AssertThat<T>
where
    T: AbsDiff + Debug,
    T::ReturnType: Debug + PartialOrd
{
    fn is_close_to<E, O>(self, expected: E, offset: O) -> Self
    where
        E: Borrow<T>,
        O: Borrow<T::ReturnType>
    {
        let expected = expected.borrow();
        let offset = offset.borrow();
        let abs_diff = self.data.abs_diff(expected);

        if matches!(abs_diff.partial_cmp(offset), None | Some(Ordering::Greater)) {
            Failure::new(&self)
                .expected_it(format!("to be within <{:?}> of <{:?}>", offset, expected))
                .but_it(format!("was <{:?}>, which is outside that range", &self.data))
                .fail();
        }

        self
    }

    fn is_not_close_to<E, O>(self, expected: E, offset: O) -> Self
    where
        E: Borrow<T>,
        O: Borrow<T::ReturnType>
    {
        let expected = expected.borrow();
        let offset = offset.borrow();
        let abs_diff = self.data.abs_diff(expected);

        if &abs_diff <= offset {
            Failure::new(&self)
                .expected_it(format!("not to be within <{:?}> of <{:?}>", offset, expected))
                .but_it(format!("was <{:?}>, which is inside that range", &self.data))
                .fail();
        }

        self
    }
}

#[cfg(test)]
mod tests {

    use crate::{assert_fails, assert_that};

    use super::*;

    #[test]
    fn is_close_to_passes_for_integer_less_than_target_by_offset() {
        assert_that!(5).is_close_to(3, 2u32);
    }

    #[test]
    fn is_close_to_passes_for_float_greater_than_target_by_less_than_offset() {
        assert_that!(3.6).is_close_to(3.5, 0.2);
    }

    #[test]
    fn is_close_to_passes_for_number_in_range_exceeding_type_bounds() {
        assert_that!(3u32).is_close_to(1u32, 2u32);
    }

    #[test]
    fn is_close_to_fails_for_integer_greater_than_target_by_more_than_offset() {
        assert_fails!((2 + 3).is_close_to(2, 2u32),
            expected it "to be within <2> of <2>"
            but it "was <5>, which is outside that range");
    }

    #[test]
    fn is_close_to_fails_for_float_less_than_target_by_more_than_offset() {
        assert_fails!((0.25 + 0.75).is_close_to(1.5, 0.2),
            expected it "to be within <0.2> of <1.5>"
            but it "was <1.0>, which is outside that range");
    }

    #[test]
    fn is_close_to_fails_for_nan() {
        assert_fails!((f32::NAN).is_close_to(1.0, 100.0),
            expected it "to be within <100.0> of <1.0>"
            but it "was <NaN>, which is outside that range");
    }

    #[test]
    fn is_not_close_to_passes_for_integer_greater_than_target_by_more_than_offset() {
        assert_that!(5).is_not_close_to(2, 2u32);
    }

    #[test]
    fn is_not_close_to_passes_for_float_less_than_target_by_more_than_offset() {
        assert_that!(1.0).is_not_close_to(1.5, 0.2);
    }

    #[test]
    fn is_not_close_to_passes_for_nan() {
        assert_that!(f32::NAN).is_not_close_to(1.0, 100.0);
    }

    #[test]
    fn is_not_close_to_fails_for_integer_less_than_target_by_offset() {
        assert_fails!((2 + 3).is_not_close_to(3, 2u32),
            expected it "not to be within <2> of <3>"
            but it "was <5>, which is inside that range");
    }

    #[test]
    fn is_not_close_to_fails_for_float_greater_than_target_by_less_than_offset() {
        assert_fails!((3.0f32 + 0.75f32).is_not_close_to(3.5f32, 0.3f32),
            expected it "not to be within <0.3> of <3.5>"
            but it "was <3.75>, which is inside that range");
    }
}
