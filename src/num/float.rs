//! Specialized assertions for floating point numbers, grouped by the [Float] trait. This relates to
//! the special values (infinity, not-a-number), not to the non-integer behavior of floats. See
//! [FloatAssertions] for more details.

use std::fmt::Debug;

use crate::{AssertThat, Failure};

/// A trait for all types implementing IEEE-754-style floating point numbers, i.e. values which can
/// be infinite or NaN (not a number). This is implemented on all primitive float types of the
/// standard library. Used to enable assertions defined by [FloatAssertions].
pub trait Float {
    /// Indicates whether this float is infinite, i.e. positive infinity or negative infinity.
    fn is_infinite(&self) -> bool;

    /// Indicates whether this float is NaN (not a number).
    fn is_nan(&self) -> bool;
}

macro_rules! impl_float {
    ($type:ty) => {
        impl Float for $type {
            fn is_infinite(&self) -> bool {
                <$type>::is_infinite(*self)
            }

            fn is_nan(&self) -> bool {
                <$type>::is_nan(*self)
            }
        }
    };
}

impl_float!(f32);
impl_float!(f64);

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with an
/// argument that implements the [Float] trait, e.g. a standard library primitive float ([f32] or
/// [f64]).
///
/// Examples:
///
/// ```
/// use kernal::prelude::*;
///
/// assert_that!(0.5).is_finite().is_not_nan();
/// assert_that!(f32::NEG_INFINITY).is_infinite();
/// assert_that!(f32::NAN).is_nan();
/// ```
pub trait FloatAssertions {
    /// Asserts that the tested float represents a finite number, i.e. it is not positive infinity,
    /// negative infinity, or NaN.
    fn is_finite(self) -> Self;

    /// Asserts that the tested float is positive or negative infinity.
    fn is_infinite(self) -> Self;

    /// Asserts that the tested float is NaN (not a number).
    fn is_nan(self) -> Self;

    /// Asserts that the tested float is not NaN (not a number), i.e. it is a number.
    fn is_not_nan(self) -> Self;
}

impl<T: Debug + Float> FloatAssertions for AssertThat<T> {
    fn is_finite(self) -> Self {
        if self.data.is_infinite() || self.data.is_nan() {
            Failure::new(&self)
                .expected_it("to be finite")
                .but_it_was_data(&self)
                .fail();
        }

        self
    }

    fn is_infinite(self) -> Self {
        if !self.data.is_infinite() {
            Failure::new(&self)
                .expected_it("to be infinite")
                .but_it_was_data(&self)
                .fail();
        }

        self
    }

    fn is_nan(self) -> Self {
        if !self.data.is_nan() {
            Failure::new(&self)
                .expected_it("to be <NaN>")
                .but_it_was_data(&self)
                .fail();
        }

        self
    }

    fn is_not_nan(self) -> Self {
        if self.data.is_nan() {
            Failure::new(&self)
                .expected_it("not to be <NaN>")
                .but_it("was")
                .fail();
        }

        self
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::{assert_fails, assert_that};

    #[test]
    fn is_finite_passes_for_zero() {
        assert_that!(0.0).is_finite();
    }

    #[test]
    fn is_finite_passes_for_one() {
        assert_that!(1.0).is_finite();
    }

    #[test]
    fn is_finite_passes_for_negative_one() {
        assert_that!(-1.0).is_finite();
    }

    #[test]
    fn is_finite_fails_for_infinity() {
        assert_fails!((f32::INFINITY).is_finite(),
            expected it "to be finite"
            but it "was <inf>");
    }

    #[test]
    fn is_finite_fails_for_negative_infinity() {
        assert_fails!((f32::NEG_INFINITY).is_finite(),
            expected it "to be finite"
            but it "was <-inf>");
    }

    #[test]
    fn is_finite_fails_for_nan() {
        assert_fails!((f32::NAN).is_finite(), expected it "to be finite" but it "was <NaN>");
    }

    #[test]
    fn is_infinite_passes_for_infinity() {
        assert_that!(f32::INFINITY).is_infinite();
    }

    #[test]
    fn is_infinite_passes_for_negative_infinity() {
        assert_that!(f32::NEG_INFINITY).is_infinite();
    }

    #[test]
    fn is_infinite_fails_for_one() {
        assert_fails!((1.0).is_infinite(), expected it "to be infinite" but it "was <1.0>");
    }

    #[test]
    fn is_infinite_fails_for_nan() {
        assert_fails!((f32::NAN).is_infinite(), expected it "to be infinite" but it "was <NaN>");
    }

    #[test]
    fn is_nan_passes_for_nan() {
        assert_that!(f32::NAN).is_nan();
    }

    #[test]
    fn is_nan_fails_for_zero() {
        assert_fails!((0.0).is_nan(), expected it "to be <NaN>" but it "was <0.0>");
    }

    #[test]
    fn is_nan_fails_for_infinity() {
        assert_fails!((f32::INFINITY).is_nan(), expected it "to be <NaN>" but it "was <inf>");
    }

    #[test]
    fn is_not_nan_passes_for_zero() {
        assert_that!(0.0).is_not_nan();
    }

    #[test]
    fn is_not_nan_passes_for_infinity() {
        assert_that!(f32::INFINITY).is_not_nan();
    }

    #[test]
    fn is_not_nan_fails_for_nan() {
        assert_fails!((f32::NAN).is_not_nan(), expected it "not to be <NaN>" but it "was");
    }
}
