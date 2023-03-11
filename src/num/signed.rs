use std::fmt::Debug;

use crate::{AssertThat, Failure};
use crate::num::{Signed, Zero};

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with a numeric
/// argument of a type that can be [Zero]. The blanket implementation also requires [PartialEq] on
/// the number type in order to check equality with zero.
///
/// Examples:
///
/// ```
/// use kernal::prelude::*;
///
/// assert_that!(5).is_not_zero();
/// assert_that!(0).is_zero();
/// ```
pub trait ZeroableAssertions {

    /// Asserts that the tested value is equal to zero according to the [PartialEq] trait and the
    /// zero-value provided by [Zero].
    fn is_zero(self) -> Self;

    /// Asserts that the tested value is different from zero according to the [PartialEq] trait and
    /// the zero-value provided by [Zero].
    fn is_not_zero(self) -> Self;
}

impl<T: Debug + PartialEq + Zero> ZeroableAssertions for AssertThat<T> {

    fn is_zero(self) -> Self {
        if self.data != T::ZERO {
            Failure::new(&self)
                .expected_it("to be zero")
                .but_it_was_data(&self)
                .fail();
        }

        self
    }

    fn is_not_zero(self) -> Self {
        if self.data == T::ZERO {
            Failure::new(&self).expected_it("not to be zero").but_it("was").fail();
        }

        self
    }
}

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with a numeric
/// argument of a type that is [Signed], i.e. can be positive, negative, or zero.
///
/// Examples:
///
/// ```
/// use kernal::prelude::*;
///
/// assert_that!(5).is_positive();
/// assert_that!(0).is_not_positive().is_not_negative();
/// ```
pub trait SignedAssertions {

    /// Asserts that the tested value is positive, i.e. strictly greater than [Zero::ZERO].
    fn is_positive(self) -> Self;

    /// Asserts that the tested value is not positive, i.e. less than or equal to [Zero::ZERO] or
    /// not comparable to zero.
    fn is_not_positive(self) -> Self;

    /// Asserts that the tested value is negative, i.e. strictly less than [Zero::ZERO].
    fn is_negative(self) -> Self;

    /// Asserts that the tested value is not negative, i.e. greater than or equal to [Zero::ZERO] or
    /// not comparable to zero.
    fn is_not_negative(self) -> Self;
}

impl<T: Debug + Signed> SignedAssertions for AssertThat<T> {

    fn is_positive(self) -> Self {
        if !(self.data > T::ZERO) {
            Failure::new(&self).expected_it("to be positive").but_it_was_data(&self).fail();
        }

        self
    }

    fn is_not_positive(self) -> Self {
        if self.data > T::ZERO {
            Failure::new(&self).expected_it("not to be positive").but_it_was_data(&self).fail();
        }

        self
    }

    fn is_negative(self) -> Self {
        if !(self.data < T::ZERO) {
            Failure::new(&self).expected_it("to be negative").but_it_was_data(&self).fail();
        }
        
        self
    }

    fn is_not_negative(self) -> Self {
        if self.data < T::ZERO {
            Failure::new(&self).expected_it("not to be negative").but_it_was_data(&self).fail();
        }
        
        self
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    use crate::{assert_fails, assert_that};

    #[test]
    fn is_zero_passes_for_zero() {
        assert_that!(0).is_zero();
    }

    #[test]
    fn is_zero_fails_for_one() {
        assert_fails!((1).is_zero(), expected it "to be zero" but it "was <1>");
    }

    #[test]
    fn is_zero_fails_for_negative_one() {
        assert_fails!((-1).is_zero(), expected it "to be zero" but it "was <-1>");
    }

    #[test]
    fn is_not_zero_passes_for_one() {
        assert_that!(1).is_not_zero();
    }

    #[test]
    fn is_not_zero_passes_for_negative_one() {
        assert_that!(-1).is_not_zero();
    }

    #[test]
    fn is_not_zero_fails_for_zero() {
        assert_fails!((0).is_not_zero(), expected it "not to be zero" but it "was");
    }

    #[test]
    fn is_positive_passes_for_one() {
        assert_that!(1).is_positive();
    }

    #[test]
    fn is_positive_fails_for_zero() {
        assert_fails!((0).is_positive(), expected it "to be positive" but it "was <0>");
    }

    #[test]
    fn is_positive_fails_for_negative_one() {
        assert_fails!((-1).is_positive(), expected it "to be positive" but it "was <-1>");
    }

    #[test]
    fn is_not_positive_passes_for_zero() {
        assert_that!(0).is_not_positive();
    }

    #[test]
    fn is_not_positive_passes_for_negative_one() {
        assert_that!(-1).is_not_positive();
    }

    #[test]
    fn is_not_positive_fails_for_one() {
        assert_fails!((1).is_not_positive(), expected it "not to be positive" but it "was <1>");
    }

    #[test]
    fn is_negative_passes_for_negative_one() {
        assert_that!(-1).is_negative();
    }

    #[test]
    fn is_negative_fails_for_zero() {
        assert_fails!((0).is_negative(), expected it "to be negative" but it "was <0>");
    }

    #[test]
    fn is_negative_fails_for_one() {
        assert_fails!((1).is_negative(), expected it "to be negative" but it "was <1>");
    }

    #[test]
    fn is_not_negative_passes_for_zero() {
        assert_that!(0).is_not_negative();
    }

    #[test]
    fn is_not_negative_passes_for_one() {
        assert_that!(1).is_not_negative();
    }

    #[test]
    fn is_not_negative_fails_for_negative_one() {
        assert_fails!((-1).is_not_negative(), expected it "not to be negative" but it "was <-1>");
    }
}
