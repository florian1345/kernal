use crate::{AssertThat, Failure};

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with [bool]
/// argument.
///
/// Examples:
///
/// ```
/// use kernal::prelude::*;
///
/// assert_that!(1 == 1).is_true();
/// assert_that!(1 == 2).is_false();
/// ```
pub trait BooleanAssertions {

    /// Asserts that the tested boolean is `true`.
    fn is_true(self) -> Self;

    /// Asserts that the tested boolean is `false`.
    fn is_false(self) -> Self;
}

impl BooleanAssertions for AssertThat<bool> {

    fn is_true(self) -> AssertThat<bool> {
        if !self.data {
            Failure::new(&self).expected_it("to be true").but_it("was false").fail();
        }

        self
    }

    fn is_false(self) -> AssertThat<bool> {
        if self.data {
            Failure::new(&self).expected_it("to be false").but_it("was true").fail();
        }

        self
    }
}

#[cfg(test)]
mod tests {

    use crate::{assert_fails, assert_that};

    use super::*;

    #[test]
    fn is_true_passes_for_true() {
        assert_that!(true).is_true();
    }

    #[test]
    fn is_true_fails_for_false() {
        assert_fails!((false).is_true(), expected it "to be true" but it "was false");
    }

    #[test]
    fn is_false_passes_for_false() {
        assert_that!(false).is_false();
    }

    #[test]
    fn is_false_fails_for_true() {
        assert_fails!((true).is_false(), expected it "to be false" but it "was true");
    }
}
