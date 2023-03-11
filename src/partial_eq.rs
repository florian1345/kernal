use std::borrow::Borrow;
use std::fmt::Debug;

use crate::{AssertThat, Failure};

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with an
/// argument that implements the [PartialEq] trait.
///
/// Examples:
///
/// ```
/// use kernal::prelude::*;
///
/// assert_that!(1 + 1).is_equal_to(2).is_not_equal_to(3);
/// ```
pub trait PartialEqAssertions<T> {

    /// Asserts that the tested value is equal to the given `expected` value according to the
    /// [PartialEq] trait.
    fn is_equal_to<E: Borrow<T>>(self, expected: E) -> Self;

    /// Asserts that the tested value is different from the given `expected` value according to the
    /// [PartialEq] trait.
    fn is_not_equal_to<E: Borrow<T>>(self, expected: E) -> Self;
}

impl<T: Debug + PartialEq> PartialEqAssertions<T> for AssertThat<T> {
    fn is_equal_to<E: Borrow<T>>(self, expected: E) -> Self {
        let expected_data = expected.borrow();

        if &self.data != expected_data {
            Failure::new(&self)
                .expected_it(format!("to equal <{:?}>", expected_data))
                .but_it_was_data(&self)
                .fail();
        }

        self
    }

    fn is_not_equal_to<E: Borrow<T>>(self, expected: E) -> Self {
        let expected_data = expected.borrow();

        if &self.data == expected_data {
            Failure::new(&self)
                .expected_it(format!("not to equal <{:?}>", expected_data))
                .but_it("did")
                .fail();
        }

        self
    }
}

#[cfg(test)]
mod tests {

    use crate::{assert_fails, assert_that};

    use super::*;

    struct U32Wrapper {
        data: u32
    }

    impl Borrow<u32> for U32Wrapper {
        fn borrow(&self) -> &u32 {
            &self.data
        }
    }

    #[test]
    fn is_equal_to_passes_for_equal_integers() {
        assert_that!(1 + 2).is_equal_to(3);
    }
    
    #[test]
    fn is_equal_to_passes_for_u32_with_equivalent_u32_wrapper() {
        assert_that!(42).is_equal_to(U32Wrapper { data: 42 });
    }

    #[test]
    fn is_equal_to_fails_for_different_integers() {
        assert_fails!((1 - 1).is_equal_to(-1), expected it "to equal <-1>" but it "was <0>");
    }

    #[test]
    fn is_equal_to_fails_for_u32_with_non_equivalent_u32_wrapper() {
        assert_fails!((21 + 21).is_equal_to(U32Wrapper { data: 43 }),
            expected it "to equal <43>"
            but it "was <42>");
    }

    #[test]
    fn is_not_equal_to_passes_for_different_integers() {
        assert_that!(1 + 2).is_not_equal_to(4);
    }

    #[test]
    fn is_not_equal_to_passes_for_u32_with_non_equivalent_u32_wrapper() {
        assert_that!(42).is_not_equal_to(U32Wrapper { data: 43 });
    }

    #[test]
    fn is_not_equal_to_fails_for_equal_integers() {
        assert_fails!((1 - 1).is_not_equal_to(0), expected it "not to equal <0>" but it "did");
    }

    #[test]
    fn is_not_equal_to_fails_for_u32_with_equivalent_u32_wrapper() {
        assert_fails!((21 + 21).is_not_equal_to(U32Wrapper { data: 42 }),
            expected it "not to equal <42>"
            but it "did");
    }
}
