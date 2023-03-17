//! Contains assertions for [Option] values. The [OptionAssertions] works for all [Option]s which
//! implement [Debug]. [OptionPartialEqAssertions] provides additional assertions if the value type
//! implements [PartialEq].

use std::borrow::Borrow;
use std::fmt::Debug;

use crate::{AssertThat, Failure};

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with [Option]
/// argument.
///
/// Examples:
///
/// ```
/// use kernal::prelude::*;
///
/// assert_that!(Some(2 + 3)).is_some().to_value().is_equal_to(5);
/// assert_that!(None::<u32>).is_none();
/// ```
pub trait OptionAssertions<T> {

    /// Asserts that the tested option is a `Some` variant with any value, i.e. that
    /// [Option::is_some] is `true`.
    fn is_some(self) -> Self;

    /// Asserts that the tested option is a `None` variant, i.e. that [Option::is_none] is `true`.
    fn is_none(self) -> Self;

    /// Asserts that the tested option is a `Some` variant and converts this asserter to one for the
    /// contained value, so chained assertions can be run on the unwrapped value.
    fn to_value(self) -> AssertThat<T>;
}

impl<T: Debug> OptionAssertions<T> for AssertThat<Option<T>> {

    fn is_some(self) -> Self {
        if self.data.is_none() {
            Failure::new(&self).expected_it("to be <Some(_)>").but_it("was <None>").fail();
        }

        self
    }

    fn is_none(self) -> Self {
        if let Some(data) = self.data.borrow() {
            Failure::new(&self)
                .expected_it("to be <None>")
                .but_it(format!("was <Some({:?})>", data))
                .fail();
        }

        self
    }

    fn to_value(self) -> AssertThat<T> {
        match self.data {
            None => Failure::new(&self).expected_it("to be <Some(_)>").but_it("was <None>").fail(),
            Some(data) => AssertThat {
                data,
                expression: format!("value of <{}>", self.expression)
            }
        }
    }
}

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with [Option]
/// argument whose value type implements the [PartialEq] trait.
///
/// Examples:
///
/// ```
/// use kernal::prelude::*;
///
/// assert_that!(Some(2 + 3)).contains(5).does_not_contain(3);
/// assert_that!(None::<u32>).does_not_contain(0);
/// ```
pub trait OptionPartialEqAssertions<T> {

    /// Asserts that the tested option is a `Some` variant that contains a value equal to the given
    /// `expected` value according to the [PartialEq] trait.
    fn contains<E: Borrow<T>>(self, expected: E) -> Self;

    /// Asserts that the tested option is a `None` variant or a `Some` variant that contains a value
    /// different from the given `unexpected` value according to the [PartialEq] trait.
    fn does_not_contain<E: Borrow<T>>(self, unexpected: E) -> Self;
}

impl<T: Debug + PartialEq> OptionPartialEqAssertions<T> for AssertThat<Option<T>> {

    fn contains<E: Borrow<T>>(self, expected: E) -> Self {
        let expected = expected.borrow();

        if !self.data.iter().any(|data| data == expected) {
            Failure::new(&self)
                .expected_it(format!("to contain <{:?}>", expected))
                .but_it_was_data(&self)
                .fail();
        }

        self
    }

    fn does_not_contain<E: Borrow<T>>(self, unexpected: E) -> Self {
        let unexpected = unexpected.borrow();

        if self.data.iter().any(|data| data == unexpected) {
            Failure::new(&self)
                .expected_it(format!("not to contain <{:?}>", unexpected))
                .but_it_was_data(&self)
                .fail();
        }

        self
    }
}

#[cfg(test)]
mod tests {

    use crate::{assert_fails, assert_that};
    use crate::partial_eq::PartialEqAssertions;

    use super::*;

    #[test]
    fn is_some_passes_for_some() {
        assert_that!(Some(0)).is_some();
    }

    #[test]
    fn is_some_fails_for_none() {
        assert_fails!((None::<u32>).is_some(), expected it "to be <Some(_)>" but it "was <None>");
    }

    #[test]
    fn is_none_passes_for_none() {
        assert_that!(None::<u32>).is_none();
    }

    #[test]
    fn is_none_fails_for_some() {
        assert_fails!((Some(42)).is_none(), expected it "to be <None>" but it "was <Some(42)>");
    }

    #[test]
    fn to_value_returns_correct_value_for_some() {
        assert_that!(Some(1 + 1)).to_value().is_equal_to(2);
    }

    #[test]
    fn to_value_returns_correct_expression_for_some() {
        let expression = assert_that!(Some(1 + 1)).to_value().expression;

        assert_that!(expression.as_str()).is_equal_to("value of <Some(1 + 1)>");
    }

    #[test]
    fn to_value_fails_for_none() {
        assert_fails!((None::<u32>).is_some(), expected it "to be <Some(_)>" but it "was <None>");
    }

    #[test]
    fn contains_passes_for_some_with_correct_value() {
        assert_that!(Some("hello")).contains("hello");
    }

    #[test]
    fn contains_fails_for_some_with_incorrect_value() {
        assert_fails!((Some("hello")).contains("world"),
            expected it "to contain <\"world\">"
            but it "was <Some(\"hello\")>");
    }

    #[test]
    fn contains_fails_for_none() {
        assert_fails!((None::<&str>).contains("hello"),
            expected it "to contain <\"hello\">"
            but it "was <None>");
    }

    #[test]
    fn does_not_contain_passes_for_some_with_incorrect_value() {
        assert_that!(Some("hello")).does_not_contain("world");
    }

    #[test]
    fn does_not_contain_passes_for_none() {
        assert_that!(None::<&str>).does_not_contain("hello");
    }

    #[test]
    fn does_not_contain_fails_for_some_with_correct_value() {
        assert_fails!((Some("hello")).does_not_contain("hello"),
            expected it "not to contain <\"hello\">"
            but it "was <Some(\"hello\")>");
    }
}
