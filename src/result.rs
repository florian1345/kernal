use std::borrow::Borrow;
use std::fmt::Debug;
use crate::{AssertThat, Failure};

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with [Result]
/// argument.
///
/// Examples:
///
/// ```
/// use kernal::prelude::*;
/// use std::str::FromStr;
///
/// assert_that!(u32::from_str("123")).is_ok();
/// assert_that!(u32::from_str("hello")).is_err();
/// ```
pub trait ResultAssertions<V, E> {

    /// Asserts that the tested result is an `Ok` variant, i.e. there is no error.
    fn is_ok(self) -> Self;

    /// Asserts that the tested result is an `Err` variant, i.e. there is an error.
    fn is_err(self) -> Self;

    /// Asserts that the tested result is ok (see [ResultAssertions::is_ok]) and returns a new
    /// [AssertThat] instance that allows assertions on its value.
    fn to_value(self) -> AssertThat<V>;

    /// Asserts that the tested result is an error (see [ResultAssertions::is_err]) and returns a
    /// new [AssertThat] instance that allows assertions on its error.
    fn to_error(self) -> AssertThat<E>;
}

impl<V, E> ResultAssertions<V, E> for AssertThat<Result<V, E>>
where
    V: Debug,
    E: Debug
{
    fn is_ok(self) -> Self {
        if self.data.is_err() {
            Failure::new(&self)
                .expected_it("to be ok")
                .but_it_was_data(&self)
                .fail();
        }

        self
    }

    fn is_err(self) -> Self {
        if self.data.is_ok() {
            Failure::new(&self)
                .expected_it("to be an error")
                .but_it_was_data(&self)
                .fail();
        }

        self
    }

    fn to_value(mut self) -> AssertThat<V> {
        self = self.is_ok();

        AssertThat {
            data: self.data.unwrap(),
            expression: format!("value of <{}>", self.expression)
        }
    }

    fn to_error(mut self) -> AssertThat<E> {
        self = self.is_err();

        AssertThat {
            data: self.data.unwrap_err(),
            expression: format!("error of <{}>", self.expression)
        }
    }
}

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with [Result]
/// argument where the value type implements [PartialEq].
///
/// Examples:
///
/// ```
/// use kernal::prelude::*;
/// use std::str::FromStr;
///
/// assert_that!(u32::from_str("123")).contains_value(123);
/// assert_that!(u32::from_str("hello")).does_not_contain_value(0);
/// ```
pub trait ResultValuePartialEqAssertions<V, E> {

    /// Asserts that the tested result is an `Ok` variant that contains the given `expected` value.
    fn contains_value<B: Borrow<V>>(self, expected: B) -> Self;

    /// Asserts that the tested result is not an `Ok` variant that contains the given `unexpected`
    /// value. That is, this assertion passes if and only if the tested result is an `Err` variant
    /// or an `Ok` variant that contains some other value.
    fn does_not_contain_value<B: Borrow<V>>(self, unexpected: B) -> Self;
}

impl<V, E> ResultValuePartialEqAssertions<V, E> for AssertThat<Result<V, E>>
where
    V: Debug + PartialEq,
    E: Debug
{
    fn contains_value<B: Borrow<V>>(self, expected: B) -> Self {
        let expected = expected.borrow();

        match &self.data {
            Ok(value) if value == expected => self,
            Ok(_) => Failure::new(&self)
                .expected_it(format!("to contain the value <{:?}>", expected))
                .but_it_was_data(&self)
                .fail(),
            Err(_) => Failure::new(&self).expected_it("to be ok").but_it_was_data(&self).fail()
        }
    }

    fn does_not_contain_value<B: Borrow<V>>(self, unexpected: B) -> Self {
        let unexpected = unexpected.borrow();

        if self.data.iter().any(|value| value == unexpected) {
            Failure::new(&self)
                .expected_it(format!("not to be ok with the value <{:?}>", unexpected))
                .but_it("was")
                .fail();
        }

        self
    }
}

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with [Result]
/// argument where the error type implements [PartialEq].
///
/// Examples:
///
/// ```
/// use kernal::prelude::*;
/// use std::str::FromStr;
///
/// let err_result: Result<u32, &str> = Err("some error");
/// let ok_result: Result<u32, &str> = Ok(123);
///
/// assert_that!(err_result).contains_error("some error");
/// assert_that!(ok_result).does_not_contain_error("some error");
/// ```
pub trait ResultErrorPartialEqAssertions<V, E> {

    /// Asserts that the tested result is an `Err` variant that contains the given `expected` error.
    fn contains_error<B: Borrow<E>>(self, expected: B) -> Self;

    /// Asserts that the tested result is not an `Err` variant that contains the given `unexpected`
    /// error. That is, this assertion passes if and only if the tested result is an `Ok` variant
    /// or an `Err` variant that contains some other error.
    fn does_not_contain_error<B: Borrow<E>>(self, unexpected: B) -> Self;
}

impl<V, E> ResultErrorPartialEqAssertions<V, E> for AssertThat<Result<V, E>>
where
    V: Debug,
    E: Debug + PartialEq
{
    fn contains_error<B: Borrow<E>>(self, expected: B) -> Self {
        let expected = expected.borrow();

        match &self.data {
            Err(error) if error == expected => self,
            Err(_) => Failure::new(&self)
                .expected_it(format!("to contain the error <{:?}>", expected))
                .but_it_was_data(&self)
                .fail(),
            Ok(_) => Failure::new(&self).expected_it("to be an error").but_it_was_data(&self).fail()
        }
    }

    fn does_not_contain_error<B: Borrow<E>>(self, unexpected: B) -> Self {
        let unexpected = unexpected.borrow();
        let contains_unexpected_error = match &self.data {
            Err(error) => error == unexpected,
            _ => false
        };

        if contains_unexpected_error {
            Failure::new(&self)
                .expected_it(format!("not to be the error <{:?}>", unexpected))
                .but_it("was")
                .fail();
        }

        self
    }
}

#[cfg(test)]
mod tests {
    use crate::assert_fails;
    use crate::prelude::*;

    #[test]
    fn is_ok_passes_for_ok() {
        let result: Result<u32, u32> = Ok(5);

        assert_that!(result).is_ok();
    }

    #[test]
    fn is_ok_fails_for_err() {
        let result: Result<u32, u32> = Err(10);

        assert_fails!((result).is_ok(), expected it "to be ok" but it "was <Err(10)>");
    }

    #[test]
    fn is_err_passes_for_err() {
        let result: Result<u32, u32> = Err(10);

        assert_that!(result).is_err();
    }

    #[test]
    fn is_err_fails_for_ok() {
        let result: Result<u32, u32> = Ok(5);

        assert_fails!((result).is_err(), expected it "to be an error" but it "was <Ok(5)>");
    }

    #[test]
    fn to_value_works_for_ok() {
        let result: Result<u32, u32> = Ok(42);

        assert_that!(result).to_value().is_equal_to(42);
    }

    #[test]
    fn to_value_has_the_correct_expression() {
        let result: Result<u32, u32> = Ok(42);
        let expression = assert_that!(result).to_value().expression;

        assert_that!(expression.as_str()).is_equal_to("value of <result>");
    }

    #[test]
    fn to_value_panics_for_err() {
        let result: Result<u32, u32> = Err(23);

        assert_fails!((result).to_value(), expected it "to be ok" but it "was <Err(23)>");
    }

    #[test]
    fn to_error_works_for_err() {
        let result: Result<u32, u32> = Err(23);

        assert_that!(result).to_error().is_equal_to(23);
    }

    #[test]
    fn to_error_has_the_correct_expression() {
        let result: Result<u32, u32> = Err(23);
        let expression = assert_that!(result).to_error().expression;

        assert_that!(expression.as_str()).is_equal_to("error of <result>");
    }

    #[test]
    fn to_error_panics_for_ok() {
        let result: Result<u32, u32> = Ok(42);

        assert_fails!((result).to_error(), expected it "to be an error" but it "was <Ok(42)>");
    }

    #[test]
    fn contains_value_passes_for_ok_with_correct_value() {
        let result: Result<u32, u32> = Ok(420);

        assert_that!(result).contains_value(420);
    }

    #[test]
    fn contains_value_fails_for_ok_with_incorrect_value() {
        let result: Result<u32, u32> = Ok(420);

        assert_fails!((result).contains_value(1337),
            expected it "to contain the value <1337>"
            but it "was <Ok(420)>");
    }

    #[test]
    fn contains_value_fails_for_err() {
        let result: Result<u32, u32> = Err(1337);

        assert_fails!((result).contains_value(1337),
            expected it "to be ok"
            but it "was <Err(1337)>");
    }

    #[test]
    fn does_not_contain_value_passes_for_ok_with_incorrect_value() {
        let result: Result<u32, u32> = Ok(420);

        assert_that!(result).does_not_contain_value(1337);
    }

    #[test]
    fn does_not_contain_value_passes_for_err() {
        let result: Result<u32, u32> = Err(1337);

        assert_that!(result).does_not_contain_value(1337);
    }

    #[test]
    fn does_not_contain_value_fails_for_ok_with_correct_value() {
        let result: Result<u32, u32> = Ok(420);

        assert_fails!((result).does_not_contain_value(420),
            expected it "not to be ok with the value <420>"
            but it "was");
    }

    #[test]
    fn contains_error_passes_for_err_with_correct_error() {
        let result: Result<u32, u32> = Err(1337);

        assert_that!(result).contains_error(1337);
    }

    #[test]
    fn contains_error_fails_for_err_with_incorrect_error() {
        let result: Result<u32, u32> = Err(420);

        assert_fails!((result).contains_error(1337),
            expected it "to contain the error <1337>"
            but it "was <Err(420)>");
    }

    #[test]
    fn contains_error_fails_for_ok() {
        let result: Result<u32, u32> = Ok(1337);

        assert_fails!((result).contains_error(1337),
            expected it "to be an error"
            but it "was <Ok(1337)>");
    }

    #[test]
    fn does_not_contain_error_passes_for_err_with_incorrect_error() {
        let result: Result<u32, u32> = Err(420);

        assert_that!(result).does_not_contain_error(1337);
    }

    #[test]
    fn does_not_contain_error_passes_for_ok() {
        let result: Result<u32, u32> = Ok(1337);

        assert_that!(result).does_not_contain_error(1337);
    }

    #[test]
    fn does_not_contain_error_fails_for_err_with_correct_error() {
        let result: Result<u32, u32> = Err(1337);

        assert_fails!((result).does_not_contain_error(1337),
            expected it "not to be the error <1337>"
            but it "was");
    }
}
