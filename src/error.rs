use std::borrow::Borrow;
use std::error::Error;

use crate::{AssertThat, Failure};

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with an
/// argument that implements the [Error] trait.
///
/// Examples:
///
/// ```
/// use kernal::prelude::*;
///
/// use std::error::Error;
/// use std::fmt::{self, Debug, Display, Formatter};
///
/// #[derive(Debug)]
/// struct MyError;
///
/// impl Display for MyError {
///     fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
///         write!(f, "test message")
///     }
/// }
///
/// impl Error for MyError { }
///
/// assert_that!(MyError).has_message("test message").does_not_have_source();
/// ```
pub trait ErrorAssertions {

    /// Asserts that the message obtained by using the [Display](std::fmt::Display) implementation
    /// of the tested error is equal to the given `expected_message`.
    fn has_message<M: Borrow<str>>(self, expected_message: M) -> Self;

    /// Asserts that the tested error has a source, i.e. running [Error::source] on it yields a
    /// `Some` variant.
    fn has_source(self) -> Self;

    /// Asserts that the tested error does not have a source, i.e. running [Error::source] on it
    /// yields `None`.
    fn does_not_have_source(self) -> Self;
}

impl<T: Error> ErrorAssertions for AssertThat<T> {

    fn has_message<M: Borrow<str>>(self, expected_message: M) -> Self {
        let message = self.data.to_string();
        let expected_message = expected_message.borrow();

        if &message != expected_message {
            Failure::new(&self)
                .expected_it(format!("to have the error message <{}>",
                    expected_message.escape_debug()))
                .but_it(format!("had the message <{}>", message.escape_debug()))
                .fail()
        }

        self
    }

    fn has_source(self) -> Self {
        if self.data.source().is_none() {
            Failure::new(&self).expected_it("to have an error source").but_it("did not").fail();
        }

        self
    }

    fn does_not_have_source(self) -> Self {
        if self.data.source().is_some() {
            Failure::new(&self).expected_it("not to have an error source").but_it("did").fail();
        }

        self
    }
}

#[cfg(test)]
mod tests {

    use std::fmt::{self, Display, Formatter};

    use crate::{assert_fails, assert_that};

    use super::*;

    #[derive(Debug)]
    struct InnerError;

    impl Display for InnerError {
        fn fmt(&self, _: &mut Formatter<'_>) -> fmt::Result {
            panic!("attempted to display inner error")
        }
    }

    impl Error for InnerError { }

    #[derive(Debug)]
    struct MockError {
        message: String,
        source: Option<InnerError>
    }

    impl MockError {
        fn with_source(message: impl Into<String>) -> MockError {
            MockError {
                message: message.into(),
                source: Some(InnerError)
            }
        }

        fn without_source(message: impl Into<String>) -> MockError {
            MockError {
                message: message.into(),
                source: None
            }
        }
    }

    impl Display for MockError {
        fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
            write!(f, "{}", &self.message)
        }
    }

    impl Error for MockError {
        fn source(&self) -> Option<&(dyn Error + 'static)> {
            self.source.as_ref().map(|e| {
                let object: &(dyn Error + 'static) = &*e;
                object
            })
        }
    }

    #[test]
    fn has_message_passes_for_correct_message() {
        let error = MockError::without_source("the message");
        
        assert_that!(error).has_message("the message");
    }

    #[test]
    fn has_message_fails_for_incorrect_message() {
        let error = MockError::without_source("the message");

        assert_fails!((error).has_message("not the message"),
            expected it "to have the error message <not the message>"
            but it "had the message <the message>");
    }

    #[test]
    fn has_source_passes_for_error_with_source() {
        let error = MockError::with_source("irrelevant message");

        assert_that!(error).has_source();
    }

    #[test]
    fn has_source_fails_for_error_without_source() {
        let error = MockError::without_source("irrelevant message");

        assert_fails!((error).has_source(), expected it "to have an error source" but it "did not");
    }

    #[test]
    fn does_not_have_source_passes_for_error_without_source() {
        let error = MockError::without_source("");

        assert_that!(error).does_not_have_source();
    }

    #[test]
    fn does_not_have_source_fails_for_error_with_source() {
        let error = MockError::with_source("");

        assert_fails!((error).does_not_have_source(),
            expected it "not to have an error source"
            but it "did");
    }
}
