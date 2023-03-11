use std::any::Any;
use std::borrow::Borrow;
use std::panic::{catch_unwind, UnwindSafe};

use crate::{AssertThat, Failure};

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with a function
/// argument that has no parameters. It defines assertions over whether the given function panics or
/// terminates normally. Contrary to other assertions, these will consume the [AssertThat] instance
/// when asserted. This is because the assertions call the function in order to determine whether
/// it panics.
///
/// Examples:
///
/// ```
/// use kernal::prelude::*;
///
/// assert_that!(|| { }).does_not_panic();
/// assert_that!(|| panic!()).panics();
/// assert_that!(|| panic!("my message")).panics_with_message("my message");
/// assert_that!(|| panic!("other message")).panics_with_message_containing("message");
/// ```
pub trait PanicAssertions {

    /// Runs the tested function and asserts that it panicked, i.e. the test will fail if the
    /// function terminated normally.
    fn panics(self);

    /// Runs the tested function and asserts that it did not panic, i.e. that it terminated
    /// normally.
    fn does_not_panic(self);

    /// Runs the tested function and asserts that it panicked, i.e. the test will fail if the
    /// function terminated normally. In addition, it is asserted that the panic message equals the
    /// given `expected_message`.
    fn panics_with_message<M: Borrow<str>>(self, expected_message: M);

    /// Runs the tested function and asserts that it panicked, i.e. the test will fail if the
    /// function terminated normally. In addition, it is asserted that the panic message contains
    /// the given `expected_message` as a substring.
    fn panics_with_message_containing<M: Borrow<str>>(self, expected_message_part: M);

    /// Runs the tested function and asserts that it panicked, i.e. the test will fail if the
    /// function terminated normally. In addition, it is asserted that the panic message matches the
    /// provided `predicate`.
    fn panics_with_message_matching<P: FnOnce(&str) -> bool>(self, predicate: P);
}

fn to_message(error: Box<dyn Any + Send>) -> Option<String> {
    if let Some(s) = error.downcast_ref::<&'static str>() {
        Some((*s).to_owned())
    }
    else if let Some(s) = error.downcast_ref::<String>() {
        Some(s.clone())
    }
    else {
        None
    }
}

fn assert_panics_with_message_matching_predicate<R, F, S, P>(
    assert_that: AssertThat<F>, expected_it: S, predicate: P)
where
    F: FnOnce() -> R + UnwindSafe,
    S: Into<String>,
    P: FnOnce(&str) -> bool
{
    let failure = Failure::from_expression(&assert_that.expression)
        .expected_it(expected_it);

    match catch_unwind(assert_that.data).map_err(to_message) {
        Ok(_) => failure.but_it("did not panic").fail(),
        Err(None) => failure.but_it("panicked without decodable message").fail(),
        Err(Some(msg)) if !predicate(&msg) =>
            failure.but_it(format!("panicked with message <{}>", &msg)).fail(),
        _ => { }
    }
}

impl<R, F: FnOnce() -> R + UnwindSafe> PanicAssertions for AssertThat<F> {
    fn panics(self) {
        if let Ok(_) = catch_unwind(self.data) {
            Failure::from_expression(&self.expression)
                .expected_it("to panic")
                .but_it("did not panic")
                .fail();
        }
    }

    fn does_not_panic(self) {
        if let Err(error) = catch_unwind(self.data) {
            let failure = Failure::from_expression(&self.expression)
                .expected_it("not to panic");

            if let Some(msg) = to_message(error) {
                failure.but_it(format!("panicked with message <{}>", msg)).fail();
            }
            else {
                failure.but_it("panicked").fail();
            }
        }
    }

    fn panics_with_message<M: Borrow<str>>(self, expected_message: M) {
        let expected_message = expected_message.borrow();
        let expected_it = format!("to panic with message <{}>", expected_message);

        assert_panics_with_message_matching_predicate(
            self, expected_it, |msg| msg == expected_message);
    }

    fn panics_with_message_containing<M: Borrow<str>>(self, expected_message_part: M) {
        let expected_message_part = expected_message_part.borrow();
        let expected_it = format!("to panic with message containing <{}>", expected_message_part);

        assert_panics_with_message_matching_predicate(
            self, expected_it, |msg| msg.contains(expected_message_part));
    }

    fn panics_with_message_matching<P: FnOnce(&str) -> bool>(self, predicate: P) {
        assert_panics_with_message_matching_predicate(
            self, "to panic with message matching predicate", predicate);
    }
}

#[cfg(test)]
mod tests {

    use crate::assert_that;

    use super::*;

    #[test]
    fn panics_passes_with_panicking_function() {
        assert_that!(|| panic!("hello")).panics();
    }

    #[test]
    #[should_panic(expected = "expected: <|| 1> to panic\nbut:      it did not panic")]
    fn panic_fails_with_non_panicking_function() {
        assert_that!(|| 1).panics();
    }

    #[test]
    fn does_not_panic_passes_with_non_panicking_function() {
        assert_that!(|| 1).does_not_panic();
    }

    #[test]
    #[should_panic(expected = "expected: <|| panic!(\"hello\")> not to panic\nbut:      it \
        panicked with message <hello>")]
    fn does_not_panic_fails_with_panicking_function() {
        assert_that!(|| panic!("hello")).does_not_panic();
    }

    #[test]
    fn panics_with_message_passes_with_panicking_function_and_correct_message() {
        assert_that!(|| panic!("hello")).panics_with_message("hello");
    }

    #[test]
    #[should_panic(expected = "expected: <|| panic!(\"hello\")> to panic with message \
        <henlo>\nbut:      it panicked with message <hello>")]
    fn panics_with_message_fails_with_panicking_function_and_wrong_message() {
        assert_that!(|| panic!("hello")).panics_with_message("henlo");
    }

    #[test]
    #[should_panic(expected = "expected: <|| 1> to panic with message <hello>\nbut:      it did \
        not panic")]
    fn panics_with_message_fails_with_non_panicking_function() {
        assert_that!(|| 1).panics_with_message("hello");
    }

    #[test]
    fn panics_with_message_containing_passes_with_complete_message() {
        assert_that!(|| panic!("hello")).panics_with_message_containing("hello");
    }

    #[test]
    fn panics_with_message_containing_passes_with_partial_message() {
        assert_that!(|| panic!("hello")).panics_with_message_containing("el");
    }

    #[test]
    #[should_panic(expected = "expected: <|| 1> to panic with message containing \
        <hello>\nbut:      it did not panic")]
    fn panics_with_message_containing_fails_with_non_panicking_function() {
        assert_that!(|| 1).panics_with_message_containing("hello");
    }

    #[test]
    #[should_panic(expected = "expected: <|| panic!(\"hello\")> to panic with message containing \
        <en>\nbut:      it panicked with message <hello>")]
    fn panics_with_message_containing_fails_with_message_which_does_not_contain_part() {
        assert_that!(|| panic!("hello")).panics_with_message_containing("en");
    }

    #[test]
    fn panics_with_message_matching_passes_with_message_matching_predicate() {
        assert_that!(|| panic!("hello")).panics_with_message_matching(|m| m.len() == 5);
    }

    #[test]
    #[should_panic(expected = "expected: <|| 1> to panic with message matching \
        predicate\nbut:      it did not panic")]
    fn panics_with_message_matching_fails_with_non_panicking_function() {
        assert_that!(|| 1).panics_with_message_matching(|m| m.len() == 5);
    }

    #[test]
    #[should_panic(expected = "expected: <|| panic!(\"hello!\")> to panic with message matching \
        predicate\nbut:      it panicked with message <hello!>")]
    fn panics_with_message_matching_fails_with_message_not_matching_predicate() {
        assert_that!(|| panic!("hello!")).panics_with_message_matching(|m| m.len() == 5);
    }
}
