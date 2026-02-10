use std::panic::UnwindSafe;

use crate::panic::PanicAssertions;
use crate::{Failure, assert_that};

pub(crate) fn assert_fails_do<F: FnOnce() -> () + UnwindSafe>(
    assertion: F,
    expression: &str,
    expected_it: impl Into<String>,
    but_it: impl Into<String>,
) {
    let expected_message = Failure::from_expression(expression)
        .expected_it(expected_it)
        .but_it(but_it)
        .message();

    assert_that!(assertion).panics_with_message(expected_message);
}

/// Utility-macro to compactly write tests for failing assertions. As an example, consider the
/// following assertion.
///
/// ```norun
/// assert_that!(1).is_equal_to(2);
/// ```
///
/// To test that this assertion fails with the correct message, we would use this macro as follows.
///
/// ```norun
/// assert_fails!((1).is_equal_to(2),
///   expected it "to equal <2>"
///   but it "was <1>");
/// ```
///
/// # Arguments
///
/// * $input: The expression tested by the assertion which is expected to fail. Put inside
///   parentheses to ensure it is isolated from the rest (`.` would otherwise be interpreted as part
///   of the expression). In the example, this would be `1`.
/// * $assertion: The identifier of the assertion-method to test. In the example, this would be
///   `is_equal_to`.
/// * args: A parameter list to supply to the assertion expected to fail. In the example, this would
///   be `2`
/// * $expected_it: A string literal/parenthesized expression containing the expected part of the
///   error message that comes after `expected: <...> `. The first part of this line is asserted to
///   be as the `Failure` struct defines, with appropriate expression text. In the example, this
///   would be `"to equal <2>"`.
/// * $but_it: A string literal/parenthesized expression containing the expected part of the error
///   message that comes after `but:      it <...> `. In the example, this would be `"was <1>"`.
#[macro_export]
macro_rules! assert_fails {
    (( $input:expr ) . $assertion:ident ( $( $args:expr ),* ),
            expected it $expected_it:tt but it $but_it:tt) => {
        #[allow(unused_parens)]
        $crate::test_util::assert_fails_do(
            || { $crate::assert_that!($input).$assertion($( $args, )*); },
            stringify!($input),
            $expected_it,
            $but_it);
    }
}

mod tests {

    use crate::prelude::*;

    #[test]
    fn assert_fails_works_for_failing_assertion() {
        assert_fails!((1).is_equal_to(2), expected it "to equal <2>" but it "was <1>");
    }

    #[test]
    #[should_panic]
    fn assert_fails_panics_for_passing_assertion() {
        assert_fails!((1).is_equal_to(1), expected it "to equal <1>" but it "was <1>");
    }

    #[test]
    #[should_panic]
    fn assert_fails_panics_for_wrong_expected_it_message() {
        assert_fails!((1).is_equal_to(2), expected it "to equal <3>" but it "was <1>");
    }

    #[test]
    #[should_panic]
    fn assert_fails_panics_for_wrong_but_it_message() {
        assert_fails!((1).is_equal_to(2), expected it "to equal <2>" but it "was <3>");
    }
}
