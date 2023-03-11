use std::panic::UnwindSafe;

use crate::{assert_that, Failure};
use crate::panic::PanicAssertions;

pub(crate) fn assert_fails_do<R, F: FnOnce() -> R + UnwindSafe>(
        assertion: F, expression: &str, expected_it: &str, but_it: impl Into<String>) {
    let expected_message = Failure::from_expression(expression)
        .expected_it(expected_it)
        .but_it(but_it)
        .message();

    assert_that!(assertion).panics_with_message(expected_message);
}

#[macro_export]
macro_rules! assert_fails {
    (( $input:expr ) . $assertion:ident ( $( $expected:expr ),* ),
            expected it $expected_it:tt but it $but_it:tt) => {
        $crate::test_util::assert_fails_do(
            || $crate::assert_that!($input).$assertion($( $expected, )*),
            stringify!($input),
            $expected_it,
            $but_it);
    }
}
