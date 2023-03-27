use crate::{AssertThat, Failure};

// TODO use Pattern as soon as it is stable (https://github.com/rust-lang/rust/issues/27721)

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with a
/// [String] argument. This trait defines relations between strings such as substrings, prefixes,
/// and suffixes.
///
/// Example:
///
/// ```
/// use kernal::prelude::*;
///
/// assert_that!("I like trains").starts_with("I like").does_not_contain("cars");
/// ```
pub trait StringPatternAssertions {

    /// Asserts that the tested string contains the given `substring`, i.e. some slice of the tested
    /// string is equal to the substring.
    fn contains<S: AsRef<str>>(self, substring: S) -> Self;

    /// Asserts that the tested string does not contain the given `substring`, i.e. no slice of the
    /// tested string is equal to the substring.
    fn does_not_contain<S: AsRef<str>>(self, substring: S) -> Self;

    /// Asserts that the tested string contains a prefix that is equal to the given `prefix`, i.e.
    /// the slice of the tested string that contains the first `prefix.len()` characters is equal to
    /// `prefix`. If the tested string is shorter than the prefix, the assertion fails.
    fn starts_with<S: AsRef<str>>(self, prefix: S) -> Self;

    /// Asserts that the tested string does not contain a prefix that is equal to the given
    /// `prefix`, i.e. the slice of the tested string that contains the first `prefix.len()`
    /// characters is different from `prefix`. If the tested string is shorter than the prefix, the
    /// assertion passes trivially.
    fn does_not_start_with<S: AsRef<str>>(self, prefix: S) -> Self;

    /// Asserts that the tested string contains a suffix that is equal to the given `suffix`, i.e.
    /// the slice of the tested string that contains the last `suffix.len()` characters is equal to
    /// `suffix`. If the tested string is shorter than the suffix, the assertion fails.
    fn ends_with<S: AsRef<str>>(self, suffix: S) -> Self;

    /// Asserts that the tested string does not contain a suffix that is equal to the given
    /// `suffix`, i.e. the slice of the tested string that contains the last `suffix.len()`
    /// characters is different from suffix`. If the tested string is shorter than the suffix, the
    /// assertion fails trivially.
    fn does_not_end_with<S: AsRef<str>>(self, suffix: S) -> Self;
}

impl<T: AsRef<str>> StringPatternAssertions for AssertThat<T> {

    fn contains<S: AsRef<str>>(self, substring: S) -> Self {
        let string = self.data.as_ref();
        let substring = substring.as_ref();

        if !string.contains(substring) {
            Failure::new(&self)
                .expected_it(format!("to contain <{}>", substring.escape_debug()))
                .but_it(format!("was <{}>", string.escape_debug()))
                .fail();
        }

        self
    }

    fn does_not_contain<S: AsRef<str>>(self, substring: S) -> Self {
        let string = self.data.as_ref();
        let substring = substring.as_ref();

        if let Some(byte_index) = string.find(substring) {
            let highlighted = format!("{}[{}]{}",
                &string[..byte_index], substring, &string[(byte_index + substring.len())..]);

            Failure::new(&self)
                .expected_it(format!("not to contain <{}>", substring.escape_debug()))
                .but_it(format!("was <{}>", highlighted.escape_debug()))
                .fail();
        }

        self
    }

    fn starts_with<S: AsRef<str>>(self, prefix: S) -> Self {
        let string = self.data.as_ref();
        let prefix = prefix.as_ref();

        if !string.starts_with(prefix) {
            Failure::new(&self)
                .expected_it(format!("to start with <{}>", prefix.escape_debug()))
                .but_it(format!("was <{}>", string.escape_debug()))
                .fail();
        }

        self
    }

    fn does_not_start_with<S: AsRef<str>>(self, prefix: S) -> Self {
        let string = self.data.as_ref();
        let prefix = prefix.as_ref();

        if let Some(string_without_prefix) = string.strip_prefix(prefix) {
            let highlighted = format!("[{}]{}", prefix, string_without_prefix);

            Failure::new(&self)
                .expected_it(format!("not to start with <{}>", prefix.escape_debug()))
                .but_it(format!("was <{}>", highlighted.escape_debug()))
                .fail();
        }

        self
    }

    fn ends_with<S: AsRef<str>>(self, suffix: S) -> Self {
        let string = self.data.as_ref();
        let suffix = suffix.as_ref();

        if !string.ends_with(suffix) {
            Failure::new(&self)
                .expected_it(format!("to end with <{}>", suffix.escape_debug()))
                .but_it(format!("was <{}>", string.escape_debug()))
                .fail();
        }

        self
    }

    fn does_not_end_with<S: AsRef<str>>(self, suffix: S) -> Self {
        let string = self.data.as_ref();
        let suffix = suffix.as_ref();

        if let Some(string_without_suffix) = string.strip_suffix(suffix) {
            let highlighted = format!("{}[{}]", string_without_suffix, suffix);

            Failure::new(&self)
                .expected_it(format!("not to end with <{}>", suffix.escape_debug()))
                .but_it(format!("was <{}>", highlighted.escape_debug()))
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
    fn contains_passes_for_two_empty_strings() {
        assert_that!("").contains("");
    }

    #[test]
    fn contains_passes_for_two_equal_strings() {
        assert_that!("a string").contains("a string");
    }

    #[test]
    fn contains_passes_for_inner_string() {
        assert_that!("a string").contains("str");
    }

    #[test]
    fn contains_fails_for_non_contained_string() {
        assert_fails!(("a string").contains("."),
            expected it "to contain <.>"
            but it "was <a string>");
    }

    #[test]
    fn does_not_contain_passes_for_two_empty_strings() {
        assert_fails!(("").does_not_contain(""), expected it "not to contain <>" but it "was <[]>");
    }

    #[test]
    fn does_not_contain_passes_for_two_equal_strings() {
        assert_fails!(("a string").does_not_contain("a string"),
            expected it "not to contain <a string>"
            but it "was <[a string]>");
    }

    #[test]
    fn does_not_contain_passes_for_inner_string() {
        assert_fails!(("a string").does_not_contain("str"),
            expected it "not to contain <str>"
            but it "was <a [str]ing>");
    }

    #[test]
    fn does_not_contain_fails_for_non_contained_string() {
        assert_that!("a string").does_not_contain(".");
    }

    #[test]
    fn starts_with_passes_for_empty_string() {
        assert_that!("a string").starts_with("");
    }

    #[test]
    fn starts_with_passes_for_entire_string() {
        assert_that!("a string").starts_with("a string");
    }

    #[test]
    fn starts_with_passes_for_prefix() {
        assert_that!("a string").starts_with("a s");
    }

    #[test]
    fn starts_with_fails_for_unrelated_string() {
        assert_fails!(("a string").starts_with("hello"),
            expected it "to start with <hello>"
            but it "was <a string>");
    }

    #[test]
    fn starts_with_fails_for_suffix() {
        assert_fails!(("a string").starts_with("ing"),
            expected it "to start with <ing>"
            but it "was <a string>");
    }

    #[test]
    fn does_not_start_with_passes_for_unrelated_string() {
        assert_that!("a string").does_not_start_with("hello");
    }

    #[test]
    fn does_not_start_with_passes_for_suffix() {
        assert_that!("a string").does_not_start_with("ing");
    }

    #[test]
    fn does_not_start_with_fails_for_empty_string() {
        assert_fails!(("a string").does_not_start_with(""),
            expected it "not to start with <>"
            but it "was <[]a string>");
    }

    #[test]
    fn does_not_start_with_fails_for_entire_string() {
        assert_fails!(("a string").does_not_start_with("a string"),
            expected it "not to start with <a string>"
            but it "was <[a string]>");
    }

    #[test]
    fn does_not_start_with_fails_for_prefix() {
        assert_fails!(("a string").does_not_start_with("a s"),
            expected it "not to start with <a s>"
            but it "was <[a s]tring>");
    }

    #[test]
    fn ends_with_passes_for_empty_string() {
        assert_that!("a string").ends_with("");
    }

    #[test]
    fn ends_with_passes_for_entire_string() {
        assert_that!("a string").ends_with("a string");
    }

    #[test]
    fn ends_with_passes_for_suffix() {
        assert_that!("a string").ends_with("ing");
    }

    #[test]
    fn ends_with_fails_for_unrelated_string() {
        assert_fails!(("a string").ends_with("hello"),
            expected it "to end with <hello>"
            but it "was <a string>");
    }

    #[test]
    fn ends_with_fails_for_prefix() {
        assert_fails!(("a string").ends_with("a s"),
            expected it "to end with <a s>"
            but it "was <a string>");
    }

    #[test]
    fn does_not_end_with_passes_for_unrelated_string() {
        assert_that!("a string").does_not_end_with("hello");
    }

    #[test]
    fn does_not_end_with_passes_for_prefix() {
        assert_that!("a string").does_not_end_with("a s");
    }

    #[test]
    fn does_not_end_with_fails_for_empty_string() {
        assert_fails!(("a string").does_not_end_with(""),
            expected it "not to end with <>"
            but it "was <a string[]>");
    }

    #[test]
    fn does_not_end_with_fails_for_entire_string() {
        assert_fails!(("a string").does_not_end_with("a string"),
            expected it "not to end with <a string>"
            but it "was <[a string]>");
    }

    #[test]
    fn does_not_end_with_fails_for_suffix() {
        assert_fails!(("a string").does_not_end_with("ing"),
            expected it "not to end with <ing>"
            but it "was <a str[ing]>");
    }
}
