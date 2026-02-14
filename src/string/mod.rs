//! Contains assertions for string values, including among others [String] and references to [str].
//! See [StringAssertions] for more details.

pub mod pattern;

use crate::{AssertThat, Failure};

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with a
/// [String] argument. This trait contains basic assertions on the string itself and individual
/// characters. For comparing strings (such as contains, prefix, and suffix relations), see
/// [StringPatternAssertions](pattern::StringPatternAssertions).
///
/// Examples:
///
/// ```
/// use kernal::prelude::*;
///
/// assert_that!("hello world!")
///     .is_not_empty()
///     .has_char_length(12)
///     .has_byte_length_less_than(15)
///     .contains_whitespace()
///     .does_not_contain_uppercase_letters()
///     .is_trimmed();
/// ```
pub trait StringAssertions {
    /// Asserts that the tested string is empty, i.e. contains no characters.
    fn is_empty(self) -> Self;

    /// Asserts that the tested string is not empty, i.e. contains at least one character.
    fn is_not_empty(self) -> Self;

    /// Asserts that the number of characters in the tested string is equal to the given
    /// `expected_length`.
    fn has_char_length(self, expected_length: usize) -> Self;

    /// Asserts that the number of characters in the tested string is less than the given
    /// `length_bound`.
    fn has_char_length_less_than(self, length_bound: usize) -> Self;

    /// Asserts that the number of characters in the tested string is less than or equal to the
    /// given `length_bound`.
    fn has_char_length_less_than_or_equal_to(self, length_bound: usize) -> Self;

    /// Asserts that the number of characters in the tested string is greater than the given
    /// `length_bound`.
    fn has_char_length_greater_than(self, length_bound: usize) -> Self;

    /// Asserts that the number of characters in the tested string is greater than or equal to the
    /// given `length_bound`.
    fn has_char_length_greater_than_or_equal_to(self, length_bound: usize) -> Self;

    /// Asserts that the number of characters in the tested string is different to the given
    /// `unexpected_length`.
    fn has_char_length_different_to(self, unexpected_length: usize) -> Self;

    /// Asserts that the number of bytes composing the tested string is equal to the given
    /// `expected_length`.
    fn has_byte_length(self, expected_length: usize) -> Self;

    /// Asserts that the number of bytes composing the tested string is less than the given
    /// `length_bound`.
    fn has_byte_length_less_than(self, length_bound: usize) -> Self;

    /// Asserts that the number of bytes composing the tested string is less than or equal to the
    /// given `length_bound`.
    fn has_byte_length_less_than_or_equal_to(self, length_bound: usize) -> Self;

    /// Asserts that the number of bytes composing the tested string is greater than the given
    /// `length_bound`.
    fn has_byte_length_greater_than(self, length_bound: usize) -> Self;

    /// Asserts that the number of bytes composing the tested string is greater than or equal to
    /// the given `length_bound`.
    fn has_byte_length_greater_than_or_equal_to(self, length_bound: usize) -> Self;

    /// Asserts that the number of bytes composing the tested string is different to the given
    /// `unexpected_length`.
    fn has_byte_length_different_to(self, unexpected_length: usize) -> Self;

    /// Asserts that the tested string contains at least one character which is classified as
    /// whitespace according to [char::is_whitespace].
    fn contains_whitespace(self) -> Self;

    /// Asserts that the tested string contains no character which is classified as whitespace
    /// according to [char::is_whitespace].
    fn does_not_contain_whitespace(self) -> Self;

    /// Asserts that the tested string contains at least one character which is classified as
    /// alphabetic according to [char::is_alphabetic].
    fn contains_alphabetic_characters(self) -> Self;

    /// Asserts that the tested string contains no character which is classified as alphabetic
    /// according to [char::is_alphabetic].
    fn does_not_contain_alphabetic_characters(self) -> Self;

    /// Asserts that the tested string contains at least one character which is classified as
    /// numeric according to [char::is_numeric].
    fn contains_numeric_characters(self) -> Self;

    /// Asserts that the tested string contains no character which is classified as numeric
    /// according to [char::is_numeric].
    fn does_not_contain_numeric_characters(self) -> Self;

    /// Asserts that the tested string contains at least one character which is classified as
    /// alphanumeric according to [char::is_alphanumeric].
    fn contains_alphanumeric_characters(self) -> Self;

    /// Asserts that the tested string contains no character which is classified as alphanumeric
    /// according to [char::is_alphanumeric].
    fn does_not_contain_alphanumeric_characters(self) -> Self;

    /// Asserts that the tested string contains at least one character which is classified as an
    /// uppercase letter according to [char::is_uppercase].
    fn contains_uppercase_letters(self) -> Self;

    /// Asserts that the tested string contains no character which is classified as an uppercase
    /// letter according to [char::is_uppercase].
    fn does_not_contain_uppercase_letters(self) -> Self;

    /// Asserts that the tested string contains at least one character which is classified as a
    /// lowercase letter according to [char::is_lowercase].
    fn contains_lowercase_letters(self) -> Self;

    /// Asserts that the tested string contains no character which is classified as a lowercase
    /// letter according to [char::is_lowercase].
    fn does_not_contain_lowercase_letters(self) -> Self;

    /// Asserts that the tested string contains at least one character which is classified as a
    /// control character according to [char::is_control].
    fn contains_control_characters(self) -> Self;

    /// Asserts that the tested string contains no character which is classified as a control
    /// character according to [char::is_control].
    fn does_not_contain_control_characters(self) -> Self;

    /// Asserts that the tested string is trimmed, i.e. does not start and does not end with
    /// whitespace.
    fn is_trimmed(self) -> Self;

    /// Asserts that the tested string is not trimmed, i.e. starts or ends with whitespace.
    fn is_not_trimmed(self) -> Self;

    /// Asserts that the tested string is pure ASCII, i.e. contains no non-ASCII characters
    /// according to [char::is_ascii].
    fn is_ascii(self) -> Self;

    /// Asserts that the tested string is not pure ASCII, i.e. contains at least one non-ASCII
    /// character according to [char::is_ascii].
    fn is_not_ascii(self) -> Self;

    /// Converts the tested string to a [Vec] of the [char]s contained in it and allows assertions
    /// on them.
    fn to_chars(self) -> AssertThat<Vec<char>>;

    /// Converts the tested string to a [Vec] of the bytes ([u8]) contained in it and allows
    /// assertions on them.
    fn to_bytes(self) -> AssertThat<Vec<u8>>;
}

fn assert_length_matches<T, P>(
    assert_that: AssertThat<T>,
    length: usize,
    length_predicate: P,
    length_kind: &str,
    comparison_kind: &str,
    reference_length: usize,
) -> AssertThat<T>
where
    T: AsRef<str>,
    P: Fn(usize) -> bool,
{
    if !length_predicate(length) {
        let description = if comparison_kind.is_empty() {
            length_kind.to_owned()
        }
        else {
            format!("{} {}", length_kind, comparison_kind)
        };

        Failure::new(&assert_that)
            .expected_it(format!("to have {} <{}>", description, reference_length))
            .but_it(format!("had {} <{}>", length_kind, length))
            .fail();
    }

    assert_that
}

fn assert_char_length_matches<T, P>(
    assert_that: AssertThat<T>,
    length_predicate: P,
    comparison_kind: &str,
    reference_length: usize,
) -> AssertThat<T>
where
    T: AsRef<str>,
    P: Fn(usize) -> bool,
{
    let length = assert_that.data.as_ref().chars().count();

    assert_length_matches(
        assert_that,
        length,
        length_predicate,
        "char length",
        comparison_kind,
        reference_length,
    )
}

fn assert_byte_length_matches<T, P>(
    assert_that: AssertThat<T>,
    length_predicate: P,
    comparison_kind: &str,
    reference_length: usize,
) -> AssertThat<T>
where
    T: AsRef<str>,
    P: Fn(usize) -> bool,
{
    let length = assert_that.data.as_ref().len();

    assert_length_matches(
        assert_that,
        length,
        length_predicate,
        "byte length",
        comparison_kind,
        reference_length,
    )
}

fn assert_contains_characters_matching<T, P>(
    assert_that: AssertThat<T>,
    char_predicate: P,
    expected_it: &str,
) -> AssertThat<T>
where
    T: AsRef<str>,
    P: Fn(char) -> bool,
{
    let string = assert_that.data.as_ref();

    if !string.chars().any(char_predicate) {
        Failure::new(&assert_that)
            .expected_it(expected_it)
            .but_it(format!("was <{}>", string.escape_debug()))
            .fail();
    }

    assert_that
}

fn highlight_char(input: &str, byte_index: usize) -> String {
    // The first byte of an UTF-8 character is of the form 0... for one-byte-characters,
    // 110... for two-byte-characters, 1110... for three-byte-characters,
    // and 11110... for four-byte-characters.

    let first_byte = input.as_bytes()[byte_index];
    let char_size = first_byte.leading_ones().saturating_sub(1) as usize + 1;

    format!(
        "{}[{}]{}",
        input[..byte_index].escape_debug(),
        input[byte_index..(byte_index + char_size)].escape_debug(),
        input[(byte_index + char_size)..].escape_debug()
    )
}

fn assert_does_not_contain_characters_matching<T, P>(
    assert_that: AssertThat<T>,
    char_predicate: P,
    expected_it: &str,
) -> AssertThat<T>
where
    T: AsRef<str>,
    P: Fn(char) -> bool,
{
    let string = assert_that.data.as_ref();

    if let Some(byte_index) = string.find(char_predicate) {
        Failure::new(&assert_that)
            .expected_it(expected_it)
            .but_it(format!("was <{}>", highlight_char(string, byte_index)))
            .fail();
    }

    assert_that
}

impl<T: AsRef<str>> StringAssertions for AssertThat<T> {
    fn is_empty(self) -> Self {
        let data = self.data.as_ref();

        if !data.is_empty() {
            Failure::new(&self)
                .expected_it("to be empty")
                .but_it(format!("was <{}>", data.escape_debug()))
                .fail();
        }

        self
    }

    fn is_not_empty(self) -> Self {
        let data = self.data.as_ref();

        if data.is_empty() {
            Failure::new(&self)
                .expected_it("not to be empty")
                .but_it("was")
                .fail();
        }

        self
    }

    fn has_char_length(self, expected_length: usize) -> Self {
        assert_char_length_matches(
            self,
            |length| length == expected_length,
            "",
            expected_length,
        )
    }

    fn has_char_length_less_than(self, length_bound: usize) -> Self {
        assert_char_length_matches(
            self,
            |length| length < length_bound,
            "less than",
            length_bound,
        )
    }

    fn has_char_length_less_than_or_equal_to(self, length_bound: usize) -> Self {
        assert_char_length_matches(
            self,
            |length| length <= length_bound,
            "less than or equal to",
            length_bound,
        )
    }

    fn has_char_length_greater_than(self, length_bound: usize) -> Self {
        assert_char_length_matches(
            self,
            |length| length > length_bound,
            "greater than",
            length_bound,
        )
    }

    fn has_char_length_greater_than_or_equal_to(self, length_bound: usize) -> Self {
        assert_char_length_matches(
            self,
            |length| length >= length_bound,
            "greater than or equal to",
            length_bound,
        )
    }

    fn has_char_length_different_to(self, unexpected_length: usize) -> Self {
        assert_char_length_matches(
            self,
            |length| length != unexpected_length,
            "different to",
            unexpected_length,
        )
    }

    fn has_byte_length(self, expected_length: usize) -> Self {
        assert_byte_length_matches(
            self,
            |length| length == expected_length,
            "",
            expected_length,
        )
    }

    fn has_byte_length_less_than(self, length_bound: usize) -> Self {
        assert_byte_length_matches(
            self,
            |length| length < length_bound,
            "less than",
            length_bound,
        )
    }

    fn has_byte_length_less_than_or_equal_to(self, length_bound: usize) -> Self {
        assert_byte_length_matches(
            self,
            |length| length <= length_bound,
            "less than or equal to",
            length_bound,
        )
    }

    fn has_byte_length_greater_than(self, length_bound: usize) -> Self {
        assert_byte_length_matches(
            self,
            |length| length > length_bound,
            "greater than",
            length_bound,
        )
    }

    fn has_byte_length_greater_than_or_equal_to(self, length_bound: usize) -> Self {
        assert_byte_length_matches(
            self,
            |length| length >= length_bound,
            "greater than or equal to",
            length_bound,
        )
    }

    fn has_byte_length_different_to(self, unexpected_length: usize) -> Self {
        assert_byte_length_matches(
            self,
            |length| length != unexpected_length,
            "different to",
            unexpected_length,
        )
    }

    fn contains_whitespace(self) -> Self {
        assert_contains_characters_matching(self, char::is_whitespace, "to contain whitespace")
    }

    fn does_not_contain_whitespace(self) -> Self {
        assert_does_not_contain_characters_matching(
            self,
            char::is_whitespace,
            "not to contain whitespace",
        )
    }

    fn contains_alphabetic_characters(self) -> Self {
        assert_contains_characters_matching(
            self,
            char::is_alphabetic,
            "to contain alphabetic characters",
        )
    }

    fn does_not_contain_alphabetic_characters(self) -> Self {
        assert_does_not_contain_characters_matching(
            self,
            char::is_alphabetic,
            "not to contain alphabetic characters",
        )
    }

    fn contains_numeric_characters(self) -> Self {
        assert_contains_characters_matching(self, char::is_numeric, "to contain numeric characters")
    }

    fn does_not_contain_numeric_characters(self) -> Self {
        assert_does_not_contain_characters_matching(
            self,
            char::is_numeric,
            "not to contain numeric characters",
        )
    }

    fn contains_alphanumeric_characters(self) -> Self {
        assert_contains_characters_matching(
            self,
            char::is_alphanumeric,
            "to contain alphanumeric characters",
        )
    }

    fn does_not_contain_alphanumeric_characters(self) -> Self {
        assert_does_not_contain_characters_matching(
            self,
            char::is_alphanumeric,
            "not to contain alphanumeric characters",
        )
    }

    fn contains_uppercase_letters(self) -> Self {
        assert_contains_characters_matching(
            self,
            char::is_uppercase,
            "to contain uppercase letters",
        )
    }

    fn does_not_contain_uppercase_letters(self) -> Self {
        assert_does_not_contain_characters_matching(
            self,
            char::is_uppercase,
            "not to contain uppercase letters",
        )
    }

    fn contains_lowercase_letters(self) -> Self {
        assert_contains_characters_matching(
            self,
            char::is_lowercase,
            "to contain lowercase letters",
        )
    }

    fn does_not_contain_lowercase_letters(self) -> Self {
        assert_does_not_contain_characters_matching(
            self,
            char::is_lowercase,
            "not to contain lowercase letters",
        )
    }

    fn contains_control_characters(self) -> Self {
        assert_contains_characters_matching(self, char::is_control, "to contain control characters")
    }

    fn does_not_contain_control_characters(self) -> Self {
        assert_does_not_contain_characters_matching(
            self,
            char::is_control,
            "not to contain control characters",
        )
    }

    fn is_trimmed(self) -> Self {
        let string = self.data.as_ref();
        let counter_example = string
            .chars()
            .next()
            .filter(|&character| character.is_whitespace())
            .map(|_| 0)
            .or_else(|| {
                string
                    .char_indices()
                    .last()
                    .filter(|(_, character)| character.is_whitespace())
                    .map(|(index, _)| index)
            });

        if let Some(byte_index) = counter_example {
            Failure::new(&self)
                .expected_it("to be trimmed")
                .but_it(format!("was <{}>", highlight_char(string, byte_index)))
                .fail();
        }

        self
    }

    fn is_not_trimmed(self) -> Self {
        let string = self.data.as_ref();

        if string.trim().len() == string.len() {
            Failure::new(&self)
                .expected_it("not to be trimmed")
                .but_it(format!("was <{}>", string.escape_debug()))
                .fail();
        }

        self
    }

    fn is_ascii(self) -> Self {
        assert_does_not_contain_characters_matching(
            self,
            |c| !c.is_ascii(),
            "to be an ASCII string",
        )
    }

    fn is_not_ascii(self) -> Self {
        assert_contains_characters_matching(self, |c| !c.is_ascii(), "not to be an ASCII string")
    }

    fn to_chars(self) -> AssertThat<Vec<char>> {
        let data = self.data.as_ref().chars().collect();
        let expression = format!("chars of <{}>", self.expression);

        AssertThat::new(data, expression)
    }

    fn to_bytes(self) -> AssertThat<Vec<u8>> {
        let data = self.data.as_ref().bytes().collect();
        let expression = format!("bytes of <{}>", self.expression);

        AssertThat::new(data, expression)
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::{assert_fails, assert_that};

    #[test]
    fn is_empty_passes_for_empty_string() {
        assert_that!(String::new()).is_empty();
    }

    #[test]
    fn is_empty_fails_for_abc() {
        assert_fails!(("abc").is_empty(), expected it "to be empty" but it "was <abc>");
    }

    #[test]
    fn is_not_empty_passes_for_abc() {
        assert_that!("abc").is_not_empty();
    }

    #[test]
    fn is_not_empty_fails_for_empty_string() {
        let empty = String::new();

        assert_fails!((&empty).is_not_empty(), expected it "not to be empty" but it "was");
    }

    #[test]
    fn has_char_length_passes_for_empty_string_and_0() {
        assert_that!("").has_char_length(0);
    }

    #[test]
    fn has_char_length_passes_for_abc_and_3() {
        assert_that!("abc").has_char_length(3);
    }

    #[test]
    fn has_char_length_fails_for_empty_string_and_1() {
        assert_fails!(("").has_char_length(1),
            expected it "to have char length <1>"
            but it "had char length <0>");
    }

    #[test]
    fn has_char_length_fails_for_abc_and_2() {
        assert_fails!(("abc").has_char_length(2),
            expected it "to have char length <2>"
            but it "had char length <3>");
    }

    #[test]
    fn has_char_length_less_than_passes_for_empty_string_and_1() {
        assert_that!("").has_char_length_less_than(1);
    }

    #[test]
    fn has_char_length_less_than_fails_for_abc_and_3() {
        assert_fails!(("abc").has_char_length_less_than(3),
            expected it "to have char length less than <3>"
            but it "had char length <3>");
    }

    #[test]
    fn has_char_length_less_than_fails_for_abcde_and_4() {
        assert_fails!(("abcde").has_char_length_less_than(4),
            expected it "to have char length less than <4>"
            but it "had char length <5>");
    }

    #[test]
    fn has_char_length_less_than_or_equal_to_passes_for_empty_string_and_1() {
        assert_that!("").has_char_length_less_than_or_equal_to(1);
    }

    #[test]
    fn has_char_length_less_than_or_equal_to_passes_for_abc_and_3() {
        assert_that!("abc").has_char_length_less_than_or_equal_to(3);
    }

    #[test]
    fn has_char_length_less_than_or_equal_to_fails_for_abcde_and_4() {
        assert_fails!(("abcde").has_char_length_less_than_or_equal_to(4),
            expected it "to have char length less than or equal to <4>"
            but it "had char length <5>");
    }

    #[test]
    fn has_char_length_greater_than_passes_for_abcde_and_4() {
        assert_that!("abcde").has_char_length_greater_than(4);
    }

    #[test]
    fn has_char_length_greater_than_fails_for_empty_string_and_1() {
        assert_fails!(("").has_char_length_greater_than(1),
            expected it "to have char length greater than <1>"
            but it "had char length <0>");
    }

    #[test]
    fn has_char_length_greater_than_fails_for_abc_and_3() {
        assert_fails!(("abc").has_char_length_greater_than(3),
            expected it "to have char length greater than <3>"
            but it "had char length <3>");
    }

    #[test]
    fn has_char_length_greater_than_or_equal_to_passes_for_abcde_and_4() {
        assert_that!("abcde").has_char_length_greater_than_or_equal_to(4);
    }

    #[test]
    fn has_char_length_greater_than_or_equal_to_passes_for_abc_and_3() {
        assert_that!("abc").has_char_length_greater_than_or_equal_to(3);
    }

    #[test]
    fn has_char_length_greater_than_or_equal_to_fails_for_empty_string_and_1() {
        assert_fails!(("").has_char_length_greater_than_or_equal_to(1),
            expected it "to have char length greater than or equal to <1>"
            but it "had char length <0>");
    }

    #[test]
    fn has_char_length_different_to_passes_for_empty_string_and_one() {
        assert_that!("").has_char_length_different_to(1);
    }

    #[test]
    fn has_char_length_different_to_passes_for_abcde_and_4() {
        assert_that!("abcde").has_char_length_different_to(4);
    }

    #[test]
    fn has_char_length_different_to_fails_for_abc_and_3() {
        assert_fails!(("abc").has_char_length_different_to(3),
            expected it "to have char length different to <3>"
            but it "had char length <3>");
    }

    #[test]
    fn has_byte_length_equal_to_passes_for_emoji_and_4() {
        assert_that!("🙂").has_byte_length(4);
    }

    #[test]
    fn has_byte_length_equal_to_fails_for_tuer_and_3() {
        assert_fails!(("tür").has_byte_length(3),
            expected it "to have byte length <3>"
            but it "had byte length <4>");
    }

    #[test]
    fn has_byte_length_equal_to_fails_for_apple_and_6() {
        assert_fails!(("apple").has_byte_length(6),
            expected it "to have byte length <6>"
            but it "had byte length <5>");
    }

    #[test]
    fn has_byte_length_less_than_passes_for_apple_and_6() {
        assert_that!("apple").has_byte_length_less_than(6);
    }

    #[test]
    fn has_byte_length_less_than_fails_for_emoji_and_4() {
        assert_fails!(("🙂").has_byte_length_less_than(4),
            expected it "to have byte length less than <4>"
            but it "had byte length <4>");
    }

    #[test]
    fn has_byte_length_less_than_fails_for_tuer_and_3() {
        assert_fails!(("tür").has_byte_length_less_than(3),
            expected it "to have byte length less than <3>"
            but it "had byte length <4>");
    }

    #[test]
    fn has_byte_length_less_than_or_equal_to_fails_for_emoji_and_4() {
        assert_that!("🙂").has_byte_length_less_than_or_equal_to(4);
    }

    #[test]
    fn has_byte_length_less_than_or_equal_to_fails_for_apple_and_6() {
        assert_that!("apple").has_byte_length_less_than_or_equal_to(6);
    }

    #[test]
    fn has_byte_length_less_than_or_equal_to_fails_for_tuer_and_3() {
        assert_fails!(("tür").has_byte_length_less_than_or_equal_to(3),
            expected it "to have byte length less than or equal to <3>"
            but it "had byte length <4>");
    }

    #[test]
    fn has_byte_length_greater_than_passes_for_tuer_and_3() {
        assert_that!("tür").has_byte_length_greater_than(3);
    }

    #[test]
    fn has_byte_length_greater_than_fails_for_emoji_and_4() {
        assert_fails!(("🙂").has_byte_length_greater_than(4),
            expected it "to have byte length greater than <4>"
            but it "had byte length <4>");
    }

    #[test]
    fn has_byte_length_greater_than_fails_for_apple_and_6() {
        assert_fails!(("apple").has_byte_length_greater_than(6),
            expected it "to have byte length greater than <6>"
            but it "had byte length <5>");
    }

    #[test]
    fn has_byte_length_greater_than_or_equal_to_passes_for_emoji_and_4() {
        assert_that!("🙂").has_byte_length_greater_than_or_equal_to(4);
    }

    #[test]
    fn has_byte_length_greater_than_or_equal_to_passes_for_tuer_and_3() {
        assert_that!("tür").has_byte_length_greater_than_or_equal_to(3);
    }

    #[test]
    fn has_byte_length_greater_than_or_equal_to_fails_for_apple_and_6() {
        assert_fails!(("apple").has_byte_length_greater_than_or_equal_to(6),
            expected it "to have byte length greater than or equal to <6>"
            but it "had byte length <5>");
    }

    #[test]
    fn has_byte_length_different_to_passes_for_tuer_and_3() {
        assert_that!("tür").has_byte_length_different_to(3);
    }

    #[test]
    fn has_byte_length_different_to_passes_for_apple_and_6() {
        assert_that!("apple").has_byte_length_different_to(6);
    }

    #[test]
    fn has_byte_length_different_to_fails_for_emoji_and_4() {
        assert_fails!(("🙂").has_byte_length_different_to(4),
            expected it "to have byte length different to <4>"
            but it "had byte length <4>");
    }

    #[test]
    fn contains_whitespace_passes_for_single_newline() {
        assert_that!("\n").contains_whitespace();
    }

    #[test]
    fn contains_whitespace_passes_for_space_separated_words() {
        assert_that!("hello world").contains_whitespace();
    }

    #[test]
    fn contains_whitespace_fails_for_empty_string() {
        assert_fails!(("").contains_whitespace(),
            expected it "to contain whitespace"
            but it "was <>");
    }

    #[test]
    fn contains_whitespace_fails_for_single_word() {
        assert_fails!(("banana").contains_whitespace(),
            expected it "to contain whitespace"
            but it "was <banana>");
    }

    #[test]
    fn does_not_contain_whitespace_passes_for_empty_string() {
        assert_that!("").does_not_contain_whitespace();
    }

    #[test]
    fn does_not_contain_whitespace_passes_for_single_word() {
        assert_that!("banana").does_not_contain_whitespace();
    }

    #[test]
    fn does_not_contain_whitespace_fails_for_single_newline() {
        assert_fails!(("\n").does_not_contain_whitespace(),
            expected it "not to contain whitespace"
            but it "was <[\\n]>");
    }

    #[test]
    fn does_not_contain_whitespace_fails_for_space_separated_words() {
        assert_fails!(("hello world").does_not_contain_whitespace(),
            expected it "not to contain whitespace"
            but it "was <hello[ ]world>");
    }

    #[test]
    fn contains_alphabetic_characters_passes_for_single_word() {
        assert_that!("Potatoes").contains_alphabetic_characters();
    }

    #[test]
    fn contains_alphabetic_characters_passes_for_later_letter() {
        assert_that!("2 * a").contains_alphabetic_characters();
    }

    #[test]
    fn contains_alphabetic_characters_fails_for_empty_string() {
        assert_fails!(("").contains_alphabetic_characters(),
            expected it "to contain alphabetic characters"
            but it "was <>");
    }

    #[test]
    fn contains_alphabetic_characters_fails_for_number() {
        assert_fails!(("1337").contains_alphabetic_characters(),
            expected it "to contain alphabetic characters"
            but it "was <1337>");
    }

    #[test]
    fn does_not_contain_alphabetic_characters_passes_for_empty_string() {
        assert_that!("").does_not_contain_alphabetic_characters();
    }

    #[test]
    fn does_not_contain_alphabetic_characters_passes_for_number() {
        assert_that!("1337").does_not_contain_alphabetic_characters();
    }

    #[test]
    fn does_not_contain_alphabetic_characters_fails_for_single_word() {
        assert_fails!(("Potatoes").does_not_contain_alphabetic_characters(),
            expected it "not to contain alphabetic characters"
            but it "was <[P]otatoes>");
    }

    #[test]
    fn does_not_contain_alphabetic_characters_fails_for_later_letter() {
        assert_fails!(("2 * a").does_not_contain_alphabetic_characters(),
            expected it "not to contain alphabetic characters"
            but it "was <2 * [a]>");
    }

    #[test]
    fn contains_numeric_character_passes_for_number() {
        assert_that!("1337").contains_numeric_characters();
    }

    #[test]
    fn contains_numeric_character_passes_for_later_digit() {
        assert_that!("a + 2").contains_numeric_characters();
    }

    #[test]
    fn contains_numeric_character_fails_for_empty_string() {
        assert_fails!(("").contains_numeric_characters(),
            expected it "to contain numeric characters"
            but it "was <>");
    }

    #[test]
    fn contains_numeric_character_fails_for_alphabetic_word() {
        assert_fails!(("cucumber").contains_numeric_characters(),
            expected it "to contain numeric characters"
            but it "was <cucumber>");
    }

    #[test]
    fn does_not_contain_numeric_character_passes_for_empty_string() {
        assert_that!("").does_not_contain_numeric_characters();
    }

    #[test]
    fn does_not_contain_numeric_character_passes_for_alphabetic_word() {
        assert_that!("cucumber").does_not_contain_numeric_characters();
    }

    #[test]
    fn does_not_contain_numeric_character_fails_for_number() {
        assert_fails!(("1337").does_not_contain_numeric_characters(),
            expected it "not to contain numeric characters"
            but it "was <[1]337>");
    }

    #[test]
    fn does_not_contain_numeric_character_fails_for_later_digit() {
        assert_fails!(("a + 2").does_not_contain_numeric_characters(),
            expected it "not to contain numeric characters"
            but it "was <a + [2]>");
    }

    #[test]
    fn contains_alphanumeric_character_passes_for_word() {
        assert_that!("theory").contains_alphanumeric_characters();
    }

    #[test]
    fn contains_alphanumeric_characters_passes_for_mixed_numbers_and_words() {
        assert_that!("2nd row").contains_alphanumeric_characters();
    }

    #[test]
    fn contains_alphanumeric_characters_fails_for_empty_string() {
        assert_fails!(("").contains_alphanumeric_characters(),
            expected it "to contain alphanumeric characters"
            but it "was <>");
    }

    #[test]
    fn contains_alphanumeric_characters_fails_for_whitespace() {
        assert_fails!((" \n \t ").contains_alphanumeric_characters(),
            expected it "to contain alphanumeric characters"
            but it "was < \\n \\t >");
    }

    #[test]
    fn does_not_contain_alphanumeric_characters_passes_for_empty_string() {
        assert_that!("").does_not_contain_alphanumeric_characters();
    }

    #[test]
    fn does_not_contain_alphanumeric_characters_passes_for_whitespace() {
        assert_that!(" \n \t ").does_not_contain_alphanumeric_characters();
    }

    #[test]
    fn does_not_contain_alphanumeric_character_fails_for_word() {
        assert_fails!(("theory").does_not_contain_alphanumeric_characters(),
            expected it "not to contain alphanumeric characters"
            but it "was <[t]heory>");
    }

    #[test]
    fn does_not_contain_alphanumeric_characters_fails_for_mixed_numbers_and_words() {
        assert_fails!(("2nd row").does_not_contain_alphanumeric_characters(),
            expected it "not to contain alphanumeric characters"
            but it "was <[2]nd row>");
    }

    #[test]
    fn contains_uppercase_letters_passes_for_all_caps_word() {
        assert_that!("HELLO").contains_uppercase_letters();
    }

    #[test]
    fn contains_uppercase_letters_passes_for_later_capitalized_word() {
        assert_that!("hello World").contains_uppercase_letters();
    }

    #[test]
    fn contains_uppercase_letters_fails_for_empty_string() {
        assert_fails!(("").contains_uppercase_letters(),
            expected it "to contain uppercase letters"
            but it "was <>");
    }

    #[test]
    fn contains_uppercase_letters_fails_for_lowercase_word() {
        assert_fails!(("hello").contains_uppercase_letters(),
            expected it "to contain uppercase letters"
            but it "was <hello>");
    }

    #[test]
    fn does_not_contain_uppercase_letters_passes_for_empty_string() {
        assert_that!("").does_not_contain_uppercase_letters();
    }

    #[test]
    fn does_not_contain_uppercase_letters_passes_for_lowercase_word() {
        assert_that!("hello").does_not_contain_uppercase_letters();
    }

    #[test]
    fn does_not_contain_uppercase_letters_fails_for_all_caps_word() {
        assert_fails!(("HELLO").does_not_contain_uppercase_letters(),
            expected it "not to contain uppercase letters"
            but it "was <[H]ELLO>");
    }

    #[test]
    fn does_not_contain_uppercase_letters_fails_for_later_capitalized_word() {
        assert_fails!(("hello World").does_not_contain_uppercase_letters(),
            expected it "not to contain uppercase letters"
            but it "was <hello [W]orld>");
    }

    #[test]
    fn contains_lowercase_letters_passes_for_lowercase_word() {
        assert_that!("hello").contains_lowercase_letters();
    }

    #[test]
    fn contains_lowercase_letters_passes_for_later_lowercase_word() {
        assert_that!("I love Rust").contains_lowercase_letters();
    }

    #[test]
    fn contains_lowercase_letters_fails_for_empty_string() {
        assert_fails!(("").contains_lowercase_letters(),
            expected it "to contain lowercase letters"
            but it "was <>");
    }

    #[test]
    fn contains_lowercase_letters_fails_for_all_caps_word() {
        assert_fails!(("HELLO").contains_lowercase_letters(),
            expected it "to contain lowercase letters"
            but it "was <HELLO>");
    }

    #[test]
    fn does_not_contain_lowercase_letters_passes_for_empty_string() {
        assert_that!("").does_not_contain_lowercase_letters();
    }

    #[test]
    fn does_not_contain_lowercase_letters_passes_for_all_caps_word() {
        assert_that!("HELLO").does_not_contain_lowercase_letters();
    }

    #[test]
    fn does_not_contain_lowercase_lettersfailss_for_lowercase_word() {
        assert_fails!(("hello").does_not_contain_lowercase_letters(),
            expected it "not to contain lowercase letters"
            but it "was <[h]ello>");
    }

    #[test]
    fn does_not_contain_lowercase_letters_fails_for_later_lowercase_word() {
        assert_fails!(("I love Rust").does_not_contain_lowercase_letters(),
            expected it "not to contain lowercase letters"
            but it "was <I [l]ove Rust>");
    }

    #[test]
    fn contains_control_characters_passes_for_single_backspace() {
        assert_that!("\x08").contains_control_characters();
    }

    #[test]
    fn contains_control_characters_passes_for_later_backspace() {
        assert_that!("hello\x08").contains_control_characters();
    }

    #[test]
    fn contains_control_characters_fails_for_empty_string() {
        assert_fails!(("").contains_control_characters(),
            expected it "to contain control characters"
            but it "was <>");
    }

    #[test]
    fn contains_control_characters_fails_for_single_word() {
        assert_fails!(("hello").contains_control_characters(),
            expected it "to contain control characters"
            but it "was <hello>");
    }

    #[test]
    fn does_not_contain_control_characters_passes_for_empty_string() {
        assert_that!("").does_not_contain_control_characters();
    }

    #[test]
    fn does_not_contain_control_characters_passes_for_single_word() {
        assert_that!("hello").does_not_contain_control_characters();
    }

    #[test]
    fn does_not_contain_control_characters_fails_for_single_backspace() {
        assert_fails!(("\x08").does_not_contain_control_characters(),
            expected it "not to contain control characters"
            but it "was <[\\u{8}]>");
    }

    #[test]
    fn does_not_contain_control_characters_fails_for_later_backspace() {
        assert_fails!(("hello\x08").does_not_contain_control_characters(),
            expected it "not to contain control characters"
            but it "was <hello[\\u{8}]>");
    }

    #[test]
    fn is_trimmed_passes_for_empty_string() {
        assert_that!(String::new()).is_trimmed();
    }

    #[test]
    fn is_trimmed_passes_for_single_word() {
        assert_that!("Talk").is_trimmed();
    }

    #[test]
    fn is_trimmed_passes_for_trimmed_sentence() {
        assert_that!("Talk to the hand!").is_trimmed();
    }

    #[test]
    fn is_trimmed_fails_for_single_newline() {
        assert_fails!(("\n").is_trimmed(), expected it "to be trimmed" but it "was <[\\n]>");
    }

    #[test]
    fn is_trimmed_fails_for_leading_space() {
        assert_fails!((" not trimmed").is_trimmed(),
            expected it "to be trimmed"
            but it "was <[ ]not trimmed>");
    }

    #[test]
    fn is_trimmed_fails_for_trailing_tab() {
        assert_fails!(("not trimmed\t").is_trimmed(),
            expected it "to be trimmed"
            but it "was <not trimmed[\\t]>");
    }

    #[test]
    fn is_not_trimmed_passes_for_single_newline() {
        assert_that!("\n").is_not_trimmed();
    }

    #[test]
    fn is_not_trimmed_passes_for_leading_space() {
        assert_that!(" not trimmed").is_not_trimmed();
    }

    #[test]
    fn is_not_trimmed_passes_for_trailing_tab() {
        assert_that!("not trimmed\t").is_not_trimmed();
    }

    #[test]
    fn is_not_trimmed_fails_for_empty_string() {
        assert_fails!((String::new()).is_not_trimmed(),
            expected it "not to be trimmed"
            but it "was <>");
    }

    #[test]
    fn is_not_trimmed_fails_for_single_word() {
        assert_fails!(("Talk").is_not_trimmed(),
            expected it "not to be trimmed"
            but it "was <Talk>");
    }

    #[test]
    fn is_not_trimmed_fails_for_trimmed_sentence() {
        assert_fails!(("Talk to the hand!").is_not_trimmed(),
            expected it "not to be trimmed"
            but it "was <Talk to the hand!>");
    }

    #[test]
    fn is_ascii_passes_for_empty_string() {
        assert_that!("").is_ascii();
    }

    #[test]
    fn is_ascii_passes_for_ascii_string() {
        assert_that!("hello").is_ascii();
    }

    #[test]
    fn is_ascii_fails_for_non_ascii_string() {
        assert_fails!(("Long time 不见").is_ascii(),
            expected it "to be an ASCII string"
            but it "was <Long time [不]见>");
    }

    #[test]
    fn is_not_ascii_passes_for_non_ascii_string() {
        assert_that!("Long time 不见").is_not_ascii();
    }

    #[test]
    fn is_not_ascii_fails_for_empty_string() {
        assert_fails!(("").is_not_ascii(), expected it "not to be an ASCII string" but it "was <>");
    }

    #[test]
    fn is_not_ascii_fails_for_ascii_string() {
        assert_fails!(("hello").is_not_ascii(),
            expected it "not to be an ASCII string"
            but it "was <hello>");
    }

    #[test]
    fn to_chars_works_for_empty_string() {
        let chars = assert_that!("").to_chars().data;

        assert_eq!(chars, vec![]);
    }

    #[test]
    fn to_chars_works_for_ascii_string() {
        let chars = assert_that!("hello").to_chars().data;

        assert_eq!(chars, vec!['h', 'e', 'l', 'l', 'o']);
    }

    #[test]
    fn to_chars_works_for_non_ascii_string() {
        let chars = assert_that!("你好").to_chars().data;

        assert_eq!(chars, vec!['你', '好']);
    }

    #[test]
    fn to_chars_adapts_expression_appropriately() {
        let expression = assert_that!("a").to_chars().expression;

        assert_eq!(expression, "chars of <\"a\">");
    }

    #[test]
    fn to_bytes_works_for_empty_string() {
        let bytes = assert_that!("").to_bytes().data;

        assert_eq!(bytes, Vec::<u8>::new());
    }

    #[test]
    fn to_bytes_works_for_ascii_string() {
        let bytes = assert_that!("hello").to_bytes().data;

        assert_eq!(bytes, vec![b'h', b'e', b'l', b'l', b'o']);
    }

    #[test]
    fn to_bytes_works_for_non_ascii_string() {
        let bytes = assert_that!("你好").to_bytes().data;

        assert_eq!(bytes, vec![0xe4, 0xbd, 0xa0, 0xe5, 0xa5, 0xbd]);
    }

    #[test]
    fn to_bytes_adapts_expression_appropriately() {
        let expression = assert_that!("a").to_bytes().expression;

        assert_eq!(expression, "bytes of <\"a\">");
    }
}
