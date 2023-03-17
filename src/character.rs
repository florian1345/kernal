//! Contains assertions for [char] values. See the [CharacterAssertions] trait for more details.

use std::borrow::Borrow;

use crate::{AssertThat, Failure};

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with [char]
/// argument.
///
/// Examples:
///
/// ```
/// use kernal::prelude::*;
///
/// assert_that!('a').is_alphabetic().is_lowercase().is_not_numeric().is_not_whitespace();
/// assert_that!('o').is_contained_in("hello").is_not_prefix_of("world");
/// ```
pub trait CharacterAssertions {

    /// Asserts that the tested character is a whitespace character, i.e. that
    /// [char::is_whitespace] is `true`.
    fn is_whitespace(self) -> Self;

    /// Asserts that the tested character is not a whitespace character, i.e. that
    /// [char::is_whitespace] is `false`.
    fn is_not_whitespace(self) -> Self;

    /// Asserts that the tested character is an alphabetic character, i.e. that
    /// [char::is_alphabetic] is `true`.
    fn is_alphabetic(self) -> Self;

    /// Asserts that the tested character is not an alphabetic character, i.e. that
    /// [char::is_alphabetic] is `false`.
    fn is_not_alphabetic(self) -> Self;

    /// Asserts that the tested character is a numeric character, i.e. that  [char::is_numeric] is
    /// `true`.
    fn is_numeric(self) -> Self;

    /// Asserts that the tested character is not a numeric character, i.e. that  [char::is_numeric]
    /// is `false`.
    fn is_not_numeric(self) -> Self;

    /// Asserts that the tested character is an alphanumeric character, i.e. that
    /// [char::is_alphanumeric] is `true`.
    fn is_alphanumeric(self) -> Self;

    /// Asserts that the tested character is not an alphanumeric character, i.e. that
    /// [char::is_alphanumeric] is `false`.
    fn is_not_alphanumeric(self) -> Self;

    /// Asserts that the tested character is an uppercase letter, i.e. that [char::is_uppercase] is
    /// `true`.
    fn is_uppercase(self) -> Self;

    /// Asserts that the tested character is not an uppercase letter, i.e. that [char::is_uppercase]
    /// is `false`.
    fn is_not_uppercase(self) -> Self;

    /// Asserts that the tested character is a lowercase letter, i.e. that [char::is_lowercase] is
    /// `true`.
    fn is_lowercase(self) -> Self;

    /// Asserts that the tested character is not a lowercase letter, i.e. that [char::is_lowercase]
    /// is `false`.
    fn is_not_lowercase(self) -> Self;

    /// Asserts that the tested character is a control character, i.e. that [char::is_control] is
    /// `true`.
    fn is_control(self) -> Self;

    /// Asserts that the tested character is not a control character, i.e. that [char::is_control]
    /// is `false`.
    fn is_not_control(self) -> Self;

    /// Asserts that any of the characters of the given `string` (obtained by [str::chars]) is equal
    /// to the tested character.
    fn is_contained_in<S: Borrow<str>>(self, string: S) -> Self;

    /// Asserts that none of the characters of the given `string` (obtained by [str::chars]) is
    /// equal to the tested character.
    fn is_not_contained_in<S: Borrow<str>>(self, string: S) -> Self;

    /// Asserts that the tested character is equal to the first character of the given `string`
    /// (obtained by [str::chars]).
    fn is_prefix_of<S: Borrow<str>>(self, string: S) -> Self;

    /// Asserts that the tested character is not equal to the first character of the given `string`
    /// (obtained by [str::chars]).
    fn is_not_prefix_of<S: Borrow<str>>(self, string: S) -> Self;

    /// Asserts that the tested character is equal to the last character of the given `string`
    /// (obtained by [str::chars]).
    fn is_suffix_of<S: Borrow<str>>(self, string: S) -> Self;

    /// Asserts that the tested character is not equal to the last character of the given `string`
    /// (obtained by [str::chars]).
    fn is_not_suffix_of<S: Borrow<str>>(self, string: S) -> Self;

    /// Asserts that the tested character is equal to the given `expected` character ignoring
    /// casing, i.e. upper-case letters are considered equal to their corresponding lower-case
    /// letters. That is, this assertion will pass if `'a'` is compared to `'A'`.
    fn is_equal_to_ignoring_case(self, expected: char) -> Self;

    /// Asserts that the tested character is different from the given `unexpected` character
    /// ignoring casing, i.e. upper-case letters are considered equal to their corresponding
    /// lower-case letters. That is, this assertion will fail if `'a'` is compared to `'A'`.
    fn is_not_equal_to_ignoring_case(self, unexpected: char) -> Self;
}

fn assert_char_matches_predicate<P, S>(assert_that: AssertThat<char>, predicate: P, expected_it: S)
    -> AssertThat<char>
where
    P: Fn(char) -> bool,
    S: Into<String>
{
    if !predicate(assert_that.data) {
        Failure::new(&assert_that)
            .expected_it(expected_it)
            .but_it(format!("was <{}>", assert_that.data.escape_debug()))
            .fail();
    }

    assert_that
}

impl CharacterAssertions for AssertThat<char> {

    fn is_whitespace(self) -> Self {
        assert_char_matches_predicate(self,
            |character| character.is_whitespace(),
            "to be a whitespace character")
    }

    fn is_not_whitespace(self) -> Self {
        assert_char_matches_predicate(self,
            |character| !character.is_whitespace(),
            "not to be a whitespace character")
    }

    fn is_alphabetic(self) -> Self {
        assert_char_matches_predicate(self,
            |character| character.is_alphabetic(),
            "to be an alphabetic character")
    }

    fn is_not_alphabetic(self) -> Self {
        assert_char_matches_predicate(self,
            |character| !character.is_alphabetic(),
            "not to be an alphabetic character")
    }

    fn is_numeric(self) -> Self {
        assert_char_matches_predicate(self,
            |character| character.is_numeric(),
            "to be a numeric character")
    }

    fn is_not_numeric(self) -> Self {
        assert_char_matches_predicate(self,
            |character| !character.is_numeric(),
            "not to be a numeric character")
    }

    fn is_alphanumeric(self) -> Self {
        assert_char_matches_predicate(self,
            |character| character.is_alphanumeric(),
            "to be an alphanumeric character")
    }

    fn is_not_alphanumeric(self) -> Self {
        assert_char_matches_predicate(self,
            |character| !character.is_alphanumeric(),
            "not to be an alphanumeric character")
    }

    fn is_uppercase(self) -> Self {
        assert_char_matches_predicate(self,
            |character| character.is_uppercase(),
            "to be an uppercase character")
    }

    fn is_not_uppercase(self) -> Self {
        assert_char_matches_predicate(self,
            |character| !character.is_uppercase(),
            "not to be an uppercase character")
    }

    fn is_lowercase(self) -> Self {
        assert_char_matches_predicate(self,
            |character| character.is_lowercase(),
            "to be a lowercase character")
    }

    fn is_not_lowercase(self) -> Self {
        assert_char_matches_predicate(self,
            |character| !character.is_lowercase(),
            "not to be a lowercase character")
    }

    fn is_control(self) -> Self {
        assert_char_matches_predicate(self,
            |character| character.is_control(),
            "to be a control character")
    }

    fn is_not_control(self) -> Self {
        assert_char_matches_predicate(self,
            |character| !character.is_control(),
            "not to be a control character")
    }

    fn is_contained_in<S: Borrow<str>>(self, string: S) -> Self {
        let string = string.borrow();

        assert_char_matches_predicate(self,
            |character| string.chars().any(|string_character| character == string_character),
            format!("to be contained in <{}>", string.escape_debug()))
    }

    fn is_not_contained_in<S: Borrow<str>>(self, string: S) -> Self {
        let string = string.borrow();

        assert_char_matches_predicate(self,
            |character| string.chars().all(|string_character| character != string_character),
            format!("not to be contained in <{}>", string.escape_debug()))
    }

    fn is_prefix_of<S: Borrow<str>>(self, string: S) -> Self {
        let string = string.borrow();

        assert_char_matches_predicate(self, |character| string.starts_with(character),
            format!("to be the first character of <{}>", string.escape_debug()))
    }

    fn is_not_prefix_of<S: Borrow<str>>(self, string: S) -> Self {
        let string = string.borrow();

        assert_char_matches_predicate(self, |character| !string.starts_with(character),
            format!("not to be the first character of <{}>", string.escape_debug()))
    }

    fn is_suffix_of<S: Borrow<str>>(self, string: S) -> Self {
        let string = string.borrow();

        assert_char_matches_predicate(self, |character| string.ends_with(character),
            format!("to be the last character of <{}>", string.escape_debug()))
    }

    fn is_not_suffix_of<S: Borrow<str>>(self, string: S) -> Self {
        let string = string.borrow();

        assert_char_matches_predicate(self, |character| !string.ends_with(character),
            format!("not to be the last character of <{}>", string.escape_debug()))
    }

    fn is_equal_to_ignoring_case(self, expected: char) -> Self {
        assert_char_matches_predicate(self,
            |character|
                character.to_lowercase().to_string() == expected.to_lowercase().to_string(),
            format!("to equal <{}> ignoring case", expected.escape_debug()))
    }

    fn is_not_equal_to_ignoring_case(self, expected: char) -> Self {
        assert_char_matches_predicate(self,
            |character|
                character.to_lowercase().to_string() != expected.to_lowercase().to_string(),
            format!("not to equal <{}> ignoring case", expected.escape_debug()))
    }
}

#[cfg(test)]
mod tests {

    use crate::{assert_fails, assert_that};

    use super::*;

    #[test]
    fn is_whitespace_passes_for_space() {
        assert_that!(' ').is_whitespace();
    }

    #[test]
    fn is_whitespace_passes_for_newline() {
        assert_that!('\n').is_whitespace();
    }

    #[test]
    fn is_whitespace_fails_for_a() {
        assert_fails!(('a').is_whitespace(),
            expected it "to be a whitespace character"
            but it "was <a>");
    }

    #[test]
    fn is_not_whitespace_passes_for_a() {
        assert_that!('a').is_not_whitespace();
    }

    #[test]
    fn is_not_whitespace_fails_for_space() {
        assert_fails!((' ').is_not_whitespace(),
            expected it "not to be a whitespace character"
            but it "was < >");
    }

    #[test]
    fn is_not_whitespace_fails_for_newline() {
        assert_fails!(('\n').is_not_whitespace(),
            expected it "not to be a whitespace character"
            but it "was <\\n>");
    }

    #[test]
    fn is_alphabetic_passes_for_a() {
        assert_that!('a').is_alphabetic();
    }

    #[test]
    fn is_alphabetic_fails_for_0() {
        assert_fails!(('0').is_alphabetic(),
            expected it "to be an alphabetic character"
            but it "was <0>");
    }

    #[test]
    fn is_not_alphabetic_passes_for_0() {
        assert_that!('0').is_not_alphabetic();
    }

    #[test]
    fn is_not_alphabetic_fails_for_a() {
        assert_fails!(('a').is_not_alphabetic(),
            expected it "not to be an alphabetic character"
            but it "was <a>");
    }

    #[test]
    fn is_numeric_passes_for_0() {
        assert_that!('0').is_numeric();
    }

    #[test]
    fn is_numeric_fails_for_a() {
        assert_fails!(('a').is_numeric(),
            expected it "to be a numeric character"
            but it "was <a>");
    }

    #[test]
    fn is_not_numeric_passes_for_a() {
        assert_that!('a').is_not_numeric();
    }

    #[test]
    fn is_not_numeric_fails_for_0() {
        assert_fails!(('0').is_not_numeric(),
            expected it "not to be a numeric character"
            but it "was <0>");
    }

    #[test]
    fn is_alphanumeric_passes_for_0() {
        assert_that!('0').is_alphanumeric();
    }

    #[test]
    fn is_alphanumeric_passes_for_a() {
        assert_that!('a').is_alphanumeric();
    }

    #[test]
    fn is_alphanumeric_fails_for_period() {
        assert_fails!(('.').is_alphanumeric(),
            expected it "to be an alphanumeric character"
            but it "was <.>");
    }

    #[test]
    fn is_not_alphanumeric_passes_for_period() {
        assert_that!('.').is_not_alphanumeric();
    }

    #[test]
    fn is_not_alphanumeric_fails_for_0() {
        assert_fails!(('0').is_not_alphanumeric(),
            expected it "not to be an alphanumeric character"
            but it "was <0>");
    }

    #[test]
    fn is_not_alphanumeric_fails_for_a() {
        assert_fails!(('a').is_not_alphanumeric(),
            expected it "not to be an alphanumeric character"
            but it "was <a>");
    }

    #[test]
    fn is_uppercase_passes_for_uppercase_a() {
        assert_that!('A').is_uppercase();
    }

    #[test]
    fn is_uppercase_fails_for_lowercase_a() {
        assert_fails!(('a').is_uppercase(),
            expected it "to be an uppercase character"
            but it "was <a>");
    }

    #[test]
    fn is_not_uppercase_passes_for_lowercase_a() {
        assert_that!('a').is_not_uppercase();
    }

    #[test]
    fn is_not_uppercase_fails_for_uppercase_a() {
        assert_fails!(('A').is_not_uppercase(),
            expected it "not to be an uppercase character"
            but it "was <A>");
    }

    #[test]
    fn is_lowercase_passes_for_lowercase_a() {
        assert_that!('a').is_lowercase();
    }

    #[test]
    fn is_lowercase_fails_for_uppercase_a() {
        assert_fails!(('A').is_lowercase(),
            expected it "to be a lowercase character"
            but it "was <A>");
    }

    #[test]
    fn is_not_lowercase_passes_for_uppercase_a() {
        assert_that!('A').is_not_lowercase();
    }

    #[test]
    fn is_not_lowercase_fails_for_lowercase_a() {
        assert_fails!(('a').is_not_lowercase(),
            expected it "not to be a lowercase character"
            but it "was <a>");
    }

    #[test]
    fn is_control_passes_for_backspace() {
        assert_that!('\x08').is_control();
    }

    #[test]
    fn is_control_fails_for_a() {
        assert_fails!(('a').is_control(),
            expected it "to be a control character"
            but it "was <a>");
    }

    #[test]
    fn is_not_control_passes_for_a() {
        assert_that!('a').is_not_control();
    }

    #[test]
    fn is_not_control_fails_for_backspace() {
        assert_fails!(('\x08').is_not_control(),
            expected it "not to be a control character"
            but it "was <\\u{8}>");
    }

    #[test]
    fn is_contained_in_passes_for_only_character_in_string() {
        assert_that!('a').is_contained_in("a");
    }

    #[test]
    fn is_contained_in_passes_for_second_character_in_string() {
        assert_that!('b').is_contained_in("ab");
    }

    #[test]
    fn is_contained_in_fails_for_empty_string() {
        assert_fails!(('a').is_contained_in(""),
            expected it "to be contained in <>"
            but it "was <a>");
    }

    #[test]
    fn is_contained_in_fails_for_character_which_is_not_in_non_empty_string() {
        assert_fails!(('a').is_contained_in("bc"),
            expected it "to be contained in <bc>"
            but it "was <a>");
    }

    #[test]
    fn is_not_contained_in_passes_for_empty_string() {
        assert_that!('a').is_not_contained_in("");
    }

    #[test]
    fn is_not_contained_in_passes_for_character_which_is_not_in_non_empty_string() {
        assert_that!('a').is_not_contained_in("bc");
    }

    #[test]
    fn is_not_contained_in_fails_for_only_character_in_string() {
        assert_fails!(('a').is_not_contained_in("a"),
            expected it "not to be contained in <a>"
            but it "was <a>");
    }

    #[test]
    fn is_not_contained_in_fails_for_second_character_in_string() {
        assert_fails!(('b').is_not_contained_in("ab"),
            expected it "not to be contained in <ab>"
            but it "was <b>");
    }

    #[test]
    fn is_prefix_passes_for_only_character_in_string() {
        assert_that!('a').is_prefix_of("a");
    }

    #[test]
    fn is_prefix_passes_for_first_character_in_string() {
        assert_that!('a').is_prefix_of("ab");
    }

    #[test]
    fn is_prefix_fails_for_empty_string() {
        assert_fails!(('a').is_prefix_of(""),
            expected it "to be the first character of <>"
            but it "was <a>");
    }

    #[test]
    fn is_prefix_fails_for_second_character_in_string() {
        assert_fails!(('b').is_prefix_of("ab"),
            expected it "to be the first character of <ab>"
            but it "was <b>");
    }

    #[test]
    fn is_not_prefix_passes_for_empty_string() {
        assert_that!('a').is_not_prefix_of("");
    }

    #[test]
    fn is_not_prefix_passes_for_second_character_in_string() {
        assert_that!('b').is_not_prefix_of("ab");
    }

    #[test]
    fn is_not_prefix_fails_for_only_character_in_string() {
        assert_fails!(('a').is_not_prefix_of("a"),
            expected it "not to be the first character of <a>"
            but it "was <a>");
    }

    #[test]
    fn is_not_prefix_fails_for_first_character_in_string() {
        assert_fails!(('a').is_not_prefix_of("ab"),
            expected it "not to be the first character of <ab>"
            but it "was <a>");
    }

    #[test]
    fn is_suffix_passes_for_only_character_in_string() {
        assert_that!('a').is_suffix_of("a");
    }

    #[test]
    fn is_suffix_passes_for_last_character_in_string() {
        assert_that!('b').is_suffix_of("ab");
    }

    #[test]
    fn is_suffix_fails_for_empty_string() {
        assert_fails!(('a').is_suffix_of(""),
            expected it "to be the last character of <>"
            but it "was <a>");
    }

    #[test]
    fn is_suffix_fails_for_second_to_last_character_in_string() {
        assert_fails!(('a').is_suffix_of("ab"),
            expected it "to be the last character of <ab>"
            but it "was <a>");
    }

    #[test]
    fn is_not_suffix_passes_for_empty_string() {
        assert_that!('a').is_not_suffix_of("");
    }

    #[test]
    fn is_not_suffix_passes_for_second_to_last_character_in_string() {
        assert_that!('a').is_not_suffix_of("ab");
    }

    #[test]
    fn is_not_suffix_fails_for_only_character_in_string() {
        assert_fails!(('a').is_not_suffix_of("a"),
            expected it "not to be the last character of <a>"
            but it "was <a>");
    }

    #[test]
    fn is_not_suffix_fails_for_last_character_in_string() {
        assert_fails!(('b').is_not_suffix_of("ab"),
            expected it "not to be the last character of <ab>"
            but it "was <b>");
    }

    #[test]
    fn is_equal_to_ignoring_case_passes_for_same_character() {
        assert_that!('.').is_equal_to_ignoring_case('.');
    }

    #[test]
    fn is_equal_to_ignoring_case_passes_for_lowercase_a_and_uppercase_a() {
        assert_that!('a').is_equal_to_ignoring_case('A');
    }

    #[test]
    fn is_equal_to_ignoring_case_fails_for_different_letters() {
        assert_fails!(('a').is_equal_to_ignoring_case('b'),
            expected it "to equal <b> ignoring case"
            but it "was <a>");
    }

    #[test]
    fn is_not_equal_to_ignoring_case_passes_for_different_letters() {
        assert_that!('a').is_not_equal_to_ignoring_case('b');
    }

    #[test]
    fn is_not_equal_to_ignoring_case_fails_for_same_character() {
        assert_fails!(('.').is_not_equal_to_ignoring_case('.'),
            expected it "not to equal <.> ignoring case"
            but it "was <.>");
    }

    #[test]
    fn is_not_equal_to_ignoring_case_fails_for_lowercase_a_and_uppercase_a() {
        assert_fails!(('a').is_not_equal_to_ignoring_case('A'),
            expected it "not to equal <A> ignoring case"
            but it "was <a>");
    }
}
