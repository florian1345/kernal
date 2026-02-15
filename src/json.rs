//! Contains assertions for JSON-parseable values (`[u8]`- and `str`-based types, or more precisely,
//! types implementing [AsJson]) and already parsed JSON [Value]s. See [JsonAssertions] for more
//! details.

use std::borrow::Cow;
use std::fmt;
use std::fmt::{Display, Formatter};
use std::rc::Rc;
use std::sync::Arc;

use serde_json::{Result as JsonResult, Value};

use crate::{AssertThat, AssertThatData, Failure};

/// A trait for types which can be converted to a JSON [Value] (either by parsing or by cloning an
/// already parsed [Value]).
pub trait AsJson {
    /// Converts the value to a JSON [Value].
    ///
    /// # Errors
    ///
    /// Any [serde_json::Error] that occurs during parsing if this value is not already parsed.
    fn as_json(&self) -> JsonResult<Value>;
}

impl AsJson for [u8] {
    fn as_json(&self) -> JsonResult<Value> {
        serde_json::from_slice(self)
    }
}

impl<const LEN: usize> AsJson for [u8; LEN] {
    fn as_json(&self) -> JsonResult<Value> {
        <[u8]>::as_json(self)
    }
}

impl AsJson for Vec<u8> {
    fn as_json(&self) -> JsonResult<Value> {
        <[u8]>::as_json(self)
    }
}

impl AsJson for str {
    fn as_json(&self) -> JsonResult<Value> {
        serde_json::from_str(self)
    }
}

impl AsJson for String {
    fn as_json(&self) -> JsonResult<Value> {
        str::as_json(self)
    }
}

impl AsJson for Value {
    fn as_json(&self) -> JsonResult<Value> {
        Ok(self.clone())
    }
}

impl<T: AsJson + ?Sized> AsJson for &T {
    fn as_json(&self) -> JsonResult<Value> {
        T::as_json(self)
    }
}

impl<T: AsJson + ?Sized> AsJson for &mut T {
    fn as_json(&self) -> JsonResult<Value> {
        T::as_json(self)
    }
}

impl<T: AsJson + ?Sized> AsJson for Box<T> {
    fn as_json(&self) -> JsonResult<Value> {
        T::as_json(self)
    }
}

impl<T: AsJson + ?Sized> AsJson for Rc<T> {
    fn as_json(&self) -> JsonResult<Value> {
        T::as_json(self)
    }
}

impl<T: AsJson + ?Sized> AsJson for Arc<T> {
    fn as_json(&self) -> JsonResult<Value> {
        T::as_json(self)
    }
}

impl<T: AsJson + ToOwned + ?Sized> AsJson for Cow<'_, T> {
    fn as_json(&self) -> JsonResult<Value> {
        T::as_json(self)
    }
}

#[derive(Clone, Copy, Debug)]
enum BasicJsonPathSegment<'value> {
    Key(&'value str),
    Index(usize),
}

#[derive(Clone, Debug, Default)]
struct BasicJsonPath<'value> {
    segments: Vec<BasicJsonPathSegment<'value>>,
}

impl<'value> BasicJsonPath<'value> {
    fn push(&mut self, segment: BasicJsonPathSegment<'value>) {
        self.segments.push(segment);
    }

    fn pop(&mut self) {
        self.segments.pop();
    }
}

impl<'value> Display for BasicJsonPath<'value> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "$")?;

        for &segment in &self.segments {
            match segment {
                BasicJsonPathSegment::Key(key) => write!(f, ".{}", key)?,
                BasicJsonPathSegment::Index(index) => write!(f, "[{}]", index)?,
            }
        }

        Ok(())
    }
}

struct Deviation<'value> {
    path: BasicJsonPath<'value>,
    value_in_actual: Option<&'value Value>,
    value_in_expected: Option<&'value Value>,
}

impl Display for Deviation<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match (self.value_in_actual, self.value_in_expected) {
            (Some(value_in_actual), Some(value_in_expected)) => {
                write!(
                    f,
                    "different value at <{}>, expected: <{}>, got: <{}>",
                    self.path,
                    serde_json::to_string_pretty(value_in_expected).unwrap(),
                    serde_json::to_string_pretty(value_in_actual).unwrap()
                )
            },
            (Some(value_in_actual), None) => {
                write!(
                    f,
                    "unexpected value at <{}>, got: <{}>",
                    self.path,
                    serde_json::to_string_pretty(value_in_actual).unwrap()
                )
            },
            (None, Some(value_in_expected)) => {
                write!(
                    f,
                    "missing value at <{}>, expected: <{}>",
                    self.path,
                    serde_json::to_string_pretty(value_in_expected).unwrap()
                )
            },
            (None, None) => unreachable!(),
        }
    }
}

fn compare_json_rec<'value>(
    actual: &'value Value,
    expected: &'value Value,
    track_missing_keys_in_actual: bool,
    track_missing_keys_in_expected: bool,
    current_path: &mut BasicJsonPath<'value>,
    deviations: &mut Vec<Deviation<'value>>,
) {
    match (actual, expected) {
        (Value::Null, Value::Null) => {},
        (Value::Number(_), Value::Number(_))
        | (Value::Bool(_), Value::Bool(_))
        | (Value::String(_), Value::String(_)) => {
            if actual != expected {
                deviations.push(Deviation {
                    path: current_path.clone(),
                    value_in_actual: Some(actual),
                    value_in_expected: Some(expected),
                })
            }
        },
        (Value::Array(actual_array), Value::Array(expected_array)) => {
            if actual_array.len() != expected_array.len() {
                deviations.push(Deviation {
                    path: current_path.clone(),
                    value_in_actual: Some(actual),
                    value_in_expected: Some(expected),
                })
            }

            let element_iter = actual_array.iter().zip(expected_array.iter()).enumerate();

            for (index, (lhs_element, rhs_element)) in element_iter {
                current_path.push(BasicJsonPathSegment::Index(index));
                compare_json_rec(
                    lhs_element,
                    rhs_element,
                    track_missing_keys_in_actual,
                    track_missing_keys_in_expected,
                    current_path,
                    deviations,
                );
                current_path.pop();
            }
        },
        (Value::Object(actual_object), Value::Object(expected_object)) => {
            for key in actual_object
                .keys()
                .filter(|&key| expected_object.contains_key(key))
            {
                current_path.push(BasicJsonPathSegment::Key(key));
                compare_json_rec(
                    &actual_object[key],
                    &expected_object[key],
                    track_missing_keys_in_actual,
                    track_missing_keys_in_expected,
                    current_path,
                    deviations,
                );
                current_path.pop();
            }

            if track_missing_keys_in_actual {
                for key in expected_object
                    .keys()
                    .filter(|&key| !actual_object.contains_key(key))
                {
                    current_path.push(BasicJsonPathSegment::Key(key));
                    deviations.push(Deviation {
                        path: current_path.clone(),
                        value_in_actual: None,
                        value_in_expected: Some(&expected_object[key]),
                    });
                    current_path.pop();
                }
            }

            if track_missing_keys_in_expected {
                for key in actual_object
                    .keys()
                    .filter(|&key| !expected_object.contains_key(key))
                {
                    current_path.push(BasicJsonPathSegment::Key(key));
                    deviations.push(Deviation {
                        path: current_path.clone(),
                        value_in_actual: Some(&actual_object[key]),
                        value_in_expected: None,
                    });
                    current_path.pop();
                }
            }
        },
        _ => {
            // type mismatch
            deviations.push(Deviation {
                path: current_path.clone(),
                value_in_actual: Some(actual),
                value_in_expected: Some(expected),
            })
        },
    }
}

fn compare_json<'value>(
    actual: &'value Value,
    expected: &'value Value,
    track_missing_keys_in_actual: bool,
    track_missing_keys_in_expected: bool,
) -> Vec<Deviation<'value>> {
    let mut deviations = Vec::new();

    compare_json_rec(
        actual,
        expected,
        track_missing_keys_in_actual,
        track_missing_keys_in_expected,
        &mut BasicJsonPath::default(),
        &mut deviations,
    );

    deviations
}

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with an
/// argument that implements [AsJson]. The assertions provided by this trait are concerned with JSON
/// syntax and equivalence.
///
/// Examples:
///
/// ```
/// use kernal::prelude::*;
///
/// assert_that!("{\"foo\": 1, \"bar\": 2}")
///     .is_valid_json()
///     .is_equivalent_to_json("{\"bar\": 2, \"foo\": 1}")
///     .is_not_subset_of_json("{\"foo\": 1, \"baz\": 3}");
/// ```
pub trait JsonAssertions {
    /// Asserts that the tested value has valid JSON syntax (trivially successful for already parsed
    /// [Value]s).
    fn is_valid_json(self) -> Self;

    /// Asserts that the tested value does not have valid JSON syntax (trivially fails for already
    /// parsed [Value]s).
    fn is_not_valid_json(self) -> Self;

    /// Asserts that the tested value has valid JSON syntax (if it is not an already parsed [Value])
    /// and its JSON representation is equivalent to the given `expected` JSON value (which is
    /// assumed to have correct syntax).
    ///
    /// JSONs are
    fn is_equivalent_to_json(self, expected: impl AsJson) -> Self;

    /// Asserts that the tested value has valid JSON syntax (if it is not an already parsed [Value])
    /// and its JSON representation is _not_ equivalent to the given `unexpected` JSON value (which
    /// is assumed to have correct syntax).
    fn is_not_equivalent_to_json(self, unexpected: impl AsJson) -> Self;

    /// Asserts that the tested value has valid JSON syntax (if it is not an already parsed [Value])
    /// and its JSON representation is a subset of the given `expected` JSON value (which is assumed
    /// to have correct syntax).
    ///
    /// A JSON value `a` is considered to be a subset of `b`, if and only if
    ///
    /// * `a` is equivalent to `b` as defined in [JsonAssertions::is_equivalent_to_json] **or**
    /// * `a` and `b` are objects, and for every key `k` in `a`, `a[k]` is a subset of `b[k]` **or**
    /// * `a` and `b` are arrays of equal length, and for every index `i` in `a`, `a[i]` is a subset
    ///   of `b[i]`.
    ///
    /// As an example, `{ "a": { "b": 1 } }` is a subset of `{ "a": { "b": 1, "c": 2 }, "d": 3 }`,
    /// but not of `{ "a": { "b": 2 } }`. Note that `[1]` is _not_ a subset of `[1, 2]`.
    fn is_subset_of_json(self, expected: impl AsJson) -> Self;

    /// Asserts that the tested value has valid JSON syntax (if it is not an already parsed [Value])
    /// and its JSON representation is _not_ a subset of the given `unexpected` JSON value (which is
    /// assumed to have correct syntax).
    ///
    /// See [JsonAssertions::is_subset_of_json] for the definition of "subset" used by this crate in
    /// the context of JSON values.
    fn is_not_subset_of_json(self, unexpected: impl AsJson) -> Self;

    /// Asserts that the tested value has valid JSON syntax (if it is not an already parsed [Value])
    /// and its JSON representation is a superset of the given `expected` JSON value (which is
    /// assumed to have correct syntax).
    ///
    /// A JSON value `a` is considered to be a superset of `b`, if and only if `b` is a subset of
    /// `a` according to the definition in [JsonAssertions::is_subset_of_json].
    fn is_superset_of_json(self, expected: impl AsJson) -> Self;

    /// Asserts that the tested value has valid JSON syntax (if it is not an already parsed [Value])
    /// and its JSON representation is _not_ a superset of the given `unexpected` JSON value (which
    /// is assumed to have correct syntax).
    ///
    /// A JSON value `a` is considered to be a superset of `b`, if and only if `b` is a subset of
    /// `a` according to the definition in [JsonAssertions::is_subset_of_json].
    fn is_not_superset_of_json(self, unexpected: impl AsJson) -> Self;
}

fn parse_actual_and_assert_success(assert_that: &AssertThat<impl AsJson>) -> Value {
    assert_that.data().as_json().unwrap_or_else(|e| {
        Failure::new(assert_that)
            .expected_it("to have valid JSON syntax")
            .but_it(format!("was parsed with an error: {}", e))
            .fail()
    })
}

fn parse_expected(expected: impl AsJson) -> Value {
    expected
        .as_json()
        .expect("expected JSON value has invalid syntax")
}

fn assert_positive_json_comparison<T: AsJson>(
    assert_that: AssertThat<T>,
    expected: impl AsJson,
    track_missing_keys_in_actual: bool,
    track_missing_keys_in_expected: bool,
    expected_it_prefix: &str,
) -> AssertThat<T> {
    let expected = parse_expected(expected);
    let actual = parse_actual_and_assert_success(&assert_that);
    let deviations = compare_json(
        &actual,
        &expected,
        track_missing_keys_in_actual,
        track_missing_keys_in_expected,
    );

    if !deviations.is_empty() {
        Failure::new(&assert_that)
            .expected_it(format!(
                "{} <{}>",
                expected_it_prefix,
                serde_json::to_string_pretty(&expected).unwrap()
            ))
            .but_it(format!(
                "had the following unexpected deviations:\n{}",
                deviations
                    .iter()
                    .map(|deviation| deviation.to_string())
                    .collect::<Vec<_>>()
                    .join("\n")
            ))
            .fail();
    }

    assert_that
}

fn assert_negative_json_comparison<T: AsJson>(
    assert_that: AssertThat<T>,
    unexpected: impl AsJson,
    track_missing_keys_in_actual: bool,
    track_missing_keys_in_expected: bool,
    expected_it_prefix: &str,
) -> AssertThat<T> {
    let unexpected = parse_expected(unexpected);
    let actual = parse_actual_and_assert_success(&assert_that);
    let deviations = compare_json(
        &actual,
        &unexpected,
        track_missing_keys_in_actual,
        track_missing_keys_in_expected,
    );

    if deviations.is_empty() {
        Failure::new(&assert_that)
            .expected_it(format!(
                "{} <{}>",
                expected_it_prefix,
                serde_json::to_string_pretty(&unexpected).unwrap()
            ))
            .but_it(format!(
                "was <{}>",
                serde_json::to_string_pretty(&actual).unwrap()
            ))
            .fail();
    }

    assert_that
}

impl<T: AsJson> JsonAssertions for AssertThat<T> {
    fn is_valid_json(self) -> Self {
        parse_actual_and_assert_success(&self);

        self
    }

    fn is_not_valid_json(self) -> Self {
        if let Ok(value) = self.data().as_json() {
            Failure::new(&self)
                .expected_it("not to have valid JSON syntax")
                .but_it(format!(
                    "was parsed successfully as the following value: {}",
                    serde_json::to_string_pretty(&value).unwrap(),
                ))
                .fail();
        }

        self
    }

    fn is_equivalent_to_json(self, expected: impl AsJson) -> Self {
        assert_positive_json_comparison(self, expected, true, true, "to be equivalent JSON to")
    }

    fn is_not_equivalent_to_json(self, unexpected: impl AsJson) -> Self {
        assert_negative_json_comparison(
            self,
            unexpected,
            true,
            true,
            "not to be equivalent JSON to",
        )
    }

    fn is_subset_of_json(self, expected: impl AsJson) -> Self {
        assert_positive_json_comparison(self, expected, false, true, "to be a JSON subset of")
    }

    fn is_not_subset_of_json(self, unexpected: impl AsJson) -> Self {
        assert_negative_json_comparison(self, unexpected, false, true, "not to be a JSON subset of")
    }

    fn is_superset_of_json(self, expected: impl AsJson) -> Self {
        assert_positive_json_comparison(self, expected, true, false, "to be a JSON superset of")
    }

    fn is_not_superset_of_json(self, unexpected: impl AsJson) -> Self {
        assert_negative_json_comparison(
            self,
            unexpected,
            true,
            false,
            "not to be a JSON superset of",
        )
    }
}

#[cfg(test)]
mod tests {
    use std::panic::UnwindSafe;

    use rstest::rstest;
    use rstest_reuse::{apply, template};
    use serde_json::json;

    use super::*;
    use crate::prelude::*;

    fn assert_fails_with_syntax_error<T>(assertion: impl FnOnce() -> T + UnwindSafe) {
        assert_that!(assertion).panics_with_message_matching(|message| {
            message.contains("to have valid JSON syntax")
                && message.contains("was parsed with an error: ")
        });
    }

    fn assert_fails_with_deviations<T>(
        assertion: impl FnOnce() -> T + UnwindSafe,
        expected_it: &str,
        missing_paths_and_values: impl IntoIterator<Item = (&'static str, &'static str)>,
        unexpected_paths_and_values: impl IntoIterator<Item = (&'static str, &'static str)>,
        different_paths_and_values_and_expected_values: impl IntoIterator<
            Item = (&'static str, &'static str, &'static str),
        >,
    ) {
        assert_that!(assertion).panics_with_message_matching(|message| {
            message.contains(expected_it)
                && message.contains("it had the following unexpected deviations:")
                && missing_paths_and_values
                    .into_iter()
                    .all(|(missing_path, missing_value)| {
                        message.contains(&format!(
                            "missing value at <{missing_path}>, expected: <{missing_value}>"
                        ))
                    })
                && unexpected_paths_and_values.into_iter().all(
                    |(unexpected_path, unexpected_value)| {
                        message.contains(&format!(
                            "unexpected value at <{unexpected_path}>, got: <{unexpected_value}>"
                        ))
                    },
                )
                && different_paths_and_values_and_expected_values
                    .into_iter()
                    .all(|(different_path, different_value, expected_value)| {
                        message.contains(&format!(
                            "different value at <{different_path}>, expected: <{expected_value}>, \
                                got: <{different_value}>"
                        ))
                    })
        });
    }

    fn assert_negative_assertion_fails<T>(
        assertion: impl FnOnce() -> T + UnwindSafe,
        expected_it: &str,
        actual_pretty_representation: &str,
        expected_pretty_representation: &str,
    ) {
        assert_that!(assertion).panics_with_message_matching(|message| {
            message.contains(&format!("{expected_it} <{expected_pretty_representation}>"))
                && message.contains(&format!("was <{actual_pretty_representation}>"))
        });
    }

    #[template]
    #[rstest]
    #[case("{}", "{}")]
    #[case("{ \"a\": 1, \"b\": 2 }", "{\n  \"a\": 1,\n  \"b\": 2\n}")]
    #[case("[]", "[]")]
    #[case("[1, 2, 3]", "[\n  1,\n  2,\n  3\n]")]
    #[case("\n[true,\nfalse,\nnull]\n", "[\n  true,\n  false,\n  null\n]")]
    #[case("\"\"", "\"\"")]
    #[case("\"hello\"", "\"hello\"")]
    #[case("true", "true")]
    #[case("1.23", "1.23")]
    #[case(json!({ "foo": "bar" }), "{\n  \"foo\": \"bar\"\n}")]
    fn valid_jsons(#[case] json: impl AsJson + UnwindSafe, #[case] pretty_representation: &str) {}

    #[template]
    #[rstest]
    #[case("not json")]
    #[case(b"{ \"onclosed\": \"object\"")]
    #[case("\"unclosed string".to_owned())]
    #[case(b"{ \"missing\" \"colon\" }".to_owned())]
    #[case(Box::<str>::from("{ \"missing_value\" }"))]
    #[case(Rc::<str>::from("[ \"unclosed\", \"array\""))]
    #[case(Arc::<str>::from("[ \"trailing\", \"comma\", ]"))]
    #[case(Cow::<str>::Borrowed("{ \"trailing\": \"comma\", }"))]
    fn invalid_jsons(#[case] json: impl AsJson + UnwindSafe) {}

    #[apply(valid_jsons)]
    fn is_valid_json_passes(
        #[case] json: impl AsJson + UnwindSafe,
        #[case] _pretty_representation: &str,
    ) {
        assert_that!(json).is_valid_json();
    }

    #[apply(invalid_jsons)]
    fn is_valid_json_failure(#[case] json: impl AsJson + UnwindSafe) {
        assert_fails_with_syntax_error(|| assert_that!(json).is_valid_json());
    }

    #[apply(invalid_jsons)]
    fn is_not_valid_json_passes(#[case] json: impl AsJson + UnwindSafe) {
        assert_that!(json).is_not_valid_json();
    }

    #[apply(valid_jsons)]
    fn is_not_valid_json_failure(
        #[case] json: impl AsJson + UnwindSafe,
        #[case] pretty_representation: &str,
    ) {
        assert_that!(|| assert_that!(json).is_not_valid_json()).panics_with_message_matching(
            |message| {
                message.contains("not to have valid JSON syntax")
                    && message.contains(&format!(
                        "was parsed successfully as the following value: {pretty_representation}"
                    ))
            },
        );
    }

    #[template]
    #[rstest]
    #[case("null", "null", "null")]
    #[case(b"false", b"false", "false")]
    #[case("true".to_owned(), "true".to_owned(), "true")]
    #[case(b"123".to_owned(), b"123".to_owned(), "123")]
    #[case(Box::<str>::from("\"hello\""), Box::<str>::from("\"hello\""), "\"hello\"")]
    #[case(Rc::<str>::from("[]"), Rc::<str>::from("[]"), "[]")]
    #[case(Arc::<str>::from("[1, \"a\"]"), Arc::<str>::from("[1, \"a\"]"), "[\n  1,\n  \"a\"\n]")]
    #[case(Cow::<str>::Borrowed("{}"), Cow::<str>::Owned("{}".to_owned()), "{}")]
    #[case(json!({ "key": "value" }), json!({ "key": "value" }), "{\n  \"key\": \"value\"\n}")]
    #[case(
        Vec::from(b"{ \"a\": 1, \"b\": 2 }"),
        Vec::from(b"{ \"b\": 2, \"a\": 1 }"),
        "{\n  \"a\": 1,\n  \"b\": 2\n}"
    )]
    fn equivalent_jsons(
        #[case] actual: impl AsJson + UnwindSafe,
        #[case] expected: impl AsJson + UnwindSafe,
        #[case] pretty_representation: &str,
    ) {
    }

    #[template]
    #[rstest]
    #[case("{}", "{ \"foo\": \"bar\" }", [("$.foo", "\"bar\"")], "{}", "{\n  \"foo\": \"bar\"\n}")]
    #[case(
        "{ \"a\": 1 }",
        "{ \"a\": 1, \"b\": 2 }",
        [("$.b", "2")],
        "{\n  \"a\": 1\n}",
        "{\n  \"a\": 1,\n  \"b\": 2\n}",
    )]
    #[case(
        "{ \"a\": { \"b\": true } }",
        "{ \"c\": 1.5, \"a\": { \"b\": true, \"d\": false } }",
        [("$.c", "1.5"), ("$.a.d", "false")],
        "{\n  \"a\": {\n    \"b\": true\n  }\n}",
        "{\n  \"a\": {\n    \"b\": true,\n    \"d\": false\n  },\n  \"c\": 1.5\n}",
    )]
    #[case(
        "[1, {}, 3]",
        "[1, { \"a\": { \"b\": 1 } }, 3]",
        [("$[1].a", "{\n  \"b\": 1\n}")],
        "[\n  1,\n  {},\n  3\n]",
        "[\n  1,\n  {\n    \"a\": {\n      \"b\": 1\n    }\n  },\n  3\n]",
    )]
    #[case(
        "{ \"a\": { \"b\": {} } }",
        "{ \"a\": { \"b\": { \"c\": null } } }",
        [("$.a.b.c", "null")],
        "{\n  \"a\": {\n    \"b\": {}\n  }\n}",
        "{\n  \"a\": {\n    \"b\": {\n      \"c\": null\n    }\n  }\n}",
    )]
    #[case(
        "[[{ \"mid\": 0 }]]",
        "[[{ \"left\": -1, \"mid\": 0, \"right\": [1] }]]",
        [("$[0][0].left", "-1"), ("$[0][0].right", "[\n  1\n]")],
        "[\n  [\n    {\n      \"mid\": 0\n    }\n  ]\n]",
        "[\n  [\n    {\n      \"left\": -1,\n      \"mid\": 0,\n      \"right\": [\n        1\n      ]\n    }\n  ]\n]",
    )]
    #[case(
        "{}",
        "{ \"foo\": { \"bar\": [{ \"baz\": 1 }] } }",
        [("$.foo", "{\n  \"bar\": [\n    {\n      \"baz\": 1\n    }\n  ]\n}")],
        "{}",
        "{\n  \"foo\": {\n    \"bar\": [\n      {\n        \"baz\": 1\n      }\n    ]\n  }\n}",
    )]
    fn proper_subset_jsons(
        #[case] subset: impl AsJson + UnwindSafe,
        #[case] superset: impl AsJson + UnwindSafe,
        #[case] missing_paths_and_values: impl IntoIterator<Item = (&'static str, &'static str)>,
        #[case] subset_pretty_representation: &str,
        #[case] superset_pretty_representation: &str,
    ) {
    }

    #[template]
    #[rstest]
    #[case("1", "2", [], [], [("$", "1", "2")])]
    #[case("null", "\"null\"", [], [], [("$", "null", "\"null\"")])]
    #[case("{ \"a\": true }", "true", [], [], [("$", "{\n  \"a\": true\n}", "true")])]
    #[case(
        "{ \"foo\": \"bar\" }",
        "{ \"foo\": \"baz\" }",
        [],
        [],
        [("$.foo", "\"bar\"", "\"baz\"")],
    )]
    #[case("[1]", "[2]", [], [], [("$[0]", "1", "2")])]
    #[case(
        "{ \"a\": { \"b\": [1] } }",
        "{ \"a\": { \"b\": [1, 1] } }",
        [],
        [],
        [("$.a.b", "[\n  1\n]", "[\n  1,\n  1\n]")],
    )]
    #[case("{ \"a\": 1 }", "{ \"b\": 1 }", [("$.b", "1")], [("$.a", "1")], [])]
    #[case(
        "{ \"foo\": true }",
        "{ \"foo\": false, \"bar\": 1 }",
        [("$.bar", "1")],
        [],
        [("$.foo", "true", "false")],
    )]
    #[case(
        "{ \"foo\": true, \"bar\": 1 }",
        "{ \"foo\": false }",
        [],
        [("$.bar", "1")],
        [("$.foo", "true", "false")],
    )]
    #[case(
        "{ \"foo\": [1, 2, 3], \"bar\": \"hello\" }",
        "{ \"foo\": [1, 3, 2], \"baz\": \"world\" }",
        [("$.baz", "\"world\"")],
        [("$.bar", "\"hello\"")],
        [("$.foo[1]", "2", "3"), ("$.foo[2]", "3", "2")],
    )]
    fn different_jsons(
        #[case] actual: impl AsJson + UnwindSafe,
        #[case] expected: impl AsJson + UnwindSafe,
        #[case] missing_paths_and_values: impl IntoIterator<Item = (&'static str, &'static str)>,
        #[case] unexpected_paths_and_values: impl IntoIterator<Item = (&'static str, &'static str)>,
        #[case] different_paths_and_values_and_expected_values: impl IntoIterator<
            Item = (&'static str, &'static str, &'static str),
        >,
    ) {
    }

    #[apply(equivalent_jsons)]
    fn is_equivalent_to_json_passes(
        #[case] actual: impl AsJson + UnwindSafe,
        #[case] expected: impl AsJson + UnwindSafe,
        #[case] _pretty_representation: &str,
    ) {
        assert_that!(actual).is_equivalent_to_json(expected);
    }

    #[apply(invalid_jsons)]
    fn is_equivalent_to_json_fails_for_invalid_json(#[case] json: impl AsJson + UnwindSafe) {
        assert_fails_with_syntax_error(|| assert_that!(json).is_equivalent_to_json("{}"));
    }

    #[apply(proper_subset_jsons)]
    fn is_equivalent_to_json_fails_for_proper_subset(
        #[case] subset: impl AsJson + UnwindSafe,
        #[case] superset: impl AsJson + UnwindSafe,
        #[case] missing_paths_and_values: impl IntoIterator<Item = (&'static str, &'static str)>,
        #[case] _subset_pretty_representation: &str,
        #[case] _superset_pretty_representation: &str,
    ) {
        assert_fails_with_deviations(
            || assert_that!(subset).is_equivalent_to_json(superset),
            "to be equivalent JSON to",
            missing_paths_and_values,
            [],
            [],
        );
    }

    #[apply(proper_subset_jsons)]
    fn is_equivalent_to_json_fails_for_proper_superset(
        #[case] subset: impl AsJson + UnwindSafe,
        #[case] superset: impl AsJson + UnwindSafe,
        #[case] missing_paths_and_values: impl IntoIterator<Item = (&'static str, &'static str)>,
        #[case] _subset_pretty_representation: &str,
        #[case] _superset_pretty_representation: &str,
    ) {
        assert_fails_with_deviations(
            || assert_that!(superset).is_equivalent_to_json(subset),
            "to be equivalent JSON to",
            [],
            missing_paths_and_values,
            [],
        );
    }

    #[apply(different_jsons)]
    fn is_equivalent_to_json_fails_for_different_jsons(
        #[case] actual: impl AsJson + UnwindSafe,
        #[case] expected: impl AsJson + UnwindSafe,
        #[case] missing_paths_and_values: impl IntoIterator<Item = (&'static str, &'static str)>,
        #[case] unexpected_paths_and_values: impl IntoIterator<Item = (&'static str, &'static str)>,
        #[case] different_paths_and_values_and_expected_values: impl IntoIterator<
            Item = (&'static str, &'static str, &'static str),
        >,
    ) {
        assert_fails_with_deviations(
            || assert_that!(actual).is_equivalent_to_json(expected),
            "to be equivalent JSON to",
            missing_paths_and_values,
            unexpected_paths_and_values,
            different_paths_and_values_and_expected_values,
        );
    }

    #[apply(proper_subset_jsons)]
    fn is_not_equivalent_to_json_passes_for_proper_subset(
        #[case] subset: impl AsJson + UnwindSafe,
        #[case] superset: impl AsJson + UnwindSafe,
        #[case] _missing_paths_and_values: impl IntoIterator<Item = (&'static str, &'static str)>,
        #[case] _subset_pretty_representation: &str,
        #[case] _superset_pretty_representation: &str,
    ) {
        assert_that!(subset).is_not_equivalent_to_json(superset);
    }

    #[apply(proper_subset_jsons)]
    fn is_not_equivalent_to_json_passes_for_proper_superset(
        #[case] subset: impl AsJson + UnwindSafe,
        #[case] superset: impl AsJson + UnwindSafe,
        #[case] _missing_paths_and_values: impl IntoIterator<Item = (&'static str, &'static str)>,
        #[case] _subset_pretty_representation: &str,
        #[case] _superset_pretty_representation: &str,
    ) {
        assert_that!(superset).is_not_equivalent_to_json(subset);
    }

    #[apply(different_jsons)]
    fn is_not_equivalent_to_json_passes_for_different_jsons(
        #[case] actual: impl AsJson + UnwindSafe,
        #[case] expected: impl AsJson + UnwindSafe,
        #[case] _missing_paths_and_values: impl IntoIterator<Item = (&'static str, &'static str)>,
        #[case] _unexpected_paths_and_values: impl IntoIterator<Item = (&'static str, &'static str)>,
        #[case] _different_paths_and_values_and_expected_values: impl IntoIterator<
            Item = (&'static str, &'static str, &'static str),
        >,
    ) {
        assert_that!(actual).is_not_equivalent_to_json(expected);
    }

    #[apply(invalid_jsons)]
    fn is_not_equivalent_to_json_fails_for_invalid_json(#[case] json: impl AsJson + UnwindSafe) {
        assert_fails_with_syntax_error(|| assert_that!(json).is_not_equivalent_to_json("{}"));
    }

    #[apply(equivalent_jsons)]
    fn is_not_equivalent_to_json_fails_for_equivalent_jsons(
        #[case] actual: impl AsJson + UnwindSafe,
        #[case] expected: impl AsJson + UnwindSafe,
        #[case] pretty_representation: &str,
    ) {
        assert_negative_assertion_fails(
            || assert_that!(actual).is_not_equivalent_to_json(expected),
            "not to be equivalent JSON to",
            pretty_representation,
            pretty_representation,
        )
    }

    #[apply(equivalent_jsons)]
    fn is_subset_of_json_passes_for_equivalent_jsons(
        #[case] actual: impl AsJson + UnwindSafe,
        #[case] expected: impl AsJson + UnwindSafe,
        #[case] _pretty_representation: &str,
    ) {
        assert_that!(actual).is_subset_of_json(expected);
    }

    #[apply(proper_subset_jsons)]
    fn is_subset_of_json_passes_for_proper_subsets(
        #[case] subset: impl AsJson + UnwindSafe,
        #[case] superset: impl AsJson + UnwindSafe,
        #[case] _missing_paths_and_values: impl IntoIterator<Item = (&'static str, &'static str)>,
        #[case] _subset_pretty_representation: &str,
        #[case] _superset_pretty_representation: &str,
    ) {
        assert_that!(subset).is_subset_of_json(superset);
    }

    #[apply(invalid_jsons)]
    fn is_subset_of_json_fails_for_invalid_json(#[case] json: impl AsJson + UnwindSafe) {
        assert_fails_with_syntax_error(|| assert_that!(json).is_subset_of_json("{}"));
    }

    #[apply(proper_subset_jsons)]
    fn is_subset_of_json_fails_for_proper_superset(
        #[case] subset: impl AsJson + UnwindSafe,
        #[case] superset: impl AsJson + UnwindSafe,
        #[case] missing_paths_and_values: impl IntoIterator<Item = (&'static str, &'static str)>,
        #[case] _subset_pretty_representation: &str,
        #[case] _superset_pretty_representation: &str,
    ) {
        assert_fails_with_deviations(
            || assert_that!(superset).is_subset_of_json(subset),
            "to be a JSON subset of",
            [],
            missing_paths_and_values,
            [],
        );
    }

    #[apply(different_jsons)]
    fn is_subset_of_json_fails_for_different_jsons(
        #[case] actual: impl AsJson + UnwindSafe,
        #[case] expected: impl AsJson + UnwindSafe,
        #[case] _missing_paths_and_values: impl IntoIterator<Item = (&'static str, &'static str)>,
        #[case] unexpected_paths_and_values: impl IntoIterator<Item = (&'static str, &'static str)>,
        #[case] different_paths_and_values_and_expected_values: impl IntoIterator<
            Item = (&'static str, &'static str, &'static str),
        >,
    ) {
        assert_fails_with_deviations(
            || assert_that!(actual).is_subset_of_json(expected),
            "to be a JSON subset of",
            [],
            unexpected_paths_and_values,
            different_paths_and_values_and_expected_values,
        );
    }

    #[apply(proper_subset_jsons)]
    fn is_not_subset_of_json_passes_for_proper_superset(
        #[case] subset: impl AsJson + UnwindSafe,
        #[case] superset: impl AsJson + UnwindSafe,
        #[case] _missing_paths_and_values: impl IntoIterator<Item = (&'static str, &'static str)>,
        #[case] _subset_pretty_representation: &str,
        #[case] _superset_pretty_representation: &str,
    ) {
        assert_that!(superset).is_not_subset_of_json(subset);
    }

    #[apply(different_jsons)]
    fn is_not_subset_of_json_passes_for_different_jsons(
        #[case] actual: impl AsJson + UnwindSafe,
        #[case] expected: impl AsJson + UnwindSafe,
        #[case] _missing_paths_and_values: impl IntoIterator<Item = (&'static str, &'static str)>,
        #[case] _unexpected_paths_and_values: impl IntoIterator<Item = (&'static str, &'static str)>,
        #[case] _different_paths_and_values_and_expected_values: impl IntoIterator<
            Item = (&'static str, &'static str, &'static str),
        >,
    ) {
        assert_that!(actual).is_not_subset_of_json(expected);
    }

    #[apply(invalid_jsons)]
    fn is_not_subset_of_json_fails_for_invalid_json(#[case] json: impl AsJson + UnwindSafe) {
        assert_fails_with_syntax_error(|| assert_that!(json).is_not_subset_of_json("{}"));
    }

    #[apply(equivalent_jsons)]
    fn is_not_subset_of_json_fails_for_equivalent_jsons(
        #[case] actual: impl AsJson + UnwindSafe,
        #[case] expected: impl AsJson + UnwindSafe,
        #[case] pretty_representation: &str,
    ) {
        assert_negative_assertion_fails(
            || assert_that!(actual).is_not_subset_of_json(expected),
            "not to be a JSON subset of",
            pretty_representation,
            pretty_representation,
        )
    }

    #[apply(proper_subset_jsons)]
    fn is_not_subset_of_json_fails_for_proper_subset(
        #[case] subset: impl AsJson + UnwindSafe,
        #[case] superset: impl AsJson + UnwindSafe,
        #[case] _missing_paths_and_values: impl IntoIterator<Item = (&'static str, &'static str)>,
        #[case] subset_pretty_representation: &str,
        #[case] superset_pretty_representation: &str,
    ) {
        assert_negative_assertion_fails(
            || assert_that!(subset).is_not_subset_of_json(superset),
            "not to be a JSON subset of",
            subset_pretty_representation,
            superset_pretty_representation,
        )
    }

    #[apply(equivalent_jsons)]
    fn is_superset_of_json_passes_for_equivalent_jsons(
        #[case] actual: impl AsJson + UnwindSafe,
        #[case] expected: impl AsJson + UnwindSafe,
        #[case] _pretty_representation: &str,
    ) {
        assert_that!(actual).is_superset_of_json(expected);
    }

    #[apply(proper_subset_jsons)]
    fn is_superset_of_json_passes_for_proper_supersets(
        #[case] subset: impl AsJson + UnwindSafe,
        #[case] superset: impl AsJson + UnwindSafe,
        #[case] _missing_paths_and_values: impl IntoIterator<Item = (&'static str, &'static str)>,
        #[case] _subset_pretty_representation: &str,
        #[case] _superset_pretty_representation: &str,
    ) {
        assert_that!(superset).is_superset_of_json(subset);
    }

    #[apply(invalid_jsons)]
    fn is_superset_of_json_fails_for_invalid_json(#[case] json: impl AsJson + UnwindSafe) {
        assert_fails_with_syntax_error(|| assert_that!(json).is_superset_of_json("{}"));
    }

    #[apply(proper_subset_jsons)]
    fn is_superset_of_json_fails_for_proper_subset(
        #[case] subset: impl AsJson + UnwindSafe,
        #[case] superset: impl AsJson + UnwindSafe,
        #[case] missing_paths_and_values: impl IntoIterator<Item = (&'static str, &'static str)>,
        #[case] _subset_pretty_representation: &str,
        #[case] _superset_pretty_representation: &str,
    ) {
        assert_fails_with_deviations(
            || assert_that!(subset).is_superset_of_json(superset),
            "to be a JSON superset of",
            missing_paths_and_values,
            [],
            [],
        );
    }

    #[apply(different_jsons)]
    fn is_superset_of_json_fails_for_different_jsons(
        #[case] actual: impl AsJson + UnwindSafe,
        #[case] expected: impl AsJson + UnwindSafe,
        #[case] missing_paths_and_values: impl IntoIterator<Item = (&'static str, &'static str)>,
        #[case] _unexpected_paths_and_values: impl IntoIterator<Item = (&'static str, &'static str)>,
        #[case] different_paths_and_values_and_expected_values: impl IntoIterator<
            Item = (&'static str, &'static str, &'static str),
        >,
    ) {
        assert_fails_with_deviations(
            || assert_that!(actual).is_superset_of_json(expected),
            "to be a JSON superset of",
            missing_paths_and_values,
            [],
            different_paths_and_values_and_expected_values,
        );
    }

    #[apply(proper_subset_jsons)]
    fn is_not_superset_of_json_passes_for_proper_superset(
        #[case] subset: impl AsJson + UnwindSafe,
        #[case] superset: impl AsJson + UnwindSafe,
        #[case] _missing_paths_and_values: impl IntoIterator<Item = (&'static str, &'static str)>,
        #[case] _subset_pretty_representation: &str,
        #[case] _superset_pretty_representation: &str,
    ) {
        assert_that!(subset).is_not_superset_of_json(superset);
    }

    #[apply(different_jsons)]
    fn is_not_superset_of_json_passes_for_different_jsons(
        #[case] actual: impl AsJson + UnwindSafe,
        #[case] expected: impl AsJson + UnwindSafe,
        #[case] _missing_paths_and_values: impl IntoIterator<Item = (&'static str, &'static str)>,
        #[case] _unexpected_paths_and_values: impl IntoIterator<Item = (&'static str, &'static str)>,
        #[case] _different_paths_and_values_and_expected_values: impl IntoIterator<
            Item = (&'static str, &'static str, &'static str),
        >,
    ) {
        assert_that!(actual).is_not_superset_of_json(expected);
    }

    #[apply(invalid_jsons)]
    fn is_not_superset_of_json_fails_for_invalid_json(#[case] json: impl AsJson + UnwindSafe) {
        assert_fails_with_syntax_error(|| assert_that!(json).is_not_superset_of_json("{}"));
    }

    #[apply(equivalent_jsons)]
    fn is_not_superset_of_json_fails_for_equivalent_jsons(
        #[case] actual: impl AsJson + UnwindSafe,
        #[case] expected: impl AsJson + UnwindSafe,
        #[case] pretty_representation: &str,
    ) {
        assert_negative_assertion_fails(
            || assert_that!(actual).is_not_superset_of_json(expected),
            "not to be a JSON superset of",
            pretty_representation,
            pretty_representation,
        )
    }

    #[apply(proper_subset_jsons)]
    fn is_not_superset_of_json_fails_for_proper_superset(
        #[case] subset: impl AsJson + UnwindSafe,
        #[case] superset: impl AsJson + UnwindSafe,
        #[case] _missing_paths_and_values: impl IntoIterator<Item = (&'static str, &'static str)>,
        #[case] subset_pretty_representation: &str,
        #[case] superset_pretty_representation: &str,
    ) {
        assert_negative_assertion_fails(
            || assert_that!(superset).is_not_superset_of_json(subset),
            "not to be a JSON superset of",
            superset_pretty_representation,
            subset_pretty_representation,
        )
    }
}
