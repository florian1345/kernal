//! Kernal allows you to use fluent assertions in Rust tests. That is, instead of writing
//! `assert_eq!(my_vec.len(), 10)`, you can write `assert_that!(my_vec).has_length(10)`, making your
//! tests more readable and enabling the framework to provide more expressive error messages. Kernal
//! aims to provide specialized assertions for as many commonly tested properties as possible.
//!
//! # Writing an assertion
//!
//! When you write an assertion over a value, you always start with`assert_that!(<your value>)`. The
//! [assert_that] macro gives you an instance on which you can call associated functions to make
//! your assertions. To be able to use these assertions, the specialized extension traits must be
//! imported, such as [StringAssertions](string::StringAssertions) when using special assertions for
//! [String]s. You can glob-import the [prelude] module to get all imports you need to write every
//! assertion supported by Kernal.
//!
//! ```
//! use kernal::prelude::*;
//!
//! assert_that!("hello world").contains("world");
//! ```
//!
//! # Chaining
//!
//! Every assertion returns the same asserter instance to continue writing assertions on the same
//! value. In addition, some extension traits define mapping methods that manipulate the data in
//! some way and return asserter instances on the new data.
//!
//! ```
//! use kernal::prelude::*;
//!
//! assert_that!("almost")
//!     .has_char_length(6)
//!     .ends_with("most")
//!     .to_chars()
//!     .is_sorted_in_strictly_ascending_order();
//! ```
//!
//! # Creating custom assertions
//!
//! `kernal` allows the creation of custom assertions to test instances of your types in a more
//! natural way. To do this, create a new trait which has a method for your assertion. This will be
//! called on the output of the [assert_that] macro. In order to enable its usage, you need to
//! implement your trait on the [AssertThat] with the type you want to test as a type parameter.
//! Import the [AssertThatData] trait to get access to the tested data. It is not provided in the
//! [prelude] module in order to avoid presenting these methods every time the user looks for an
//! assertion. You can use the [Failure] struct to compose an error message consistent with the
//! `kernal` crate. The example below demonstrates this process.
//!
//! ```
//! use kernal::{AssertThat, AssertThatData, Failure};
//! use kernal::prelude::*;
//!
//! // Our type for which we want to write assertions.
//! struct Vector2f32 { x: f32, y: f32 }
//!
//! // The custom assertion trait we will later implement on `AssertThat`.
//! trait Vector2f32Assertions {
//!     // The custom assertion we want to supply. It is recommended to take an owned `self` and
//!     // return the same instance to support chaining.
//!     fn has_euclidean_norm(self, expected_norm: f32, epsilon: f32) -> AssertThat<Vector2f32>;
//! }
//!
//! impl Vector2f32Assertions for AssertThat<Vector2f32> {
//!     fn has_euclidean_norm(self, expected_norm: f32, epsilon: f32) -> AssertThat<Vector2f32> {
//!         // We get our data with `self.data()`, supplied by `AssertThatData`
//!         let vector = self.data();
//!         let actual_norm = (vector.x * vector.x + vector.y * vector.y).sqrt();
//!
//!         if (actual_norm - expected_norm).abs() > epsilon {
//!             // Here we must fail - using the `Failure` struct
//!             Failure::new(&self)
//!                 .expected_it(format!("to have a euclidean norm within <{}> of <{}>",
//!                     epsilon, expected_norm))
//!                 .but_it(format!("was <({}, {})>, with a euclidean norm of <{}>",
//!                     vector.x, vector.y, actual_norm))
//!                 .fail()
//!         }
//!
//!         // Here the test passes, so we return `self` for chaining
//!         self
//!     }
//! }
//!
//! assert_that!(Vector2f32 { x: 3.0, y: 4.0 }).has_euclidean_norm(5.0, 0.01);
//! assert_that!(|| assert_that!(Vector2f32 { x: 3.0, y: 3.0 }).has_euclidean_norm(5.0, 0.01))
//!     .panics();
//! ```
//!
//! # Crate features
//!
//! * `json`: Enables assertions on types that can be parsed as JSONs as well as JSON values from
//!   the [serde_json](https://docs.rs/serde_json/latest/serde_json/) crate. See the [json] module
//!   for more information.
//!
//! # Notes on performance
//!
//! Should you write assertions on large amounts of data, the standard assertions may become a
//! bottleneck. For some use cases, there are specialized assertions that use additional trait
//! bounds to improve performance. These are available under the [fast_prelude] module. See below
//! for an example on how to use it.
//!
//! ```
//! use kernal::prelude::*;
//! use kernal::fast_prelude::*;
//!
//! assert_that!([1, 2, 3, 4, 5])
//!     .contains_all_of_using_hash([2, 3, 4])
//!     .contains_none_of_using_ord([6, 7, 8]);
//! ```
//!
//! If no sufficiently performant assertion is available, you should consider falling back to
//! standard assertions.

#![allow(clippy::single_range_in_vec_init)]
#![allow(clippy::wrong_self_convention)]
#![warn(missing_docs)]

use std::fmt::Debug;

pub mod abs_diff;
pub mod boolean;
pub mod character;
pub mod collections;
pub mod error;
pub mod fast_prelude;
#[cfg(feature = "json")]
pub mod json;
pub mod lock;
pub mod maps;
pub mod num;
pub mod option;
pub mod panic;
pub mod partial_eq;
pub mod partial_ord;
pub mod path;
pub mod pointer;
pub mod prelude;
pub mod result;
pub mod string;

pub(crate) mod util;

#[cfg(test)]
pub(crate) mod test_util;

/// This struct holds the evaluated result of an expression for further assertions. It also contains
/// metadata used for generating helpful error messages should an assertion fail.
///
/// The main mode of interaction with this struct is by assertions defined by various `*Assertions`
/// traits. To import all of them and get access to all kinds of assertions, glob-import the
/// [prelude] module.
pub struct AssertThat<T> {
    pub(crate) data: T,
    pub(crate) expression: String,
}

impl<T> AssertThat<T> {
    /// Creates a new assert-that instance for the given tested `data` and with the given
    /// `expression` string representing the actual code which evaluated to the tested data. This
    /// may also be a small description (such as `chars of <my_string>`) in case assertions are
    /// transformed.
    #[must_use]
    pub fn new(data: T, expression: String) -> AssertThat<T> {
        AssertThat { data, expression }
    }
}

/// This macro starts every assertion. It takes an expression and returns an [AssertThat] instance
/// which allows to perform various assertions on the value generated by the expression. Remember to
/// import [prelude] in order to get access to all assertions. That import also provides this macro.
///
/// As an example, consider the valid assertion below.
///
/// ```
/// use kernal::prelude::*;
///
/// assert_that!(1 + 1).is_equal_to(2);
/// ```
#[macro_export]
macro_rules! assert_that {
    ($expression:expr) => {
        $crate::AssertThat::new($expression, stringify!($expression).to_owned())
    };
}

/// This type is used to generate error messages of a specific format. It is mostly used internally,
/// but exported to enable users to extend the assertions provided by this crate for custom types.
pub struct Failure {
    expression: String,
    expected_it: Option<String>,
    but_it: Option<String>,
}

impl Failure {
    /// Creates a new failure that takes the possible information from the [AssertThat] on whose
    /// data the failed assertion is run.
    #[must_use]
    pub fn new<T>(assert_that: &AssertThat<T>) -> Failure {
        Failure::from_expression(&assert_that.expression)
    }

    /// Creates a new failure for an assertion on a value that was obtained by evaluating the given
    /// `expression`. This should ideally represent the actual Rust code.
    #[must_use]
    pub fn from_expression(expression: impl Into<String>) -> Failure {
        Failure {
            expression: expression.into(),
            expected_it: None,
            but_it: None,
        }
    }

    /// Specifies the string to display in the error message to represent the expectation.
    /// Grammatically, it should follow the words "expected it".
    #[must_use]
    pub fn expected_it(mut self, expected_it: impl Into<String>) -> Failure {
        self.expected_it = Some(expected_it.into());
        self
    }

    /// Specifies the string to display in the error message to represent the actual value and
    /// failure. Grammatically, it should follow the words "but it" after the phrase generated by
    /// [Failure::expected_it].
    #[must_use]
    pub fn but_it(mut self, but_it: impl Into<String>) -> Failure {
        self.but_it = Some(but_it.into());
        self
    }

    /// Shorthand for [Failure::but_it] where the message is "was ..." with "..." being set to the
    /// [Debug] formatting of the data tested by the given `assert_that`.
    #[must_use]
    pub fn but_it_was_data<T: Debug>(self, assert_that: &AssertThat<T>) -> Failure {
        self.but_it(format!("was <{:?}>", &assert_that.data))
    }

    /// Panics with a failure message composed by arguments of previous method calls on this
    /// failure, such as [Failure::expected_it] and [Failure::but_it]
    pub fn fail(&self) -> ! {
        panic!("{}", self.message());
    }

    fn message(&self) -> String {
        let expected_it = self
            .expected_it
            .as_ref()
            .expect("incomplete failure: no expected_it provided");
        let but_it = self
            .but_it
            .as_ref()
            .expect("incomplete failure: no but_it provided");

        format!(
            "expected: <{}> {}\nbut:      it {}",
            &self.expression, expected_it, but_it
        )
    }
}

/// This trait provides access to the tested data of an [AssertThat] to write custom assertions.
pub trait AssertThatData<T> {
    /// Gets a reference to the tested data. When writing a custom assertion, this is the data on
    /// which you check conditions.
    fn data(&self) -> &T;

    /// Gets a string representing the actual code that evaluated to the tested data. This may also
    /// be a small description (such as `chars of <my_string>`) in case assertions are transformed.
    fn expression(&self) -> &str;

    /// Converts this assert-that instance into a tuple containing the tested data and expression
    /// [String].
    fn into_parts(self) -> (T, String);
}

impl<T> AssertThatData<T> for AssertThat<T> {
    fn data(&self) -> &T {
        &self.data
    }

    fn expression(&self) -> &str {
        &self.expression
    }

    fn into_parts(self) -> (T, String) {
        (self.data, self.expression)
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn assert_that_contains_correct_data() {
        assert_eq!(assert_that!(0).data, 0);
    }

    #[test]
    fn assert_that_contains_correct_expression() {
        assert_eq!(&assert_that!(1 + (2 * 3)).expression, "1 + (2 * 3)");
    }

    #[test]
    #[should_panic(expected = "expected: <a> b\nbut:      it c")]
    fn failure_panics_with_correct_message() {
        let assert_that = AssertThat {
            data: 0,
            expression: "a".to_owned(),
        };

        Failure::new(&assert_that)
            .expected_it("b")
            .but_it("c")
            .fail();
    }
}
