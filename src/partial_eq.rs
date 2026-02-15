//! Contains assertions for values which implement [PartialEq]. See [PartialEqAssertions] for more
//! details.

use std::borrow::Borrow;
use std::fmt::Debug;

use crate::collections::{CollectionDebug, HighlightedCollectionDebug};
use crate::util::borrow_all;
use crate::{AssertThat, Failure};

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with an
/// argument that implements the [PartialEq] trait.
///
/// Examples:
///
/// ```
/// use kernal::prelude::*;
///
/// assert_that!(1 + 1).is_equal_to(2).is_equal_to_none([1, 3]);
/// ```
pub trait PartialEqAssertions<T> {
    /// Asserts that the tested value is equal to the given `expected` value according to the
    /// [PartialEq] trait.
    fn is_equal_to<E: Borrow<T>>(self, expected: E) -> Self;

    /// Asserts that the tested value is different from the given `expected` value according to the
    /// [PartialEq] trait.
    fn is_not_equal_to<E: Borrow<T>>(self, expected: E) -> Self;

    /// Asserts that the tested value is equal to one element from the given `expected_iter`
    /// according to the [PartialEq] trait.
    fn is_equal_to_any<E: Borrow<T>, I: IntoIterator<Item = E>>(self, expected_iter: I) -> Self;

    /// Asserts that the tested value is not equal to any element from the given `unexpected_iter`
    /// according to the [PartialEq] trait.
    fn is_equal_to_none<E: Borrow<T>, I: IntoIterator<Item = E>>(self, unexpected_iter: I) -> Self;
}

impl<T: Debug + PartialEq> PartialEqAssertions<T> for AssertThat<T> {
    fn is_equal_to<E: Borrow<T>>(self, expected: E) -> Self {
        let expected_data = expected.borrow();

        if &self.data != expected_data {
            Failure::new(&self)
                .expected_it(format!("to equal <{:?}>", expected_data))
                .but_it_was_data(&self)
                .fail();
        }

        self
    }

    fn is_not_equal_to<E: Borrow<T>>(self, expected: E) -> Self {
        let expected_data = expected.borrow();

        if &self.data == expected_data {
            Failure::new(&self)
                .expected_it(format!("not to equal <{:?}>", expected_data))
                .but_it("did")
                .fail();
        }

        self
    }

    fn is_equal_to_any<E: Borrow<T>, I: IntoIterator<Item = E>>(self, expected_iter: I) -> Self {
        let expected_vec_unborrowed = expected_iter.into_iter().collect::<Vec<_>>();
        let expected_vec: Vec<&T> = borrow_all(&expected_vec_unborrowed);

        if expected_vec.contains(&&self.data) {
            return self;
        }

        let collection_debug = CollectionDebug {
            collection: &expected_vec,
        };

        Failure::new(&self)
            .expected_it(format!("to equal any of <{:?}>", collection_debug))
            .but_it_was_data(&self)
            .fail()
    }

    fn is_equal_to_none<E: Borrow<T>, I: IntoIterator<Item = E>>(self, unexpected_iter: I) -> Self {
        let unexpected_vec_unborrowed = unexpected_iter.into_iter().collect::<Vec<_>>();
        let unexpected_vec: Vec<&T> = borrow_all(&unexpected_vec_unborrowed);

        let counter_example_index = unexpected_vec
            .iter()
            .enumerate()
            .find(|(_, unexpected)| &self.data == **unexpected)
            .map(|(index, _)| index);

        if let Some(counter_example_index) = counter_example_index {
            let collection_debug = HighlightedCollectionDebug {
                collection: &unexpected_vec,
                highlighted_sections: vec![counter_example_index..(counter_example_index + 1)],
            };

            Failure::new(&self)
                .expected_it(format!("not to equal any of <{:?}>", collection_debug))
                .but_it_was_data(&self)
                .fail();
        }

        self
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::{assert_fails, assert_that};

    struct U32Wrapper {
        data: u32,
    }

    impl Borrow<u32> for U32Wrapper {
        fn borrow(&self) -> &u32 {
            &self.data
        }
    }

    #[test]
    fn is_equal_to_passes_for_equal_integers() {
        assert_that!(1 + 2).is_equal_to(3);
    }

    #[test]
    fn is_equal_to_passes_for_u32_with_equivalent_u32_wrapper() {
        assert_that!(42).is_equal_to(U32Wrapper { data: 42 });
    }

    #[test]
    fn is_equal_to_fails_for_different_integers() {
        assert_fails!((1 - 1).is_equal_to(-1), expected it "to equal <-1>" but it "was <0>");
    }

    #[test]
    fn is_equal_to_fails_for_u32_with_non_equivalent_u32_wrapper() {
        assert_fails!((21 + 21).is_equal_to(U32Wrapper { data: 43 }),
            expected it "to equal <43>"
            but it "was <42>");
    }

    #[test]
    fn is_not_equal_to_passes_for_different_integers() {
        assert_that!(1 + 2).is_not_equal_to(4);
    }

    #[test]
    fn is_not_equal_to_passes_for_u32_with_non_equivalent_u32_wrapper() {
        assert_that!(42).is_not_equal_to(U32Wrapper { data: 43 });
    }

    #[test]
    fn is_not_equal_to_fails_for_equal_integers() {
        assert_fails!((1 - 1).is_not_equal_to(0), expected it "not to equal <0>" but it "did");
    }

    #[test]
    fn is_not_equal_to_fails_for_u32_with_equivalent_u32_wrapper() {
        assert_fails!((21 + 21).is_not_equal_to(U32Wrapper { data: 42 }),
            expected it "not to equal <42>"
            but it "did");
    }

    #[test]
    fn is_equal_to_any_passes_for_singleton_list_containing_tested_element() {
        assert_that!(42).is_equal_to_any([42]);
    }

    #[test]
    fn is_equal_to_any_passes_for_list_containing_tested_element_later() {
        assert_that!(36).is_equal_to_any([35, 36, 37]);
    }

    #[test]
    fn is_equal_to_any_fails_for_empty_list() {
        assert_fails!((42).is_equal_to_any([] as [i32; 0]),
            expected it "to equal any of <[ ]>"
            but it "was <42>");
    }

    #[test]
    fn is_equal_to_any_fails_for_larger_list_not_containing_tested_element() {
        assert_fails!((36).is_equal_to_any([12, 13, 35, 37, 42]),
            expected it "to equal any of <[ 12, 13, 35, 37, 42 ]>"
            but it "was <36>");
    }

    #[test]
    fn is_equal_to_none_passes_for_empty_list() {
        assert_that!(42).is_equal_to_none([] as [i32; 0]);
    }

    #[test]
    fn is_equal_to_none_passes_for_larger_list_not_containing_tested_element() {
        assert_that!(36).is_equal_to_none([12, 13, 35, 37, 42]);
    }

    #[test]
    fn is_equal_to_none_fails_for_singleton_list_containing_tested_element() {
        assert_fails!((42).is_equal_to_none([42]),
            expected it "not to equal any of <[ [42] ]>"
            but it "was <42>");
    }

    #[test]
    fn is_equal_to_none_fails_for_list_containing_tested_element_later() {
        assert_fails!((36).is_equal_to_none([35, 36, 37]),
            expected it "not to equal any of <[ 35, [36], 37 ]>"
            but it "was <36>");
    }
}
