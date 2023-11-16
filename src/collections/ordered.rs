//! Defines the [OrderedCollection] trait for [Collection] with item ordering.

use std::collections::{BTreeSet, LinkedList, VecDeque};
use std::fmt::Debug;
use crate::{AssertThat, Failure};

use crate::collections::{Collection, CollectionDebug};

/// A marker trait for ordered [Collection]s whose item ordering is deliberate, specified by the
/// iteration order of [Collection::iterator]. It is implemented for all ordered collection types of
/// the standard library.
pub trait OrderedCollection<'collection>: Collection<'collection> {}

impl<'collection, T: 'collection> OrderedCollection<'collection> for [T] {}

impl<'collection, T: 'collection, const N: usize> OrderedCollection<'collection> for [T; N] {}

impl<'collection, T: 'collection> OrderedCollection<'collection> for Vec<T> {}

impl<'collection, T: 'collection> OrderedCollection<'collection> for VecDeque<T> {}

impl<'collection, T: 'collection> OrderedCollection<'collection> for LinkedList<T> {}

impl<'collection, T: 'collection> OrderedCollection<'collection> for BTreeSet<T> {}

impl<'collection, C> OrderedCollection<'collection> for &C
where
    C: OrderedCollection<'collection> + ?Sized
{}

impl<'collection, C> OrderedCollection<'collection> for &mut C
where
    C: OrderedCollection<'collection> + ?Sized
{}

impl<'collection, C> OrderedCollection<'collection> for Box<C>
where
    C: OrderedCollection<'collection> + ?Sized
{}

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with an
/// argument that implements the [OrderedCollection] trait. The [Collection::Item] type must
/// implement [Debug].
///
/// Examples:
///
/// ```
/// use kernal::prelude::*;
///
/// assert_that!(vec![1, 2, 3])
///     .satisfies_exactly_in_given_order(dyn_assertions!(
///         |&it| assert_that!(it).is_odd(),
///         |&it| assert_that!(it).is_even(),
///         |&it| assert_that!(it).is_greater_than(2)));
/// ```
pub trait OrderedCollectionAssertions<'collection, C>
where
    C: OrderedCollection<'collection>
{
    /// Asserts that each item in the tested collection satisfies the assertion at the corresponding
    /// position in the given `assertions` slice, that is, the assertion runs without panicking. The
    /// collection and `assertions` are also asserted to have the same size. **The return value of
    /// the closures is ignored, so returning `false` does not constitute an assertion failure.**
    ///
    /// For convenience, it is recommended to use the [dyn_assertions](crate::dyn_assertions) macro
    /// for constructing the assertions.
    #[allow(clippy::type_complexity)]
    fn satisfies_exactly_in_given_order(self, assertions: &[Box<dyn Fn(&C::Item)>]) -> Self;
}

impl<'collection, C> OrderedCollectionAssertions<'collection, C> for AssertThat<C>
where
    C: OrderedCollection<'collection>,
    C::Item: Debug
{
    fn satisfies_exactly_in_given_order(self, assertions: &[Box<dyn Fn(&C::Item)>]) -> Self {
        let len = self.data.len();
        let expected_len = assertions.len();

        if len != expected_len {
            Failure::new(&self)
                .expected_it(format!("to satisfy exactly in the given order <{}> given assertions",
                    expected_len))
                .but_it(format!("had <{}> items, namely <{:?}>",
                    len, CollectionDebug { collection: &self.data }))
                .fail()
        }

        for (item, assertion) in self.data.iterator().zip(assertions.iterator()) {
            assertion(item);
        }

        self
    }
}

/// A utility macro for constructing slices of assertion trait objects, that is, boxed functions
/// which take some input and have no output. These are used as input to assertions which distribute
/// items over assertions, such as [OrderedCollectionAssertions::satisfies_exactly_in_given_order].
/// It accepts patterns in the form of a list of lambda expressions, ignores the output of each one
/// and wraps it in a box.
///
/// Example:
///
/// ```
/// use kernal::prelude::*;
///
/// let boxes: &[Box<dyn Fn(&u32)>] = dyn_assertions!(
///     |it| assert_that!(*it).is_even(),
///     |&it| {
///         assert_that!(it).is_odd();
///         assert_that!(it + 1).is_greater_than(3);
///     }
/// );
/// ```
///
/// This becomes:
///
/// ```
/// use kernal::prelude::*;
///
/// let boxes: &[Box<dyn Fn(&u32)>] = &[
///     Box::new(|it| { assert_that!(*it).is_even(); }),
///     Box::new(|&it| {
///         {
///             assert_that!(it).is_odd();
///             assert_that!(it + 1).is_greater_than(3);
///         };
///     })
/// ];
/// ```
#[macro_export]
macro_rules! dyn_assertions {
    ($(|$param:pat_param| $assertions:expr),*) => {
        &[$(Box::new(|$param| { $assertions; }),)*]
    };
}

#[cfg(test)]
mod tests {

    use super::*;

    use crate::assert_fails;
    use crate::prelude::*;

    #[test]
    fn satisfies_exactly_in_given_order_passes_with_empty_collections() {
        assert_that!([] as [&str; 0]).satisfies_exactly_in_given_order(dyn_assertions!());
    }

    #[test]
    fn satisfies_exactly_in_given_order_passes_with_non_empty_collections() {
        assert_that!(["hello", "world"] as [&str; 2]).satisfies_exactly_in_given_order(dyn_assertions!(
            |item| assert_that!(item).starts_with("h"),
            |item| assert_that!(item).starts_with("w")
        ));
    }

    #[test]
    fn satisfies_exactly_in_given_order_fails_for_too_short_collection() {
        assert_fails!((["hello"]).satisfies_exactly_in_given_order(dyn_assertions!(
                |item| assert_that!(*item).has_char_length(5),
                |item| assert_that!(*item).has_char_length(6))),
            expected it "to satisfy exactly in the given order <2> given assertions"
            but it "had <1> items, namely <[ \"hello\" ]>");
    }

    #[test]
    fn satisfies_exactly_in_given_order_fails_for_too_long_collection() {
        assert_fails!((["hello", "big", "world"]).satisfies_exactly_in_given_order(dyn_assertions!(
                |item| assert_that!(*item).has_char_length(5),
                |item| assert_that!(*item).has_char_length(3))),
            expected it "to satisfy exactly in the given order <2> given assertions"
            but it "had <3> items, namely <[ \"hello\", \"big\", \"world\" ]>");
    }

    #[test]
    fn satisfies_exactly_in_given_order_fails_if_first_assertion_fails() {
        assert_that!(|| {
            assert_that!(["hello", "world"]).satisfies_exactly_in_given_order(dyn_assertions!(
                |_| panic!("first assertion failed"),
                |_| { }
            ));
        }).panics_with_message("first assertion failed");
    }

    #[test]
    fn satisfies_exactly_in_given_order_fails_if_second_assertion_fails() {
        assert_that!(|| {
            assert_that!(["hello", "world"]).satisfies_exactly_in_given_order(dyn_assertions!(
                |_| { },
                |_| panic!("second assertion failed")
            ));
        }).panics_with_message("second assertion failed");
    }

    #[test]
    fn satisfies_exactly_in_given_order_fails_for_real_assertion_failure() {
        assert_that!(|| {
            assert_that!(["apple", "banana", "cherry"]).satisfies_exactly_in_given_order(dyn_assertions!(
                |&item| assert_that!(item).has_char_length(5),
                |&item| assert_that!(item).ends_with("na"),
                |&item| assert_that!(item).is_equal_to("cucumber")
            ));
        }).panics();
    }
}
