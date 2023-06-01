//! Contains equality-based assertions for [Collection]s with items that implement [Eq] and [Ord],
//! using the additional constraints to optimize runtime. See [CollectionEqOrdAssertions] for more
//! details.

use std::borrow::Borrow;
use std::collections::BTreeSet;
use std::fmt::Debug;

use crate::AssertThat;
use crate::collections::Collection;
use crate::collections::partial_eq::{
    check_contains_all_of,
    check_contains_exactly_in_any_order,
    check_contains_none_of
};
use crate::util::borrow_all;
use crate::util::multiset::btree::BTreeMultiset;

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with an
/// argument that implements the [Collection] trait where the [Collection::Item] type implements
/// [Eq] and [Ord] in addition to the required [Debug] trait. It offers optimized assertions which
/// benefit from the additional [Ord] constraint in terms of runtime.
///
/// Examples:
///
/// ```
/// use kernal::prelude::*;
/// use kernal::fast_prelude::*;
///
/// assert_that!(&[2, 3, 5, 7, 11])
///     .contains_exactly_in_any_order_using_ord([3, 7, 2, 11, 5])
///     .contains_none_of_using_ord([4, 6, 8, 10, 12]);
/// ```
pub trait CollectionEqOrdAssertions<'collection, C>
where
    C: Collection<'collection>
{
    /// Asserts that for each of the given `items`, the tested collection contains an equal element
    /// according to [Eq] and [Ord]. If the provided iterator contains multiple equal elements, this
    /// function asserts that the tested collection contains at least that number of equal elements,
    /// so `[1, 1, 2]` contains all of `[1, 1]`, but not all of `[1, 1, 1]`.
    ///
    /// This can be considered a faster alternative to
    /// [CollectionPartialEqAssertions::contains_all_of](crate::collections::partial_eq::CollectionPartialEqAssertions::contains_all_of)
    /// with the trade-off of additional trait bounds.
    fn contains_all_of_using_ord<E, I>(self, items: I) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>;

    /// Asserts that the tested collection contains no element which is equal to one the given
    /// `items` according to [Eq] and [Ord].
    ///
    /// This can be considered a faster alternative to
    /// [CollectionPartialEqAssertions::contains_none_of](crate::collections::partial_eq::CollectionPartialEqAssertions::contains_none_of)
    /// with the trade-off of additional trait bounds.
    fn contains_none_of_using_ord<E, I>(self, items: I) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>;

    /// Asserts that there is a one-to-one matching of the given `items` and the elements of the
    /// tested collection such that matched elements are equal according to [Eq] and [Ord].
    ///
    /// This can be considered a faster alternative to
    /// [CollectionPartialEqAssertions::contains_exactly_in_any_order](crate::collections::partial_eq::CollectionPartialEqAssertions::contains_exactly_in_any_order)
    /// with the trade-off of additional trait bounds.
    fn contains_exactly_in_any_order_using_ord<E, I>(self, items: I) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>;
}

impl<'collection, C> CollectionEqOrdAssertions<'collection, C> for AssertThat<C>
where
    C: Collection<'collection>,
    C::Item: Debug + Eq + Ord
{
    fn contains_all_of_using_ord<E, I>(self, items: I) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>
    {
        let expected_items_unborrowed = items.into_iter().collect::<Vec<_>>();
        let expected_items: Vec<&C::Item> = borrow_all(&expected_items_unborrowed);

        check_contains_all_of::<_, _, BTreeMultiset<_>>(&self, self.data.iterator(), &expected_items);

        self
    }

    fn contains_none_of_using_ord<E, I>(self, items: I) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>
    {
        let unexpected_items_unborrowed = items.into_iter().collect::<Vec<_>>();
        let unexpected_items: Vec<&C::Item> = borrow_all(&unexpected_items_unborrowed);

        check_contains_none_of::<_, _, BTreeSet<_>>(&self, self.data.iterator(), unexpected_items);

        self
    }

    fn contains_exactly_in_any_order_using_ord<E, I>(self, items: I) -> Self
    where
        E: Borrow<C::Item>,
        I: IntoIterator<Item = E>
    {
        let expected_items_unborrowed = items.into_iter().collect::<Vec<_>>();
        let expected_items: Vec<&C::Item> = borrow_all(&expected_items_unborrowed);

        check_contains_exactly_in_any_order::<_, _, BTreeMultiset<_>>(
            &self, self.data.iterator(), &expected_items);

        self
    }
}

#[cfg(test)]
mod tests {

    use crate::{
        assert_fails,
        test_contains_all_of,
        test_contains_exactly_in_any_order,
        test_contains_none_of
    };
    use crate::prelude::*;

    use super::*;

    test_contains_all_of!(contains_all_of_using_ord);

    test_contains_none_of!(contains_none_of_using_ord);

    test_contains_exactly_in_any_order!(contains_exactly_in_any_order_using_ord);
}
