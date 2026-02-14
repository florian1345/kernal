//! Contains equality-based assertions for [Map]s with values that implement [Eq] and [Hash], using
//! the additional constraints to optimize runtime. See [MapEqHashAssertions] for more details.

use std::borrow::Borrow;
use std::fmt::Debug;
use std::hash::Hash;

use crate::AssertThat;
use crate::maps::Map;
use crate::maps::partial_eq::{check_contains_exactly_values, check_contains_values};
use crate::util::borrow_all;
use crate::util::multiset::hash::HashMultiset;

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with an
/// argument that implements the [Map] trait where the [Map::Value] type implements [Eq] and [Hash]
/// in addition to [Debug] on both keys and values. It offers optimized assertions which benefit
/// from the additional [Hash] constraint in terms of runtime.
///
/// Examples:
///
/// ```
/// use kernal::prelude::*;
/// use kernal::fast_prelude::*;
/// use std::collections::HashMap;
///
/// assert_that!(HashMap::from([("hello", 100), ("world", 200)]))
///     .contains_exactly_values_using_hash([200, 100]);
/// ```
pub trait MapEqHashAssertions<M: Map> {
    /// Asserts that for each of the given `values`, the tested map contains an entry with a value
    /// equal to it according to [Eq] and [Hash]. If the provided iterator contains multiple equal
    /// values, this function asserts that the tested map contains at least that number of equal
    /// values, so `[ k1 => 1, k2 => 1, k3 => 2]` contains values `[1, 1]`, but not values
    /// `[1, 1, 1]`.
    ///
    /// This can be considered a faster alternative to
    /// [MapPartialEqAssertions::contains_values](crate::maps::partial_eq::MapPartialEqAssertions::contains_values)
    /// with the trade-off of additional trait bounds.
    fn contains_values_using_hash<V, I>(self, values: I) -> Self
    where
        V: Borrow<M::Value>,
        I: IntoIterator<Item = V>;

    /// Asserts that there is a one-to-one matching of the given `values` and the values of the
    /// tested map such that matched elements are equal according to [Eq] and [Hash].
    ///
    /// This can be considered a faster alternative to
    /// [MapPartialEqAssertions::contains_exactly_values](crate::maps::partial_eq::MapPartialEqAssertions::contains_exactly_values)
    /// with the trade-off of additional trait bounds.
    fn contains_exactly_values_using_hash<V, I>(self, values: I) -> Self
    where
        V: Borrow<M::Value>,
        I: IntoIterator<Item = V>;
}

impl<M> MapEqHashAssertions<M> for AssertThat<M>
where
    M: Map,
    M::Key: Debug,
    M::Value: Debug + Eq + Hash,
{
    fn contains_values_using_hash<V, I>(self, values: I) -> Self
    where
        V: Borrow<M::Value>,
        I: IntoIterator<Item = V>,
    {
        let expected_values_unborrowed = values.into_iter().collect::<Vec<_>>();
        let expected_values: Vec<&M::Value> = borrow_all(&expected_values_unborrowed);

        check_contains_values::<_, _, HashMultiset<_>>(&self, self.data.values(), &expected_values);

        self
    }

    fn contains_exactly_values_using_hash<V, I>(self, values: I) -> Self
    where
        V: Borrow<M::Value>,
        I: IntoIterator<Item = V>,
    {
        let expected_values_unborrowed = values.into_iter().collect::<Vec<_>>();
        let expected_values: Vec<&M::Value> = borrow_all(&expected_values_unborrowed);

        check_contains_exactly_values::<_, _, HashMultiset<_>>(
            &self,
            self.data.values(),
            &expected_values,
        );

        self
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, HashMap};

    use super::*;
    use crate::prelude::*;
    use crate::{assert_fails, test_contains_exactly_values, test_contains_values};

    test_contains_values!(contains_values_using_hash);

    test_contains_exactly_values!(contains_exactly_values_using_hash);
}
