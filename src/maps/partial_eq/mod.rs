//! Contains specialized assertions for [Map]s and whose [Map::Value]s implement [PartialEq]. See
//! [MapPartialEqAssertions] for more details.

use crate::{AssertThat, Failure};
use crate::collections::CollectionDebug;
use crate::collections::partial_eq::{
    compute_missing_and_superfluous,
    format_error_for_missing_and_superfluous
};
use crate::maps::Map;
use crate::maps::debug::{HighlightedMapDebug, MapDebug, MapEntriesDebug};
use crate::util::{borrow_all, borrow_all_pairs};
use crate::util::multiset::Multiset;
use crate::util::multiset::vec::VecMultiset;

use std::borrow::Borrow;
use std::fmt::Debug;

pub mod hash;

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with an
/// argument that implements the [Map] trait whose [Map::Value] implements [PartialEq] in addition
/// to [Debug] on both keys and values.
///
/// Examples:
///
/// ```
/// use kernal::prelude::*;
/// use std::collections::HashMap;
///
/// assert_that!(HashMap::from([("hello", 100), ("world", 200)]))
///     .contains_value(100)
///     .contains_entry("world", 200);
/// ```
pub trait MapPartialEqAssertions<'map, M: Map<'map>> {

    /// Asserts that the tested map contains an entry with a value equal to the given `value`
    /// according to [PartialEq], mapped to any key.
    fn contains_value<V: Borrow<M::Value>>(self, value: V) -> Self;

    /// Asserts that the tested map contains no entry with a value equal to the given `value`
    /// according to [PartialEq], mapped to any key.
    fn does_not_contain_value<V: Borrow<M::Value>>(self, value: V) -> Self;

    /// Asserts that for each of the given `values`, the tested map contains an entry with a value
    /// equal to it according to [PartialEq]. If the provided iterator contains multiple equal
    /// values, this function asserts that the tested map contains at least that number of equal
    /// values, so `[ k1 => 1, k2 => 1, k3 => 2]` contains values `[1, 1]`, but not values
    /// `[1, 1, 1]`.
    fn contains_values<V, I>(self, values: I) -> Self
    where
        V: Borrow<M::Value>,
        I: IntoIterator<Item = V>;

    /// Asserts that for each of the given `values`, the tested map contains no entry with a value
    /// equal to it according to [PartialEq].
    fn does_not_contain_values<V, I>(self, values: I) -> Self
    where
        V: Borrow<M::Value>,
        I: IntoIterator<Item = V>;

    /// Asserts that there is a one-to-one matching of the given `values` and the values of the
    /// tested map such that matched elements are equal according to [PartialEq].
    fn contains_exactly_values<V, I>(self, values: I) -> Self
    where
        V: Borrow<M::Value>,
        I: IntoIterator<Item = V>;

    /// Asserts that the tested map contains a value equal to the given `value` according to
    /// [PartialEq], mapped to the given `key`
    fn contains_entry<K, V>(self, key: K, value: V) -> Self
    where
        K: Borrow<M::Key>,
        V: Borrow<M::Value>;

    /// Asserts that the tested map does not contain the given `key` or maps a value to it which is
    /// not equal to the given `value` according to [PartialEq].
    fn does_not_contain_entry<K, V>(self, key: K, value: V) -> Self
    where
        K: Borrow<M::Key>,
        V: Borrow<M::Value>;

    /// Asserts that for each of the given `entries`, the tested map contains its key and maps it to
    /// a value equal to the entry's value according to [PartialEq]. Duplicate entries in the given
    /// iterator will be checked individually and matched by the same entry in the tested map.
    fn contains_entries<K, V, I>(self, entries: I) -> Self
    where
        K: Borrow<M::Key>,
        V: Borrow<M::Value>,
        I: IntoIterator<Item = (K, V)>;

    /// Asserts that for each of the given `entries`, the tested map does not contain its key or
    /// maps it to a value different from the entry's value according to [PartialEq]. Duplicate
    /// entries in the given iterator will be checked individually and matched by the same entry in
    /// the tested map.
    fn does_not_contain_entries<K, V, I>(self, entries: I) -> Self
    where
        K: Borrow<M::Key>,
        V: Borrow<M::Value>,
        I: IntoIterator<Item = (K, V)>;

    /// Asserts that for each of the given `entries`, the tested map contains its key and maps it to
    /// a value equal to the entry's value according to [PartialEq]. In addition, the tested map is
    /// required not to contain any keys which are not also contained in `entries`. Duplicate keys
    /// in the given iterator will be checked individually and matched by the same entry in the
    /// tested map. If the associated values are different, the assertion will become impossible.
    fn contains_exactly_entries<K, V, I>(self, entries: I) -> Self
    where
        K: Borrow<M::Key>,
        V: Borrow<M::Value>,
        I: IntoIterator<Item = (K, V)>;
}

fn get_key<'map, 'reference, M>(map: &'reference M, value: &M::Value) -> Option<&'reference M::Key>
where
    M: Map<'map>,
    M::Value: PartialEq,
    'map: 'reference
{
    map.entries().find(|&(_, map_value)| map_value == value).map(|(key, _)| key)
}

fn check_violating_key_for_entries_check<'map, M>(assert_that: &AssertThat<M>,
    violating_key: Option<&M::Key>, entries: &[(&M::Key, &M::Value)], expected_it_prefix: &str)
where
    M: Map<'map>,
    M::Key: Debug,
    M::Value: Debug
{
    if let Some(violating_key) = violating_key {
        let map_entries_debug = MapEntriesDebug::<'_, '_, M>::new(entries.iter().cloned());
        let failure = Failure::new(assert_that)
            .expected_it(format!("{} <{:?}>", expected_it_prefix, map_entries_debug));

        if assert_that.data.get(violating_key).is_some() {
            let highlighted_map_debug = HighlightedMapDebug {
                map: &assert_that.data,
                highlighted_key: violating_key
            };

            failure
                .but_it(format!("was <{:?}>", highlighted_map_debug))
                .fail()
        }
        else {
            let map_debug = MapDebug { map: &assert_that.data };

            failure
                .but_it(format!("was <{:?}>, which is missing the key <{:?}>",
                    map_debug, violating_key))
                .fail()
        }
    }
}

fn check_contains_values<'map, 'value, M, I, MS>(assert_that: &AssertThat<M>, actual_values: I,
    expected_values: &'value [&M::Value])
where
    M: Map<'map>,
    M::Key: Debug,
    M::Value: Debug + 'value,
    I: Iterator<Item = &'value M::Value>,
    MS: Multiset<&'value M::Value>
{
    let (missing_values, _) =
        compute_missing_and_superfluous::<_, MS, _>(actual_values, expected_values);

    if !missing_values.is_empty() {
        let values_debug = CollectionDebug { collection: &expected_values };
        let map_debug = MapDebug { map: &assert_that.data };

        Failure::new(assert_that)
            .expected_it(format!("to contain all of the values <{:?}>", values_debug))
            .but_it(format!("was <{:?}>, which lacks {:?}", map_debug, missing_values))
            .fail();
    }
}

fn check_contains_exactly_values<'map, 'value, M, I, MS>(assert_that: &AssertThat<M>,
    actual_values: I, expected_values: &'value [&M::Value])
where
    M: Map<'map>,
    M::Key: Debug,
    M::Value: Debug + 'value,
    I: Iterator<Item = &'value M::Value>,
    MS: Multiset<&'value M::Value>
{
    let (missing_values, superfluous_values) =
        compute_missing_and_superfluous::<_, MS, _>(actual_values, expected_values);

    if !missing_values.is_empty() || !superfluous_values.is_empty() {
        let expected_values_debug = CollectionDebug { collection: &expected_values };
        let map_debug = MapDebug { map: &assert_that.data };
        let error =
            format_error_for_missing_and_superfluous(&missing_values, &superfluous_values);

        Failure::new(assert_that)
            .expected_it(format!("to contain exactly the values <{:?}>", expected_values_debug))
            .but_it(format!("was <{:?}>, which {}", map_debug, error))
            .fail();
    }
}

impl<'map, M> MapPartialEqAssertions<'map, M> for AssertThat<M>
where
    M: Map<'map>,
    M::Key: Debug,
    M::Value: Debug + PartialEq
{
    fn contains_value<V: Borrow<M::Value>>(self, value: V) -> Self {
        let value = value.borrow();

        if get_key(&self.data, value).is_none() {
            Failure::new(&self)
                .expected_it(format!("to contain the value <{:?}>", value))
                .but_it(format!("was <{:?}>", MapDebug { map: &self.data }))
                .fail();
        }

        self
    }

    fn does_not_contain_value<V: Borrow<M::Value>>(self, value: V) -> Self {
        let value = value.borrow();

        if let Some(key) = get_key(&self.data, value) {
            let highlighted_map_debug = HighlightedMapDebug {
                map: &self.data,
                highlighted_key: key
            };

            Failure::new(&self)
                .expected_it(format!("not to contain the value <{:?}>", value))
                .but_it(format!("was <{:?}>", highlighted_map_debug))
                .fail();
        }

        self
    }

    fn contains_values<V, I>(self, values: I) -> Self
    where
        V: Borrow<M::Value>,
        I: IntoIterator<Item = V>
    {
        let expected_values_unborrowed = values.into_iter().collect::<Vec<_>>();
        let expected_values: Vec<&M::Value> = borrow_all(&expected_values_unborrowed);

        check_contains_values::<_, _, VecMultiset<_>>(&self, self.data.values(), &expected_values);

        self
    }

    fn does_not_contain_values<V, I>(self, values: I) -> Self
    where
        V: Borrow<M::Value>,
        I: IntoIterator<Item = V>
    {
        let expected_values_unborrowed = values.into_iter().collect::<Vec<_>>();
        let expected_values: Vec<&M::Value> = borrow_all(&expected_values_unborrowed);
        let violating_key = expected_values.iter().find_map(|value| get_key(&self.data, value));

        if let Some(violating_key) = violating_key {
            let values_debug = CollectionDebug { collection: &expected_values };
            let highlighted_map_debug = HighlightedMapDebug {
                map: &self.data,
                highlighted_key: violating_key
            };

            Failure::new(&self)
                .expected_it(format!("to contain none of the values <{:?}>", values_debug))
                .but_it(format!("was <{:?}>", highlighted_map_debug))
                .fail();
        }

        self
    }

    fn contains_exactly_values<V, I>(self, values: I) -> Self
    where
        V: Borrow<M::Value>,
        I: IntoIterator<Item = V>
    {
        let expected_values_unborrowed = values.into_iter().collect::<Vec<_>>();
        let expected_values: Vec<&M::Value> = borrow_all(&expected_values_unborrowed);

        check_contains_exactly_values::<_, _, VecMultiset<_>>(
            &self, self.data.values(), &expected_values);

        self
    }

    fn contains_entry<K, V>(self, key: K, value: V) -> Self
    where
        K: Borrow<M::Key>,
        V: Borrow<M::Value>
    {
        let key = key.borrow();
        let expected_value = value.borrow();
        let failure = Failure::new(&self)
            .expected_it(
                format!("to contain the entry <{:?} => {:?}>", key, expected_value));

        match self.data.get(key) {
            Some(value) if value == expected_value => self,
            Some(value) => {
                let highlighted_map_debug = HighlightedMapDebug {
                    map: &self.data,
                    highlighted_key: key
                };

                failure
                    .but_it(format!("was <{:?}>, which maps the key to the value <{:?}>",
                        highlighted_map_debug, value))
                    .fail()
            },
            None => {
                let map_debug = MapDebug { map: &self.data };

                failure
                    .but_it(format!("was <{:?}>, which does not contain the key", map_debug))
                    .fail()
            }
        }
    }

    fn does_not_contain_entry<K, V>(self, key: K, value: V) -> Self
    where
        K: Borrow<M::Key>,
        V: Borrow<M::Value>
    {
        let key = key.borrow();
        let unexpected_value = value.borrow();

        if self.data.get(key).iter().any(|&value| value == unexpected_value) {
            let highlighted_map_debug = HighlightedMapDebug {
                map: &self.data,
                highlighted_key: key
            };

            Failure::new(&self)
                .expected_it(
                    format!("not to contain the entry <{:?} => {:?}>", key, unexpected_value))
                .but_it(format!("was <{:?}>", highlighted_map_debug))
                .fail()
        }

        self
    }

    fn contains_entries<K, V, I>(self, entries: I) -> Self
    where
        K: Borrow<M::Key>,
        V: Borrow<M::Value>,
        I: IntoIterator<Item = (K, V)>
    {
        let entries_unborrowed = entries.into_iter().collect::<Vec<_>>();
        let entries: Vec<(&M::Key, &M::Value)> = borrow_all_pairs(&entries_unborrowed);
        let violating_key = entries.iter()
            .find(|(key, value)| self.data.get(key).iter().all(|&map_value| map_value != *value))
            .map(|(key, _)| *key);

        check_violating_key_for_entries_check(
            &self, violating_key, &entries, "to contain all of the entries");

        self
    }

    fn does_not_contain_entries<K, V, I>(self, entries: I) -> Self
    where
        K: Borrow<M::Key>,
        V: Borrow<M::Value>,
        I: IntoIterator<Item = (K, V)>
    {
        let entries_unborrowed = entries.into_iter().collect::<Vec<_>>();
        let entries: Vec<(&M::Key, &M::Value)> = borrow_all_pairs(&entries_unborrowed);
        let violating_key = entries.iter()
            .find(|(key, value)| self.data.get(key).iter().any(|&map_value| map_value == *value))
            .map(|(key, _)| *key);

        check_violating_key_for_entries_check(
            &self, violating_key, &entries, "not to contain any of the entries");

        self
    }

    fn contains_exactly_entries<K, V, I>(self, entries: I) -> Self
    where
        K: Borrow<M::Key>,
        V: Borrow<M::Value>,
        I: IntoIterator<Item = (K, V)>
    {
        let entries_unborrowed = entries.into_iter().collect::<Vec<_>>();
        let entries: Vec<(&M::Key, &M::Value)> = borrow_all_pairs(&entries_unborrowed);
        let mut distinct_keys = Vec::new();
        let key_of_wrong_or_missing_entry = entries.iter().cloned()
            .find(|(key, value)| {
                if !distinct_keys.iter().any(|&distinct_key| M::are_keys_equal(distinct_key, key)) {
                    distinct_keys.push(key);
                }

                self.data.get(key).iter().all(|&map_value| map_value != *value)
            })
            .map(|(key, _)| key);

        check_violating_key_for_entries_check(
            &self, key_of_wrong_or_missing_entry, &entries, "to contain exactly the entries");

        let superfluous_key: Option<&M::Key> = self.data.keys()
            .find(|map_key| !distinct_keys.iter()
                .any(|distinct_key| M::are_keys_equal(map_key, distinct_key)));

        if let Some(superfluous_key) = superfluous_key {
            let map_entries_debug = MapEntriesDebug::<'_, '_, M>::new(entries.iter().cloned());
            let highlighted_map_debug = HighlightedMapDebug {
                map: &self.data,
                highlighted_key: superfluous_key
            };

            Failure::new(&self)
                .expected_it(format!("to contain exactly the entries <{:?}>", map_entries_debug))
                .but_it(format!("was <{:?}>, which additionally contains the key <{:?}>",
                    highlighted_map_debug, superfluous_key))
                .fail()
        }

        self
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, HashMap};

    use crate::assert_fails;
    use crate::prelude::*;
    use super::*;

    #[test]
    fn contains_value_passes_for_singleton_map() {
        assert_that!(HashMap::from([("apple", 42)])).contains_value(42);
    }

    #[test]
    fn contains_value_passes_for_map_with_same_value_for_multiple_keys() {
        assert_that!(BTreeMap::from([("apple", 23), ("banana", 23)])).contains_value(23);
    }

    #[test]
    fn contains_value_passes_for_map_with_multiple_values_including_expected_one() {
        assert_that!(BTreeMap::from([("apple", 41), ("banana", 42), ("cherry", 43)]))
            .contains_value(42);
    }

    #[test]
    fn contains_value_fails_for_empty_map() {
        assert_fails!((HashMap::<&str, i32>::new()).contains_value(42),
            expected it "to contain the value <42>"
            but it "was <[ ]>");
    }

    #[test]
    fn contains_value_fails_for_map_with_single_different_value() {
        assert_fails!((BTreeMap::from([("apple", 23)])).contains_value(45),
            expected it "to contain the value <45>"
            but it "was <[ \"apple\" => 23 ]>");
    }

    #[test]
    fn contains_value_fails_for_map_with_multiple_different_values() {
        assert_fails!((BTreeMap::from([("apple", 39), ("banana", 40), ("cherry", 41)]))
            .contains_value(42),
            expected it "to contain the value <42>"
            but it "was <[ \"apple\" => 39, \"banana\" => 40, \"cherry\" => 41 ]>");
    }

    #[test]
    fn does_not_contain_value_passes_for_empty_map() {
        assert_that!(HashMap::<&str, i32>::new()).does_not_contain_value(42);
    }

    #[test]
    fn does_not_contain_value_passes_for_map_with_single_different_value() {
        assert_that!(BTreeMap::from([("apple", 23)])).does_not_contain_value(45);
    }

    #[test]
    fn does_not_contain_value_passes_for_map_with_multiple_different_values() {
        assert_that!(BTreeMap::from([("apple", 39), ("banana", 40), ("cherry", 41)]))
            .does_not_contain_value(42);
    }

    #[test]
    fn does_not_contain_value_fails_for_singleton_map() {
        assert_fails!((HashMap::from([("apple", 42)])).does_not_contain_value(42),
            expected it "not to contain the value <42>"
            but it "was <[ [\"apple\" => 42] ]>");
    }

    #[test]
    fn does_not_contain_value_fails_for_map_with_same_value_for_multiple_keys() {
        assert_fails!((BTreeMap::from([("apple", 23), ("banana", 23)])).does_not_contain_value(23),
            expected it "not to contain the value <23>"
            but it "was <[ [\"apple\" => 23], \"banana\" => 23 ]>");
    }

    #[test]
    fn does_not_contain_value_fails_for_map_with_multiple_values_including_expected_one() {
        assert_fails!((BTreeMap::from([("apple", 41), ("banana", 42), ("cherry", 43)]))
            .does_not_contain_value(42),
            expected it "not to contain the value <42>"
            but it "was <[ \"apple\" => 41, [\"banana\" => 42], \"cherry\" => 43 ]>");
    }

    #[macro_export]
    macro_rules! test_contains_values {
        ($assertion:ident) => {
            #[test]
            fn contains_values_passes_for_empty_expected_values() {
                assert_that!(HashMap::<&str, i32>::new()).$assertion(&[]);
            }

            #[test]
            fn contains_values_passes_for_single_expected_value_on_correct_singleton_map() {
                assert_that!(BTreeMap::from([("apple", 42)])).$assertion(&[42]);
            }

            #[test]
            fn contains_values_passes_for_map_with_proper_superset_of_expected_values() {
                assert_that!(HashMap::from([("apple", 2), ("banana", 3), ("cherry", 4)]))
                    .$assertion(&[2, 4]);
            }

            #[test]
            fn contains_values_passes_for_map_with_exact_multiplicity() {
                assert_that!(HashMap::from([("apple", 2), ("banana", 3), ("cherry", 3)]))
                    .$assertion(&[3, 3]);
            }

            #[test]
            fn contains_values_passes_for_map_with_higher_multiplicity() {
                assert_that!(HashMap::from([("apple", 3), ("banana", 3), ("cherry", 3)]))
                    .$assertion(&[3, 3]);
            }

            #[test]
            fn contains_values_fails_for_empty_map_and_any_expected_value() {
                assert_fails!((HashMap::<&str, i32>::new()).$assertion(&[1]),
                    expected it "to contain all of the values <[ 1 ]>"
                    but it "was <[ ]>, which lacks 1 of <1>");
            }

            #[test]
            fn contains_values_fails_for_single_expected_value_not_in_map() {
                assert_fails!((BTreeMap::from([("apple", 1), ("banana", 2)])).$assertion(&[3]),
                    expected it "to contain all of the values <[ 3 ]>"
                    but it "was <[ \"apple\" => 1, \"banana\" => 2 ]>, which lacks 1 of <3>");
            }

            #[test]
            fn contains_values_fails_for_mixed_expected_values() {
                assert_fails!((BTreeMap::from([("apple", 1), ("banana", 2)])).$assertion(&[2, 3]),
                    expected it "to contain all of the values <[ 2, 3 ]>"
                    but it "was <[ \"apple\" => 1, \"banana\" => 2 ]>, which lacks 1 of <3>");
            }

            #[test]
            fn contains_values_fails_for_map_with_lower_multiplicity() {
                assert_fails!((BTreeMap::from([("apple", 2), ("banana", 3), ("cherry", 4)]))
                    .$assertion(&[3, 3]),
                    expected it "to contain all of the values <[ 3, 3 ]>"
                    but it "was <[ \"apple\" => 2, \"banana\" => 3, \"cherry\" => 4 ]>, \
                        which lacks 1 of <3>");
            }

            #[test]
            fn contains_values_fails_for_map_with_multiple_missing_elements() {
                assert_that!(||
                    assert_that!(BTreeMap::from([("apple", 1), ("banana", 2), ("cherry", 3)]))
                        .$assertion(&[3, 3, 3, 4]))
                    .panics_with_message_matching(|message|
                        message.contains("to contain all of the values <[ 3, 3, 3, 4 ]>") &&
                        message.contains(
                            "was <[ \"apple\" => 1, \"banana\" => 2, \"cherry\" => 3 ]>") &&
                        message.contains("2 of <3>") &&
                        message.contains("1 of <4>"));
            }
        }
    }

    test_contains_values!(contains_values);

    #[test]
    fn does_not_contain_values_passes_for_empty_expected_values() {
        assert_that!(HashMap::<&str, i32>::new()).does_not_contain_values(&[]);
    }

    #[test]
    fn does_not_contain_values_passes_for_empty_map_and_any_expected_value() {
        assert_that!(BTreeMap::<&str, i32>::new()).does_not_contain_values(&[1]);
    }

    #[test]
    fn does_not_contain_values_passes_for_single_expected_value_not_in_map() {
        assert_that!(HashMap::from([("apple", 1), ("banana", 2)])).does_not_contain_values(&[3]);
    }

    #[test]
    fn does_not_contain_values_fails_for_single_expected_value_on_correct_singleton_map() {
        assert_fails!((HashMap::from([("apple", 42)])).does_not_contain_values(&[42]),
            expected it "to contain none of the values <[ 42 ]>"
            but it "was <[ [\"apple\" => 42] ]>");
    }

    #[test]
    fn does_not_contain_values_fails_for_single_expected_value_on_map_with_multiple_values() {
        assert_fails!((BTreeMap::from([("apple", 41), ("banana", 42)]))
            .does_not_contain_values(&[42]),
            expected it "to contain none of the values <[ 42 ]>"
            but it "was <[ \"apple\" => 41, [\"banana\" => 42] ]>");
    }

    #[test]
    fn does_not_contain_values_fails_for_mixed_expected_values() {
        assert_fails!((BTreeMap::from([("apple", 1), ("banana", 2)])).does_not_contain_values(&[2, 3]),
            expected it "to contain none of the values <[ 2, 3 ]>"
            but it "was <[ \"apple\" => 1, [\"banana\" => 2] ]>");
    }


    #[macro_export]
    macro_rules! test_contains_exactly_values {
        ($assertion:ident) => {
            #[test]
            fn contains_exactly_values_passes_for_empty_map_and_no_expected_values() {
                assert_that!(BTreeMap::<&str, i32>::new()).contains_exactly_values(&[] as &[i32]);
            }

            #[test]
            fn contains_exactly_values_passes_for_singleton_map_of_expected_value() {
                assert_that!(HashMap::from([("apple", 42)])).contains_exactly_values(&[42]);
            }

            #[test]
            fn contains_exactly_values_passes_for_larger_map_of_expected_values_in_different_order() {
                assert_that!(BTreeMap::from([("apple", 42), ("banana", 43), ("cherry", 44)]))
                    .contains_exactly_values(&[44, 43, 42] as &[i32]);
            }

            #[test]
            fn contains_exactly_values_passes_for_map_with_correct_higher_multiplicity() {
                assert_that!(HashMap::from([("apple", 42), ("banana", 42)]))
                    .contains_exactly_values(&[42, 42]);
            }

            #[test]
            fn contains_exactly_values_fails_for_empty_map_and_single_expected_value() {
                assert_fails!((HashMap::<&str, i32>::new()).contains_exactly_values(&[42]),
                    expected it "to contain exactly the values <[ 42 ]>"
                    but it "was <[ ]>, which lacks 1 of <42>");
            }

            #[test]
            fn contains_exactly_values_fails_for_singleton_map_and_no_expected_values() {
                assert_fails!((BTreeMap::from([("apple", 42)])).contains_exactly_values(&[] as &[i32]),
                    expected it "to contain exactly the values <[ ]>"
                    but it "was <[ \"apple\" => 42 ]>, which additionally has 1 of <42>");
            }

            #[test]
            fn contains_exactly_values_fails_for_map_with_lower_multiplicity() {
                assert_fails!((HashMap::from([("apple", 42)])).contains_exactly_values(&[42, 42, 42]),
                    expected it "to contain exactly the values <[ 42, 42, 42 ]>"
                    but it "was <[ \"apple\" => 42 ]>, which lacks 2 of <42>");
            }

            #[test]
            fn contains_exactly_values_fails_for_map_with_higher_multiplicity() {
                assert_fails!((BTreeMap::from([("apple", 42), ("banana", 42), ("cherry", 42)]))
                    .contains_exactly_values(&[42]),
                    expected it "to contain exactly the values <[ 42 ]>"
                    but it "was <[ \"apple\" => 42, \"banana\" => 42, \"cherry\" => 42 ]>, \
                        which additionally has 2 of <42>");
            }

            #[test]
            fn contains_exactly_values_fails_for_map_with_multiple_missing_and_superfluous_values() {
                assert_fails!((BTreeMap::from([("apple", 42), ("banana", 43), ("cherry", 44)]))
                    .contains_exactly_values(&[41, 42, 45]),
                    expected it "to contain exactly the values <[ 41, 42, 45 ]>"
                    but it "was <[ \"apple\" => 42, \"banana\" => 43, \"cherry\" => 44 ]>, \
                        which lacks 1 of <41>, 1 of <45> and additionally has 1 of <43>, 1 of <44>");
            }
        }
    }

    test_contains_exactly_values!(contains_exactly_values);

    #[test]
    fn contains_entry_passes_for_singleton_map_with_correct_entry() {
        assert_that!(BTreeMap::from([("apple", 42)])).contains_entry("apple", 42);
    }

    #[test]
    fn contains_entry_passes_for_larger_map_with_correct_entry() {
        assert_that!(HashMap::from([("apple", 41), ("banana", 42), ("cherry", 43)]))
            .contains_entry("banana", 42);
    }

    #[test]
    fn contains_entry_fails_for_empty_map() {
        assert_fails!((HashMap::<&str, i32>::new()).contains_entry("apple", 42),
            expected it "to contain the entry <\"apple\" => 42>"
            but it "was <[ ]>, which does not contain the key");
    }

    #[test]
    fn contains_entry_fails_for_map_with_incorrect_keys() {
        assert_fails!((BTreeMap::from([("banana", 42), ("cherry", 42)]))
            .contains_entry("apple", 42),
            expected it "to contain the entry <\"apple\" => 42>"
            but it "was <[ \"banana\" => 42, \"cherry\" => 42 ]>, which does not contain the key");
    }

    #[test]
    fn contains_entry_fails_for_singleton_map_with_incorrect_value_for_correct_key() {
        assert_fails!((HashMap::from([("apple", 41)])).contains_entry("apple", 42),
            expected it "to contain the entry <\"apple\" => 42>"
            but it "was <[ [\"apple\" => 41] ]>, which maps the key to the value <41>");
    }

    #[test]
    fn contains_entry_fails_for_larger_map_with_incorrect_value_for_correct_key() {
        assert_fails!((BTreeMap::from([("apple", 42), ("banana", 41), ("cherry", 42)]))
            .contains_entry("banana", 42),
            expected it "to contain the entry <\"banana\" => 42>"
            but it "was <[ \"apple\" => 42, [\"banana\" => 41], \"cherry\" => 42 ]>, \
                which maps the key to the value <41>");
    }

    #[test]
    fn does_not_contain_entry_fails_for_singleton_map_with_correct_entry() {
        assert_fails!((HashMap::from([("apple", 42)])).does_not_contain_entry("apple", 42),
            expected it "not to contain the entry <\"apple\" => 42>"
            but it "was <[ [\"apple\" => 42] ]>");
    }

    #[test]
    fn does_not_contain_entry_fails_for_larger_map_with_correct_entry() {
        assert_fails!((BTreeMap::from([("apple", 41), ("banana", 42), ("cherry", 43)]))
            .does_not_contain_entry("banana", 42),
            expected it "not to contain the entry <\"banana\" => 42>"
            but it "was <[ \"apple\" => 41, [\"banana\" => 42], \"cherry\" => 43 ]>");
    }

    #[test]
    fn does_not_contain_entry_passes_for_empty_map() {
        assert_that!(HashMap::<&str, i32>::new()).does_not_contain_entry("apple", 42);
    }

    #[test]
    fn does_not_contain_entry_passes_for_map_with_incorrect_keys() {
        assert_that!(BTreeMap::from([("banana", 42), ("cherry", 42)]))
            .does_not_contain_entry("apple", 42);
    }

    #[test]
    fn does_not_contain_entry_passes_for_singleton_map_with_incorrect_value_for_correct_key() {
        assert_that!(HashMap::from([("apple", 41)])).does_not_contain_entry("apple", 42);
    }

    #[test]
    fn does_not_contain_entry_passes_for_larger_map_with_incorrect_value_for_correct_key() {
        assert_that!(BTreeMap::from([("apple", 42), ("banana", 41), ("cherry", 42)]))
            .does_not_contain_entry("banana", 42);
    }

    #[test]
    fn contains_entries_passes_for_empty_expected_entries() {
        assert_that!(HashMap::<&str, i32>::new()).contains_entries([] as [(&str, i32); 0]);
    }

    #[test]
    fn contains_entries_passes_for_map_with_one_and_only_expected_entry() {
        assert_that!(BTreeMap::from([("apple", 5)])).contains_entries([("apple", 5)]);
    }

    #[test]
    fn contains_entries_passes_for_larger_map_with_exactly_expected_entries() {
        let entries = [("apple", 5), ("banana", 6), ("cherry", 6)];

        assert_that!(HashMap::from(entries.clone())).contains_entries(entries);
    }

    #[test]
    fn contains_entries_passes_for_map_with_expected_entries_and_more() {
        assert_that!(BTreeMap::from([("apple", 5), ("banana", 6), ("cherry", 6)]))
            .contains_entries([("apple", 5), ("cherry", 6)]);
    }

    #[test]
    fn contains_entries_fails_for_empty_map_and_single_expected_entry() {
        assert_fails!((HashMap::<&str, i32>::new()).contains_entries([("apple", 5)]),
            expected it "to contain all of the entries <[ \"apple\" => 5 ]>"
            but it "was <[ ]>, which is missing the key <\"apple\">");
    }

    #[test]
    fn contains_entries_fails_for_map_with_single_incorrect_key() {
        assert_fails!((BTreeMap::from([("banana", 5)])).contains_entries([("apple", 5)]),
            expected it "to contain all of the entries <[ \"apple\" => 5 ]>"
            but it "was <[ \"banana\" => 5 ]>, which is missing the key <\"apple\">");
    }

    #[test]
    fn contains_entries_fails_for_map_with_single_incorrect_value() {
        assert_fails!((HashMap::from([("apple", 6)])).contains_entries([("apple", 5)]),
            expected it "to contain all of the entries <[ \"apple\" => 5 ]>"
            but it "was <[ [\"apple\" => 6] ]>");
    }

    #[test]
    fn contains_entries_fails_for_larger_map_with_incorrect_entry() {
        assert_fails!((BTreeMap::from([("apple", 5), ("banana", 5), ("cherry", 6)]))
            .contains_entries([("apple", 5), ("banana", 6), ("cherry", 6)]),
            expected it "to contain all of the entries \
                <[ \"apple\" => 5, \"banana\" => 6, \"cherry\" => 6 ]>"
            but it "was <[ \"apple\" => 5, [\"banana\" => 5], \"cherry\" => 6 ]>");
    }

    #[test]
    fn does_not_contain_entries_passes_for_empty_unexpected_entries() {
        assert_that!(HashMap::<&str, i32>::new()).does_not_contain_entries([] as [(&str, i32); 0]);
    }

    #[test]
    fn does_not_contain_entries_passes_for_empty_map_and_single_unexpected_entry() {
        assert_that!(HashMap::<&str, i32>::new()).does_not_contain_entries([("apple", 5)]);
    }

    #[test]
    fn does_not_contain_entries_passes_for_map_with_single_different_key() {
        assert_that!(BTreeMap::from([("banana", 5)])).does_not_contain_entries([("apple", 5)]);
    }

    #[test]
    fn does_not_contain_entries_passes_for_map_with_single_different_value() {
        assert_that!(HashMap::from([("apple", 6)])).does_not_contain_entries([("apple", 5)]);
    }

    #[test]
    fn does_not_contain_entries_passes_for_larger_map_without_unexpected_entries() {
        assert_that!(HashMap::from([("apple", 5), ("banana", 6), ("cherry", 6)]))
            .does_not_contain_entries([("banana", 5), ("cherry", 5), ("dragon fruit", 12)]);
    }

    #[test]
    fn does_not_contain_entries_fails_for_map_with_one_and_only_expected_entry() {
        assert_fails!((BTreeMap::from([("apple", 5)])).does_not_contain_entries([("apple", 5)]),
            expected it "not to contain any of the entries <[ \"apple\" => 5 ]>"
            but it "was <[ [\"apple\" => 5] ]>");
    }

    #[test]
    fn does_not_contain_entries_passes_for_larger_map_containing_one_unexpected_entry() {
        assert_fails!((BTreeMap::from([("apple", 5), ("banana", 6), ("cherry", 6)]))
            .does_not_contain_entries([("apple", 6), ("banana", 6)]),
            expected it "not to contain any of the entries <[ \"apple\" => 6, \"banana\" => 6 ]>"
            but it "was <[ \"apple\" => 5, [\"banana\" => 6], \"cherry\" => 6 ]>");
    }

    #[test]
    fn contains_exactly_entries_passes_for_empty_map_with_empty_expected_entries() {
        assert_that!(HashMap::<&str, i32>::new()).contains_exactly_entries([] as [(&str, i32); 0]);
    }

    #[test]
    fn contains_exactly_entries_passes_for_singleton_map_with_correct_entries() {
        assert_that!(BTreeMap::from([("apple", 1)])).contains_exactly_entries([("apple", 1)]);
    }

    #[test]
    fn contains_exactly_entries_passes_for_larger_map_with_correct_entries() {
        assert_that!(BTreeMap::from([("apple", 1), ("banana", 2), ("cherry", 3)]))
            .contains_exactly_entries([("banana", 2), ("cherry", 3), ("apple", 1)]);
    }

    #[test]
    fn contains_exactly_entries_passes_for_duplicated_expected_entry_and_correct_map() {
        assert_that!(HashMap::from([("apple", 1), ("banana", 2)]))
            .contains_exactly_entries([("banana", 2), ("apple", 1), ("banana", 2)]);
    }

    #[test]
    fn contains_exactly_entries_fails_for_empty_map_and_single_expected_entry() {
        assert_fails!((HashMap::<&str, i32>::new()).contains_exactly_entries([("apple", 1)]),
            expected it "to contain exactly the entries <[ \"apple\" => 1 ]>"
            but it "was <[ ]>, which is missing the key <\"apple\">");
    }

    #[test]
    fn contains_exactly_entries_fails_for_map_with_incorrect_key() {
        assert_fails!((BTreeMap::from([("apple", 1), ("bananana", 2), ("cherry", 3)]))
            .contains_exactly_entries([("apple", 1), ("banana", 2), ("cherry", 3)]),
            expected it "to contain exactly the entries \
                <[ \"apple\" => 1, \"banana\" => 2, \"cherry\" => 3 ]>"
            but it "was <[ \"apple\" => 1, \"bananana\" => 2, \"cherry\" => 3 ]>, \
                which is missing the key <\"banana\">");
    }

    #[test]
    fn contains_exactly_entries_fails_for_map_with_incorrect_value() {
        assert_fails!((HashMap::from([("apple", 2)])).contains_exactly_entries([("apple", 1)]),
            expected it "to contain exactly the entries <[ \"apple\" => 1 ]>"
            but it "was <[ [\"apple\" => 2] ]>");
    }

    #[test]
    fn contains_exactly_entries_fails_for_superfluous_entry() {
        assert_fails!((BTreeMap::from([("apple", 1), ("banana", 2)]))
            .contains_exactly_entries([("apple", 1)]),
            expected it "to contain exactly the entries <[ \"apple\" => 1 ]>"
            but it "was <[ \"apple\" => 1, [\"banana\" => 2] ]>, \
                which additionally contains the key <\"banana\">");
    }

    #[test]
    fn contains_exactly_entries_fails_for_expected_entries_with_duplicate_key_and_missing_key() {
        assert_fails!((HashMap::from([("apple", 1)]))
            .contains_exactly_entries([("apple", 1), ("apple", 1), ("banana", 2), ("apple", 1)]),
            expected it "to contain exactly the entries \
                <[ \"apple\" => 1, \"apple\" => 1, \"banana\" => 2, \"apple\" => 1 ]>"
            but it "was <[ \"apple\" => 1 ]>, which is missing the key <\"banana\">");
    }
}
