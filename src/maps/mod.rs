//! Defines the basic [Map] to generalize all types of maps (such as hash maps) and defines wrapper
//! structs to create [Collection] views of a map. In addition, general map-based assertions are
//! provided by [MapAssertions]. Sub-modules of this module provide more specialized assertions.

use std::borrow::Borrow;
use std::collections::btree_map::{
    Iter as BTreeMapEntryIter,
    Keys as BTreeMapKeyIter,
    Values as BTreeMapValueIter,
};
use std::collections::hash_map::{
    Iter as HashMapEntryIter,
    Keys as HashMapKeyIter,
    Values as HashMapValueIter,
};
use std::collections::{BTreeMap, HashMap};
use std::fmt::Debug;
use std::hash::Hash;
use std::marker::PhantomData;
use std::slice::Iter as SliceIter;

use crate::collections::{Collection, CollectionDebug};
use crate::maps::debug::{HighlightedMapDebug, MapDebug};
use crate::util::borrow_all;
use crate::{AssertThat, Failure};

pub mod partial_eq;

mod debug;

/// A trait for maps which assign [Map::Value]s of one type to [Map::Key]s of (potentially) another
/// type, with a unique mapping for each key. This contrasts with collections, which only have one
/// type of item.
///
/// The content of a map is defined by various iterators ([Map::keys], [Map::values], and
/// [Map::entries]) and a key-wise mapping given by [Map::get].
///
/// This trait is required to allow map-based assertions. It is implemented on all common map types
/// in the standard library and references thereof.
pub trait Map<'map> {
    /// The type of keys used for lookup in this map type to obtain values.
    type Key;

    /// The type of values associated with keys in this map type.
    type Value;

    /// The type of iterators which can iterate over references of the keys of a map. Iteration
    /// order is not specified.
    type KeyIter<'iter>: Iterator<Item = &'iter Self::Key>
    where
        Self: 'iter,
        'map: 'iter;

    /// The type of iterators which can iterate over references of the values of a map. Iteration
    /// order is not specified.
    type ValueIter<'iter>: Iterator<Item = &'iter Self::Value>
    where
        Self: 'iter,
        'map: 'iter;

    /// The type of iterators which can iterate over entries of a map, i.e. pairs of key- and
    /// value-references. Iteration order is not specified.
    type EntryIter<'iter>: Iterator<Item = (&'iter Self::Key, &'iter Self::Value)>
    where
        Self: 'iter,
        'map: 'iter;

    /// Returns an iterator over references of the keys of this map. Iteration order is not
    /// specified.
    fn keys<'reference>(&'reference self) -> Self::KeyIter<'reference>
    where
        'map: 'reference;

    /// Returns an iterator over references of the values of this map. Iteration order is not
    /// specified.
    fn values<'reference>(&'reference self) -> Self::ValueIter<'reference>
    where
        'map: 'reference;

    /// Returns an iterator over references of the entries of this map, i.e. pairs of key- and
    /// value-references. Iteration order is not specified.
    fn entries<'reference>(&'reference self) -> Self::EntryIter<'reference>
    where
        'map: 'reference;

    /// Gets a reference to the value associated with the given `key` in a `Some` variant, if a
    /// mapping exists. Otherwise, if this map has no value associated with the key, `None` is
    /// returned.
    fn get<Q: Borrow<Self::Key>>(&self, key: &Q) -> Option<&Self::Value>;

    /// Returns the number of mappings/key-value-pairs contained in this map. By default, this is
    /// implemented by counting the [Map::keys]. A more efficient implementation may be provided.
    fn len(&self) -> usize {
        self.keys().count()
    }

    /// Indicates whether this map is empty, i.e. it has a length ([Map::len]) of zero. By default,
    /// this is implemented by checking whether [Map::len] returns 0. A more efficient
    /// implementation may be provided.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Indicates whether two keys would identify the same entry in this type of map. In most cases
    /// (e.g. in all standard library maps), this would be an equality as defined by [Eq].
    fn are_keys_equal(key_1: &Self::Key, key_2: &Self::Key) -> bool;
}

impl<'map, K, V> Map<'map> for HashMap<K, V>
where
    K: Eq + Hash + 'map,
    V: 'map,
{
    type Key = K;
    type Value = V;

    type KeyIter<'iter>
        = HashMapKeyIter<'iter, K, V>
    where
        Self: 'iter,
        'map: 'iter;

    type ValueIter<'iter>
        = HashMapValueIter<'iter, K, V>
    where
        Self: 'iter,
        'map: 'iter;

    type EntryIter<'iter>
        = HashMapEntryIter<'iter, K, V>
    where
        Self: 'iter,
        'map: 'iter;

    fn keys<'reference>(&'reference self) -> Self::KeyIter<'reference>
    where
        'map: 'reference,
    {
        HashMap::keys(self)
    }

    fn values<'reference>(&'reference self) -> Self::ValueIter<'reference>
    where
        'map: 'reference,
    {
        HashMap::values(self)
    }

    fn entries<'reference>(&'reference self) -> Self::EntryIter<'reference>
    where
        'map: 'reference,
    {
        HashMap::iter(self)
    }

    fn get<Q: Borrow<Self::Key>>(&self, key: &Q) -> Option<&Self::Value> {
        HashMap::get(self, key.borrow())
    }

    fn len(&self) -> usize {
        HashMap::len(self)
    }

    fn are_keys_equal(key_1: &Self::Key, key_2: &Self::Key) -> bool {
        key_1 == key_2
    }
}

impl<'map, K, V> Map<'map> for BTreeMap<K, V>
where
    K: Ord + 'map,
    V: 'map,
{
    type Key = K;
    type Value = V;

    type KeyIter<'iter>
        = BTreeMapKeyIter<'iter, K, V>
    where
        Self: 'iter,
        'map: 'iter;

    type ValueIter<'iter>
        = BTreeMapValueIter<'iter, K, V>
    where
        Self: 'iter,
        'map: 'iter;

    type EntryIter<'iter>
        = BTreeMapEntryIter<'iter, K, V>
    where
        Self: 'iter,
        'map: 'iter;

    fn keys<'reference>(&'reference self) -> Self::KeyIter<'reference>
    where
        'map: 'reference,
    {
        BTreeMap::keys(self)
    }

    fn values<'reference>(&'reference self) -> Self::ValueIter<'reference>
    where
        'map: 'reference,
    {
        BTreeMap::values(self)
    }

    fn entries<'reference>(&'reference self) -> Self::EntryIter<'reference>
    where
        'map: 'reference,
    {
        BTreeMap::iter(self)
    }

    fn get<Q: Borrow<Self::Key>>(&self, key: &Q) -> Option<&Self::Value> {
        BTreeMap::get(self, key.borrow())
    }

    fn len(&self) -> usize {
        BTreeMap::len(self)
    }

    fn are_keys_equal(key_1: &Self::Key, key_2: &Self::Key) -> bool {
        key_1 == key_2
    }
}

macro_rules! impl_map_for_ref {
    ($ref_type:ty) => {
        impl<'map, M: Map<'map>> Map<'map> for $ref_type {
            type Key = M::Key;
            type Value = M::Value;

            type KeyIter<'iter>
                = M::KeyIter<'iter>
            where
                Self: 'iter,
                'map: 'iter;

            type ValueIter<'iter>
                = M::ValueIter<'iter>
            where
                Self: 'iter,
                'map: 'iter;

            type EntryIter<'iter>
                = M::EntryIter<'iter>
            where
                Self: 'iter,
                'map: 'iter;

            fn keys<'reference>(&'reference self) -> M::KeyIter<'reference>
            where
                'map: 'reference,
            {
                (**self).keys()
            }

            fn values<'reference>(&'reference self) -> M::ValueIter<'reference>
            where
                'map: 'reference,
            {
                (**self).values()
            }

            fn entries<'reference>(&'reference self) -> M::EntryIter<'reference>
            where
                'map: 'reference,
            {
                (**self).entries()
            }

            fn get<Q: Borrow<M::Key>>(&self, key: &Q) -> Option<&M::Value> {
                (**self).get(key)
            }

            fn len(&self) -> usize {
                (**self).len()
            }

            fn is_empty(&self) -> bool {
                (**self).is_empty()
            }

            fn are_keys_equal(key_1: &M::Key, key_2: &M::Key) -> bool {
                M::are_keys_equal(key_1, key_2)
            }
        }
    };
}

impl_map_for_ref!(&M);
impl_map_for_ref!(&mut M);
impl_map_for_ref!(Box<M>);

/// A [Collection] which contains the keys of a [Map]. That is, the [Collection::iterator] returns
/// the same items as [Map::keys].
pub struct MapKeys<'map, M: Map<'map>> {
    _lifetime: PhantomData<&'map ()>,
    map: M,
}

impl<'map, M: Map<'map>> Collection<'map> for MapKeys<'map, M> {
    type Item = M::Key;

    type Iter<'iter>
        = M::KeyIter<'iter>
    where
        Self: 'iter,
        'map: 'iter;

    fn iterator<'reference>(&'reference self) -> Self::Iter<'reference>
    where
        'map: 'reference,
    {
        self.map.keys()
    }
}

/// A [Collection] which contains the values of a [Map]. That is, the [Collection::iterator] returns
/// the same items as [Map::values].
pub struct MapValues<'map, M: Map<'map>> {
    _lifetime: PhantomData<&'map ()>,
    map: M,
}

impl<'map, M: Map<'map>> Collection<'map> for MapValues<'map, M> {
    type Item = M::Value;

    type Iter<'iter>
        = M::ValueIter<'iter>
    where
        Self: 'iter,
        'map: 'iter;

    fn iterator<'reference>(&'reference self) -> Self::Iter<'reference>
    where
        'map: 'reference,
    {
        self.map.values()
    }
}

/// A [Collection] which contains the entries of a [Map]. The [Collection::iterator] returns
/// _references_ to the [Map::entries], whose items are instantiated with the `'wrapper` lifetime.
pub struct MapEntries<'wrapper, 'map, M: Map<'map>> {
    entries: Vec<(&'wrapper M::Key, &'wrapper M::Value)>,
}

impl<'wrapper, 'map, M: Map<'map>> Collection<'wrapper> for MapEntries<'wrapper, 'map, M> {
    type Item = (&'wrapper M::Key, &'wrapper M::Value);

    type Iter<'iter>
        = SliceIter<'iter, Self::Item>
    where
        Self: 'iter,
        'wrapper: 'iter;

    fn iterator<'reference>(&'reference self) -> Self::Iter<'reference>
    where
        'wrapper: 'reference,
    {
        self.entries.iter()
    }
}

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with an
/// argument that implements the [Map] trait. The [Map::Key] and [Map::Value] types must implement
/// [Debug].
///
/// Examples:
///
/// ```
/// use kernal::prelude::*;
/// use std::collections::{BTreeMap, HashMap};
///
/// assert_that!(HashMap::<String, u32>::new()).is_empty().has_length(0);
///
/// let fruit_map = BTreeMap::from([("apple", 1), ("banana", 2)]);
///
/// assert_that!(&fruit_map).contains_keys(["apple", "banana"]).does_not_contain_key("cherry");
/// assert_that!(fruit_map).to_keys().contains_exactly_in_any_order(["banana", "apple"]);
/// ```
pub trait MapAssertions<'map, M: Map<'map>> {
    /// Asserts that the tested map is empty, i.e. contains no entries.
    fn is_empty(self) -> Self;

    /// Asserts that the tested map is not empty, i.e. contains at least one entry.
    fn is_not_empty(self) -> Self;

    /// Asserts that the number of entries contained in the tested map is equal to the given
    /// `expected_length`.
    fn has_length(self, expected_length: usize) -> Self;

    /// Asserts that the number of entries contained in the tested map is less than the given
    /// `length_bound`.
    fn has_length_less_than(self, length_bound: usize) -> Self;

    /// Asserts that the number of entries contained in the tested map is less than or equal to the
    /// given `length_bound`.
    fn has_length_less_than_or_equal_to(self, length_bound: usize) -> Self;

    /// Asserts that the number of entries contained in the tested map is greater than the given
    /// `length_bound`.
    fn has_length_greater_than(self, length_bound: usize) -> Self;

    /// Asserts that the number of entries contained in the tested map is greater than or equal to
    /// the given `length_bound`.
    fn has_length_greater_than_or_equal_to(self, length_bound: usize) -> Self;

    /// Asserts that the number of entries contained in the tested map is different from the given
    /// `unexpected_length`.
    fn does_not_have_length(self, unexpected_length: usize) -> Self;

    /// Asserts that the tested map has an entry associated with the given `key`, i.e. [Map::get]
    /// returns a `Some` variant.
    fn contains_key<K: Borrow<M::Key>>(self, key: K) -> Self;

    /// Asserts that the tested map does not have an entry associated with the given `key`, i.e.
    /// [Map::get] returns `None`.
    fn does_not_contain_key<K: Borrow<M::Key>>(self, key: K) -> Self;

    /// Asserts that for each of the given `keys`, the tested map has an entry associated with it,
    /// i.e. [Map::get] returns a `Some` variant.
    fn contains_keys<K: Borrow<M::Key>, I: IntoIterator<Item = K>>(self, keys: I) -> Self;

    /// Asserts that for each of the given `keys`, the tested map has no entry associated with it,
    /// i.e. [Map::get] returns `None`.
    fn does_not_contain_keys<K: Borrow<M::Key>, I: IntoIterator<Item = K>>(self, keys: I) -> Self;

    /// Asserts that there is a one-to-one mapping of keys in the tested map and in the given
    /// iterator of `keys`, which are considered equal by the tested map type's standards (see
    /// [Map::are_keys_equal]). The order of the given `keys` iterator is irrelevant and duplicate
    /// keys are ignored.
    fn contains_exactly_keys<K: Borrow<M::Key>, I: IntoIterator<Item = K>>(self, keys: I) -> Self;

    /// Converts the tested map into a [Collection] that contains its keys and allows assertions on
    /// it.
    fn to_keys(self) -> AssertThat<MapKeys<'map, M>>;

    /// Converts the tested map into a [Collection] that contains its values and allows assertions
    /// on it.
    fn to_values(self) -> AssertThat<MapValues<'map, M>>;

    /// Converts the tested map into a [Collection] that contains _references_ to its entries and
    /// allows assertions on it.
    ///
    /// Due to restrictions in the current type setup, this method requires a lifetime to be
    /// associated with the returned entries. It is still intended and recommended  to be used in a
    /// call chain as all other assertions.
    fn to_entries<'this>(&'this self) -> AssertThat<MapEntries<'this, 'map, M>>
    where
        'map: 'this;
}

fn assert_length_predicate<'map, M, F>(
    assert_that: AssertThat<M>,
    length_predicate: F,
    reference_len: usize,
    expected_it_prefix: &str,
) -> AssertThat<M>
where
    M: Map<'map>,
    M::Key: Debug,
    M::Value: Debug,
    F: Fn(usize) -> bool,
{
    let len = assert_that.data.len();

    if !length_predicate(len) {
        let map_debug = MapDebug {
            map: &assert_that.data,
        };

        Failure::new(&assert_that)
            .expected_it(format!("{} <{}>", expected_it_prefix, reference_len))
            .but_it(format!("was <{:?}> with length <{}>", map_debug, len))
            .fail();
    }

    assert_that
}

impl<'map, M> MapAssertions<'map, M> for AssertThat<M>
where
    M: Map<'map> + 'map,
    M::Key: Debug,
    M::Value: Debug,
{
    fn is_empty(self) -> Self {
        if !self.data.is_empty() {
            Failure::new(&self)
                .expected_it("to be empty")
                .but_it(format!("was <{:?}>", MapDebug { map: &self.data }))
                .fail();
        }

        self
    }

    fn is_not_empty(self) -> Self {
        if self.data.is_empty() {
            Failure::new(&self)
                .expected_it("not to be empty")
                .but_it("was")
                .fail();
        }

        self
    }

    fn has_length(self, expected_length: usize) -> Self {
        assert_length_predicate(
            self,
            |len| len == expected_length,
            expected_length,
            "to have length",
        )
    }

    fn has_length_less_than(self, length_bound: usize) -> Self {
        assert_length_predicate(
            self,
            |len| len < length_bound,
            length_bound,
            "to have length less than",
        )
    }

    fn has_length_less_than_or_equal_to(self, length_bound: usize) -> Self {
        assert_length_predicate(
            self,
            |len| len <= length_bound,
            length_bound,
            "to have length less than or equal to",
        )
    }

    fn has_length_greater_than(self, length_bound: usize) -> Self {
        assert_length_predicate(
            self,
            |len| len > length_bound,
            length_bound,
            "to have length greater than",
        )
    }

    fn has_length_greater_than_or_equal_to(self, length_bound: usize) -> Self {
        assert_length_predicate(
            self,
            |len| len >= length_bound,
            length_bound,
            "to have length greater than or equal to",
        )
    }

    fn does_not_have_length(self, unexpected_length: usize) -> Self {
        assert_length_predicate(
            self,
            |len| len != unexpected_length,
            unexpected_length,
            "not to have length",
        )
    }

    fn contains_key<K: Borrow<M::Key>>(self, key: K) -> Self {
        if self.data.get(&key).is_none() {
            Failure::new(&self)
                .expected_it(format!(
                    "to contain an entry for the key <{:?}>",
                    key.borrow()
                ))
                .but_it(format!("was <{:?}>", MapDebug { map: &self.data }))
                .fail();
        }

        self
    }

    fn does_not_contain_key<K: Borrow<M::Key>>(self, key: K) -> Self {
        if self.data.get(&key).is_some() {
            let highlighted_map_debug = HighlightedMapDebug {
                map: &self.data,
                highlighted_key: key.borrow(),
            };

            Failure::new(&self)
                .expected_it(format!(
                    "not to contain an entry for the key <{:?}>",
                    key.borrow()
                ))
                .but_it(format!("was <{:?}>", highlighted_map_debug))
                .fail();
        }

        self
    }

    fn contains_keys<K: Borrow<M::Key>, I: IntoIterator<Item = K>>(self, keys: I) -> Self {
        let keys_unborrowed = keys.into_iter().collect::<Vec<_>>();
        let keys: Vec<&M::Key> = borrow_all(&keys_unborrowed);

        if let Some(&missing_key) = keys.iter().find(|&key| self.data.get(key).is_none()) {
            let keys_debug = CollectionDebug { collection: &keys };
            let map_debug = MapDebug { map: &self.data };

            Failure::new(&self)
                .expected_it(format!(
                    "to contain entries for the keys <{:?}>",
                    keys_debug
                ))
                .but_it(format!(
                    "was <{:?}>, which is missing the key <{:?}>",
                    map_debug, missing_key
                ))
                .fail();
        }

        self
    }

    fn does_not_contain_keys<K: Borrow<M::Key>, I: IntoIterator<Item = K>>(self, keys: I) -> Self {
        let keys_unborrowed = keys.into_iter().collect::<Vec<_>>();
        let keys: Vec<&M::Key> = borrow_all(&keys_unborrowed);

        if let Some(&present_key) = keys.iter().find(|&key| self.data.get(key).is_some()) {
            let keys_debug = CollectionDebug { collection: &keys };
            let map_debug = HighlightedMapDebug {
                map: &self.data,
                highlighted_key: present_key,
            };

            Failure::new(&self)
                .expected_it(format!(
                    "not to contain entries for the keys <{:?}>",
                    keys_debug
                ))
                .but_it(format!("was <{:?}>", map_debug))
                .fail();
        }

        self
    }

    fn contains_exactly_keys<K: Borrow<M::Key>, I: IntoIterator<Item = K>>(self, keys: I) -> Self {
        let expected_keys_unborrowed = keys.into_iter().collect::<Vec<_>>();
        let expected_keys: Vec<&M::Key> = borrow_all(&expected_keys_unborrowed);
        let missing_keys = expected_keys
            .iter()
            .cloned()
            .filter(|&expected_key| self.data.get(expected_key).is_none())
            .collect::<Vec<_>>();
        let superfluous_keys: Vec<&M::Key> = self
            .data
            .keys()
            .filter(|actual_key| {
                !expected_keys
                    .iter()
                    .any(|expected_key| M::are_keys_equal(actual_key, expected_key))
            })
            .collect::<Vec<_>>();
        let mut errors = Vec::new();

        if !missing_keys.is_empty() {
            let missing_keys_debug = CollectionDebug {
                collection: &missing_keys,
            };
            errors.push(format!("lacks <{:?}>", missing_keys_debug));
        }

        if !superfluous_keys.is_empty() {
            let superfluous_keys_debug = CollectionDebug {
                collection: &superfluous_keys,
            };
            errors.push(format!("additionally has <{:?}>", superfluous_keys_debug));
        }

        if !errors.is_empty() {
            let expected_keys_debug = CollectionDebug {
                collection: &expected_keys,
            };
            let map_debug = MapDebug { map: &self.data };
            let error_message = errors.join(" and ");

            Failure::new(&self)
                .expected_it(format!(
                    "to contain exactly the keys <{:?}>",
                    expected_keys_debug
                ))
                .but_it(format!("was <{:?}>, which {}", map_debug, error_message))
                .fail()
        }

        self
    }

    fn to_keys(self) -> AssertThat<MapKeys<'map, M>> {
        AssertThat {
            data: MapKeys {
                _lifetime: PhantomData,
                map: self.data,
            },
            expression: format!("keys of <{}>", self.expression),
        }
    }

    fn to_values(self) -> AssertThat<MapValues<'map, M>> {
        AssertThat {
            data: MapValues {
                _lifetime: PhantomData,
                map: self.data,
            },
            expression: format!("values of <{}>", self.expression),
        }
    }

    // TODO find a solution that does not require a reference here

    fn to_entries<'this>(&'this self) -> AssertThat<MapEntries<'this, 'map, M>>
    where
        'map: 'this,
    {
        AssertThat {
            data: MapEntries {
                entries: self.data.entries().collect::<Vec<_>>(),
            },
            expression: format!("entries of <{}>", self.expression),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::iter::Empty;
    use std::slice::Iter as SliceIter;

    use super::*;
    use crate::prelude::*;
    use crate::{assert_fails, assert_that};

    struct MockMap {
        keys: Vec<i32>,
    }

    impl<'map> Map<'map> for MockMap {
        type Key = i32;
        type Value = i32;
        type KeyIter<'iter>
            = SliceIter<'iter, i32>
        where
            Self: 'iter,
            'map: 'iter;
        type ValueIter<'iter>
            = Empty<&'iter i32>
        where
            Self: 'iter,
            'map: 'iter;
        type EntryIter<'iter>
            = Empty<(&'iter i32, &'iter i32)>
        where
            Self: 'iter,
            'map: 'iter;

        fn keys<'reference>(&'reference self) -> Self::KeyIter<'reference>
        where
            'map: 'reference,
        {
            self.keys.iter()
        }

        fn values<'reference>(&'reference self) -> Self::ValueIter<'reference>
        where
            'map: 'reference,
        {
            panic!("mock map values not expected to be called")
        }

        fn entries<'reference>(&'reference self) -> Self::EntryIter<'reference>
        where
            'map: 'reference,
        {
            panic!("mock map entries not expected to be called")
        }

        fn get<Q: Borrow<i32>>(&self, _: &Q) -> Option<&i32> {
            panic!("mock map get not expected to be called")
        }

        fn are_keys_equal(_: &i32, _: &i32) -> bool {
            panic!("mock map are_keys_equal not expected to be called")
        }
    }

    #[test]
    fn default_len_works_for_empty_map() {
        assert_that!(MockMap { keys: vec![] }).has_length(0);
    }

    #[test]
    fn default_is_empty_for_empty_map() {
        assert_that!(MockMap { keys: vec![] }).is_empty();
    }

    #[test]
    fn default_len_works_for_larger_map() {
        assert_that!(MockMap {
            keys: vec![2, 4, 6]
        })
        .has_length(3);
    }

    #[test]
    fn default_is_empty_for_larger_map() {
        assert_that!(MockMap {
            keys: vec![2, 4, 6]
        })
        .is_not_empty();
    }

    #[test]
    fn is_empty_passes_for_empty_map() {
        assert_that!(HashMap::<String, u32>::new()).is_empty();
    }

    #[test]
    fn is_empty_fails_for_singleton_map() {
        assert_fails!((HashMap::from([("hello", 5)])).is_empty(),
            expected it "to be empty"
            but it "was <[ \"hello\" => 5 ]>");
    }

    #[test]
    fn is_empty_fails_for_larger_map() {
        assert_fails!((BTreeMap::from([("apple", 3), ("banana", 4)])).is_empty(),
            expected it "to be empty"
            but it "was <[ \"apple\" => 3, \"banana\" => 4 ]>");
    }

    #[test]
    fn is_not_empty_passes_for_singleton_map() {
        assert_that!(&mut BTreeMap::from([("hello", 5)])).is_not_empty();
    }

    #[test]
    fn is_not_empty_passes_for_larger_map() {
        assert_that!(HashMap::from([("apple", 3), ("banana", 4)])).is_not_empty();
    }

    #[test]
    fn is_not_empty_fails_for_empty_map() {
        assert_fails!((BTreeMap::<String, u32>::new()).is_not_empty(),
            expected it "not to be empty"
            but it "was");
    }

    #[test]
    fn has_length_passes_for_equal_length() {
        assert_that!(BTreeMap::from([("apple", 1), ("banana", 2)])).has_length(2);
    }

    #[test]
    fn has_length_fails_for_lower_length() {
        assert_fails!((BTreeMap::from([("apple", 1), ("banana", 2)])).has_length(3),
            expected it "to have length <3>"
            but it "was <[ \"apple\" => 1, \"banana\" => 2 ]> with length <2>");
    }

    #[test]
    fn has_length_fails_for_higher_length() {
        assert_fails!((BTreeMap::from([("apple", 1), ("banana", 2)])).has_length(1),
            expected it "to have length <1>"
            but it "was <[ \"apple\" => 1, \"banana\" => 2 ]> with length <2>");
    }

    #[test]
    fn has_length_less_than_passes_for_lower_length() {
        assert_that!(&BTreeMap::from([("apple", 1), ("banana", 2)])).has_length_less_than(3);
    }

    #[test]
    fn has_length_less_than_fails_for_equal_length() {
        assert_fails!((BTreeMap::from([("apple", 1), ("banana", 2)])).has_length_less_than(2),
            expected it "to have length less than <2>"
            but it "was <[ \"apple\" => 1, \"banana\" => 2 ]> with length <2>");
    }

    #[test]
    fn has_length_less_than_fails_for_higher_length() {
        assert_fails!((BTreeMap::from([("apple", 1), ("banana", 2)])).has_length_less_than(1),
            expected it "to have length less than <1>"
            but it "was <[ \"apple\" => 1, \"banana\" => 2 ]> with length <2>");
    }

    #[test]
    fn has_length_less_than_or_equal_to_passes_for_lower_length() {
        assert_that!(BTreeMap::from([("apple", 1), ("banana", 2)]))
            .has_length_less_than_or_equal_to(3);
    }

    #[test]
    fn has_length_less_than_or_equal_to_passes_for_equal_length() {
        assert_that!(BTreeMap::from([("apple", 1), ("banana", 2)]))
            .has_length_less_than_or_equal_to(2);
    }

    #[test]
    fn has_length_less_than_or_equal_to_fails_for_higher_length() {
        assert_fails!(
            (BTreeMap::from([("apple", 1), ("banana", 2)])).has_length_less_than_or_equal_to(1),
            expected it "to have length less than or equal to <1>"
            but it "was <[ \"apple\" => 1, \"banana\" => 2 ]> with length <2>");
    }

    #[test]
    fn has_length_greater_than_passes_for_higher_length() {
        assert_that!(BTreeMap::from([("apple", 1), ("banana", 2)])).has_length_greater_than(1);
    }

    #[test]
    fn has_length_greater_than_fails_for_equal_length() {
        assert_fails!((BTreeMap::from([("apple", 1), ("banana", 2)])).has_length_greater_than(2),
            expected it "to have length greater than <2>"
            but it "was <[ \"apple\" => 1, \"banana\" => 2 ]> with length <2>");
    }

    #[test]
    fn has_length_greater_than_fails_for_lower_length() {
        assert_fails!((BTreeMap::from([("apple", 1), ("banana", 2)])).has_length_greater_than(3),
            expected it "to have length greater than <3>"
            but it "was <[ \"apple\" => 1, \"banana\" => 2 ]> with length <2>");
    }

    #[test]
    fn has_length_greater_than_or_equal_to_passes_for_higher_length() {
        assert_that!(BTreeMap::from([("apple", 1), ("banana", 2)]))
            .has_length_greater_than_or_equal_to(1);
    }

    #[test]
    fn has_length_greater_than_or_equal_to_passes_for_equal_length() {
        assert_that!(BTreeMap::from([("apple", 1), ("banana", 2)]))
            .has_length_greater_than_or_equal_to(2);
    }

    #[test]
    fn has_length_greater_than_or_equal_to_fails_for_lower_length() {
        assert_fails!(
            (BTreeMap::from([("apple", 1), ("banana", 2)])).has_length_greater_than_or_equal_to(3),
            expected it "to have length greater than or equal to <3>"
            but it "was <[ \"apple\" => 1, \"banana\" => 2 ]> with length <2>");
    }

    #[test]
    fn does_not_have_length_passes_for_lower_length() {
        assert_that!(BTreeMap::from([("apple", 1), ("banana", 2)])).does_not_have_length(3);
    }

    #[test]
    fn does_not_have_length_passes_for_higher_length() {
        assert_that!(BTreeMap::from([("apple", 1), ("banana", 2)])).does_not_have_length(1);
    }

    #[test]
    fn does_not_have_length_fails_for_equal_length() {
        assert_fails!((BTreeMap::from([("apple", 1), ("banana", 2)])).does_not_have_length(2),
            expected it "not to have length <2>"
            but it "was <[ \"apple\" => 1, \"banana\" => 2 ]> with length <2>");
    }

    #[test]
    fn contains_key_passes_for_only_key_in_singleton() {
        assert_that!(HashMap::from([("apple", 1)])).contains_key("apple");
    }

    #[test]
    fn contains_key_passes_for_valid_key_in_larger_map() {
        assert_that!(&BTreeMap::from([
            ("apple", 1),
            ("banana", 2),
            ("cherry", 3)
        ]))
        .contains_key("banana");
    }

    #[test]
    fn contains_key_fails_for_empty_map() {
        assert_fails!((HashMap::<&str, i32>::new()).contains_key("apple"),
            expected it "to contain an entry for the key <\"apple\">"
            but it "was <[ ]>");
    }

    #[test]
    fn contains_key_fails_for_invalid_key_in_larger_map() {
        assert_fails!(
            (BTreeMap::from([("apple", 1), ("banana", 2), ("cherry", 3)])).contains_key("pear"),
            expected it "to contain an entry for the key <\"pear\">"
            but it "was <[ \"apple\" => 1, \"banana\" => 2, \"cherry\" => 3 ]>");
    }

    #[test]
    fn does_not_contain_key_fails_for_only_key_in_singleton() {
        assert_fails!((HashMap::from([("apple", 1)])).does_not_contain_key("apple"),
            expected it "not to contain an entry for the key <\"apple\">"
            but it "was <[ [\"apple\" => 1] ]>");
    }

    #[test]
    fn does_not_contain_key_fails_for_valid_key_in_larger_map() {
        assert_fails!(
            (BTreeMap::from([("apple", 1), ("banana", 2), ("cherry", 3)]))
                .does_not_contain_key("banana"),
            expected it "not to contain an entry for the key <\"banana\">"
            but it "was <[ \"apple\" => 1, [\"banana\" => 2], \"cherry\" => 3 ]>");
    }

    #[test]
    fn does_not_contain_key_passes_for_empty_map() {
        assert_that!(HashMap::<&str, i32>::new()).does_not_contain_key("apple");
    }

    #[test]
    fn does_not_contain_key_passes_for_invalid_key_in_larger_map() {
        assert_that!(BTreeMap::from([("apple", 1), ("banana", 2), ("cherry", 3)]))
            .does_not_contain_key("pear");
    }

    #[test]
    fn contains_keys_passes_for_empty_keys() {
        assert_that!(HashMap::<&str, i32>::new()).contains_keys([] as [&str; 0]);
    }

    #[test]
    fn contains_keys_passes_for_same_single_key() {
        assert_that!(HashMap::from([("apple", 1)])).contains_keys(["apple"]);
    }

    #[test]
    fn contains_keys_passes_for_same_larger_key_set() {
        assert_that!(BTreeMap::from([("apple", 1), ("banana", 2), ("cherry", 3)]))
            .contains_keys(["cherry", "banana", "apple"]);
    }

    #[test]
    fn contains_keys_passes_for_map_with_proper_superset_of_keys() {
        assert_that!(BTreeMap::from([("apple", 1), ("banana", 2), ("cherry", 3)]))
            .contains_keys(["cherry", "apple"]);
    }

    #[test]
    fn contains_keys_fails_for_empty_map_with_single_key() {
        assert_fails!((HashMap::<&str, i32>::new()).contains_keys(["apple"]),
            expected it "to contain entries for the keys <[ \"apple\" ]>"
            but it "was <[ ]>, which is missing the key <\"apple\">");
    }

    #[test]
    fn contains_keys_fails_for_single_key_not_contained_in_map() {
        assert_fails!((BTreeMap::from([("apple", 1), ("banana", 2)])).contains_keys(["cherry"]),
            expected it "to contain entries for the keys <[ \"cherry\" ]>"
            but it
                "was <[ \"apple\" => 1, \"banana\" => 2 ]>, which is missing the key <\"cherry\">");
    }

    #[test]
    fn contains_keys_fails_for_key_set_with_only_some_keys_in_map() {
        assert_fails!((BTreeMap::from([("apple", 1), ("cherry", 2)]))
            .contains_keys(["apple", "banana", "cherry"]),
            expected it "to contain entries for the keys <[ \"apple\", \"banana\", \"cherry\" ]>"
            but it
                "was <[ \"apple\" => 1, \"cherry\" => 2 ]>, which is missing the key <\"banana\">");
    }

    #[test]
    fn does_not_contain_keys_passes_for_empty_keys() {
        assert_that!(HashMap::<&str, i32>::new()).does_not_contain_keys([] as [&str; 0]);
    }

    #[test]
    fn does_not_contain_keys_passes_for_empty_map_with_single_key() {
        assert_that!(HashMap::<&str, i32>::new()).does_not_contain_keys(["apple"]);
    }

    #[test]
    fn does_not_contain_keys_passes_for_single_key_not_contained_in_map() {
        assert_that!(BTreeMap::from([("apple", 1), ("banana", 2)]))
            .does_not_contain_keys(["cherry"]);
    }

    #[test]
    fn does_not_contain_keys_passes_for_disjunct_larger_key_set() {
        assert_that!(BTreeMap::from([("apple", 1), ("banana", 2), ("cherry", 3)]))
            .does_not_contain_keys(["dragon fruit", "eggplant", "fig"]);
    }

    #[test]
    fn does_not_contain_keys_fails_for_same_single_key() {
        assert_fails!((HashMap::from([("apple", 1)])).does_not_contain_keys(["apple"]),
            expected it "not to contain entries for the keys <[ \"apple\" ]>"
            but it "was <[ [\"apple\" => 1] ]>");
    }

    #[test]
    fn does_not_contain_keys_fails_for_map_with_proper_superset_of_keys() {
        assert_fails!((BTreeMap::from([("apple", 1), ("banana", 2), ("cherry", 3)]))
            .does_not_contain_keys(["cherry", "apple"]),
            expected it "not to contain entries for the keys <[ \"cherry\", \"apple\" ]>"
            but it "was <[ \"apple\" => 1, \"banana\" => 2, [\"cherry\" => 3] ]>");
    }

    #[test]
    fn does_not_contain_keys_fails_for_key_set_with_only_some_keys_not_in_map() {
        assert_fails!((BTreeMap::from([("apple", 1), ("cherry", 2)]))
            .does_not_contain_keys(["banana", "cherry", "dragon fruit"]),
            expected it
                "not to contain entries for the keys <[ \"banana\", \"cherry\", \"dragon fruit\" ]>"
            but it "was <[ \"apple\" => 1, [\"cherry\" => 2] ]>");
    }

    #[test]
    fn contains_exactly_keys_passes_for_empty_map_and_no_keys() {
        assert_that!(HashMap::<&str, i32>::new()).contains_exactly_keys(&[] as &[&str]);
    }

    #[test]
    fn contains_exactly_keys_passes_for_singleton_map_with_correct_keys() {
        assert_that!(BTreeMap::from([("apple", 1)])).contains_exactly_keys(&["apple"]);
    }

    #[test]
    fn contains_exactly_keys_passes_for_larger_map_with_correct_keys() {
        assert_that!(&HashMap::from([("apple", 1), ("banana", 2), ("cherry", 3)]))
            .contains_exactly_keys(&["cherry", "apple", "banana"]);
    }

    #[test]
    fn contains_exactly_keys_fails_for_empty_map_and_some_key() {
        let map = BTreeMap::<&str, i32>::new();

        assert_fails!((&map).contains_exactly_keys(&["apple"]),
            expected it "to contain exactly the keys <[ \"apple\" ]>"
            but it "was <[ ]>, which lacks <[ \"apple\" ]>");
    }

    #[test]
    fn contains_exactly_keys_fails_for_map_missing_keys() {
        assert_fails!((HashMap::from([("banana", 2)]))
            .contains_exactly_keys(&["apple", "banana", "cherry"]),
            expected it "to contain exactly the keys <[ \"apple\", \"banana\", \"cherry\" ]>"
            but it "was <[ \"banana\" => 2 ]>, which lacks <[ \"apple\", \"cherry\" ]>");
    }

    #[test]
    fn contains_exactly_keys_fails_for_map_with_additional_keys() {
        assert_fails!((BTreeMap::from([("apple", 1), ("banana", 2), ("cherry", 3)]))
            .contains_exactly_keys(&["banana"]),
            expected it "to contain exactly the keys <[ \"banana\" ]>"
            but it "was <[ \"apple\" => 1, \"banana\" => 2, \"cherry\" => 3 ]>, \
                which additionally has <[ \"apple\", \"cherry\" ]>");
    }

    #[test]
    fn contains_exactly_keys_fails_for_map_with_missing_and_additional_keys() {
        assert_fails!((BTreeMap::from([("apple", 1), ("banana", 2), ("cherry", 3)]))
            .contains_exactly_keys(&["apple", "dragon fruit", "cherry"]),
            expected it "to contain exactly the keys <[ \"apple\", \"dragon fruit\", \"cherry\" ]>"
            but it "was <[ \"apple\" => 1, \"banana\" => 2, \"cherry\" => 3 ]>, \
                which lacks <[ \"dragon fruit\" ]> and additionally has <[ \"banana\" ]>");
    }

    #[test]
    fn to_keys_works_for_empty_map() {
        assert_that!(HashMap::<&str, i32>::new())
            .to_keys()
            .is_empty();
    }

    #[test]
    fn to_keys_works_on_singleton_map() {
        assert_that!(&HashMap::from([("apple", 1)]))
            .to_keys()
            .contains_exactly_in_any_order(["apple"]);
    }

    #[test]
    fn to_keys_works_on_larger_map() {
        assert_that!(BTreeMap::from([("apple", 1), ("banana", 2), ("cherry", 3)]))
            .to_keys()
            .contains_exactly_in_any_order(["apple", "banana", "cherry"]);
    }

    #[test]
    fn to_keys_has_correct_expression() {
        let mut map = HashMap::from([("apple", 1)]);
        let expression = assert_that!(&mut map).to_keys().expression;

        assert_that!(expression.as_str()).is_equal_to("keys of <&mut map>");
    }

    #[test]
    fn to_values_works_for_empty_map() {
        assert_that!(HashMap::<&str, i32>::new())
            .to_values()
            .is_empty();
    }

    #[test]
    fn to_values_works_on_singleton_map() {
        assert_that!(&HashMap::from([("apple", 1)]))
            .to_values()
            .contains_exactly_in_any_order([1]);
    }

    #[test]
    fn to_values_works_on_larger_map() {
        assert_that!(BTreeMap::from([("apple", 1), ("banana", 2), ("cherry", 3)]))
            .to_values()
            .contains_exactly_in_any_order([1, 2, 3]);
    }

    #[test]
    fn to_values_has_correct_expression() {
        let mut map = HashMap::from([("apple", 1)]);
        let expression = assert_that!(&mut map).to_values().expression;

        assert_that!(expression.as_str()).is_equal_to("values of <&mut map>");
    }

    #[test]
    fn to_entries_works_for_empty_map() {
        assert_that!(HashMap::<&str, i32>::new())
            .to_entries()
            .is_empty();
    }

    #[test]
    fn to_entries_works_on_singleton_map() {
        assert_that!(&HashMap::from([("apple", 1)]))
            .to_entries()
            .contains_exactly_in_any_order([(&"apple", &1)]);
    }

    #[test]
    fn to_entries_works_on_larger_map() {
        assert_that!(BTreeMap::from([("apple", 1), ("banana", 2), ("cherry", 3)]))
            .to_entries()
            .contains_exactly_in_any_order([(&"apple", &1), (&"banana", &2), (&"cherry", &3)]);
    }

    #[test]
    fn to_entries_has_correct_expression() {
        let mut map = HashMap::from([("apple", 1)]);
        let expression = assert_that!(&mut map).to_entries().expression;

        assert_that!(expression.as_str()).is_equal_to("entries of <&mut map>");
    }
}
