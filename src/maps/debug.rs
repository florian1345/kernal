use std::fmt;
use std::fmt::{Debug, Formatter};

use crate::collections::{CollectionDebug, HighlightedCollectionDebug};
use crate::maps::Map;

struct MapEntryDebug<'reference, M: Map> {
    entry: (&'reference M::Key, &'reference M::Value),
}

impl<M> Debug for MapEntryDebug<'_, M>
where
    M: Map,
    M::Key: Debug,
    M::Value: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{:?} => {:?}", &self.entry.0, &self.entry.1)
    }
}

pub(crate) struct MapEntriesDebug<'reference, M: Map> {
    map_entries_debug: Vec<MapEntryDebug<'reference, M>>,
}

impl<'reference, M: Map> MapEntriesDebug<'reference, M> {
    pub(crate) fn new<I>(entries: I) -> MapEntriesDebug<'reference, M>
    where
        I: Iterator<Item = (&'reference M::Key, &'reference M::Value)>,
    {
        let map_entries_debug = entries
            .map(|entry| MapEntryDebug::<M> { entry })
            .collect::<Vec<_>>();

        MapEntriesDebug { map_entries_debug }
    }
}

impl<M> Debug for MapEntriesDebug<'_, M>
where
    M: Map,
    M::Key: Debug,
    M::Value: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{:?}",
            CollectionDebug {
                collection: &self.map_entries_debug
            }
        )
    }
}

pub(crate) struct MapDebug<'wrapper, M> {
    pub(crate) map: &'wrapper M,
}

impl<M> Debug for MapDebug<'_, M>
where
    M: Map,
    M::Key: Debug,
    M::Value: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", MapEntriesDebug::<'_, M>::new(self.map.entries()))
    }
}

pub(crate) struct HighlightedMapDebug<'wrapper, 'key, M>
where
    M: Map,
{
    pub(crate) map: &'wrapper M,
    pub(crate) highlighted_key: &'key M::Key,
}

impl<'key, M> Debug for HighlightedMapDebug<'_, 'key, M>
where
    M: Map,
    M::Key: Debug,
    M::Value: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let map_entries_debug = self
            .map
            .entries()
            .map(|entry| MapEntryDebug::<M> { entry })
            .collect::<Vec<_>>();
        let highlighted_index = map_entries_debug
            .iter()
            .enumerate()
            .find(|(_, entry)| M::are_keys_equal(entry.entry.0, self.highlighted_key))
            .map(|(index, _)| index)
            .expect("internal kernal error: highlighted key not found");

        let highlighted_collection_debug = HighlightedCollectionDebug {
            collection: &map_entries_debug,
            highlighted_sections: vec![highlighted_index..(highlighted_index + 1)],
        };

        write!(f, "{:?}", highlighted_collection_debug)
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, HashMap};

    use super::*;
    use crate::assert_that;
    use crate::prelude::*;

    #[test]
    fn map_debug_works_with_empty_map() {
        let map_debug = MapDebug {
            map: &HashMap::<String, u32>::new(),
        };
        let formatted = format!("{:?}", map_debug);

        assert_that!(formatted.as_str()).is_equal_to("[ ]");
    }

    #[test]
    fn map_debug_works_with_singleton_map() {
        let map_debug = MapDebug {
            map: &HashMap::from([("hello", 10)]),
        };
        let formatted = format!("{:?}", map_debug);

        assert_that!(formatted.as_str()).is_equal_to("[ \"hello\" => 10 ]");
    }

    #[test]
    fn map_debug_works_with_larger_map() {
        let map_debug = MapDebug {
            map: &BTreeMap::from([("apple", 3), ("banana", 5), ("cherry", 4)]),
        };
        let formatted = format!("{:?}", map_debug);

        assert_that!(formatted.as_str())
            .is_equal_to("[ \"apple\" => 3, \"banana\" => 5, \"cherry\" => 4 ]");
    }

    #[test]
    fn highlighted_map_debug_works_for_single_highlighted_entry() {
        let highlighted_map_debug = HighlightedMapDebug {
            map: &HashMap::from([("apple", 1)]),
            highlighted_key: &"apple",
        };
        let formatted = format!("{:?}", highlighted_map_debug);

        assert_that!(formatted.as_str()).is_equal_to("[ [\"apple\" => 1] ]");
    }

    #[test]
    fn highlighted_map_debug_works_for_later_highlighted_entry() {
        let highlighted_map_debug = HighlightedMapDebug {
            map: &BTreeMap::from([("apple", 1), ("banana", 2), ("cherry", 4)]),
            highlighted_key: &"banana",
        };
        let formatted = format!("{:?}", highlighted_map_debug);

        assert_that!(formatted.as_str())
            .is_equal_to("[ \"apple\" => 1, [\"banana\" => 2], \"cherry\" => 4 ]");
    }

    #[test]
    fn highlighted_map_debug_panics_if_key_does_not_exist() {
        let highlighted_map_debug = HighlightedMapDebug {
            map: &HashMap::from([("apple", 1), ("banana", 2)]),
            highlighted_key: &"cherry",
        };

        assert_that!(|| format!("{:?}", highlighted_map_debug))
            .panics_with_message("internal kernal error: highlighted key not found");
    }
}
