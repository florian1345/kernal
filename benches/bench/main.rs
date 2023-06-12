use std::collections::HashMap;
use std::time::Duration;

use criterion::{BenchmarkGroup, Criterion};
use criterion::measurement::WallTime;

use kernal::prelude::*;
use kernal::fast_prelude::*;

fn bench_collection_with_different_sizes(name: &str, operation: impl Fn(&[u64]),
        group: &mut BenchmarkGroup<WallTime>) {
    const SIZES: [usize; 4] = [ 64, 256, 1024, 4096 ];

    for size in SIZES {
        let id = format!("{}_{}", name, size);
        let vec = (0..(size as u64)).collect::<Vec<_>>();

        group.bench_function(id, |bencher| bencher.iter(|| operation(&vec)));
    }
}

fn bench_collection_contains_all_of(group: &mut BenchmarkGroup<WallTime>) {
    fn contained_items(slice: &[u64]) -> Vec<u64> {
        let len = slice.len() as u64;

        (0..(len / 2))
            .map(|offset| len / 4 + offset)
            .collect()
    }

    bench_collection_with_different_sizes("vec", |slice| {
        assert_that!(slice).contains_all_of(contained_items(slice));
    }, group);

    bench_collection_with_different_sizes("hash", |slice| {
        assert_that!(slice).contains_all_of_using_hash(contained_items(slice));
    }, group);

    bench_collection_with_different_sizes("ord", |slice| {
        assert_that!(slice).contains_all_of_using_ord(contained_items(slice));
    }, group);
}

fn bench_collection_contains_none_of(group: &mut BenchmarkGroup<WallTime>) {
    fn uncontained_items(slice: &[u64]) -> Vec<u64> {
        let len = slice.len() as u64;

        (0..len)
            .map(|offset| len + offset + 1)
            .collect()
    }

    bench_collection_with_different_sizes("vec", |slice| {
        assert_that!(slice).contains_none_of(uncontained_items(slice));
    }, group);

    bench_collection_with_different_sizes("hash", |slice| {
        assert_that!(slice).contains_none_of_using_hash(uncontained_items(slice));
    }, group);

    bench_collection_with_different_sizes("ord", |slice| {
        assert_that!(slice).contains_none_of_using_ord(uncontained_items(slice));
    }, group);
}

fn bench_collection_contains_exactly_in_any_order(group: &mut BenchmarkGroup<WallTime>) {
    fn exact_items(slice: &[u64]) -> Vec<u64> {
        slice.iter().cloned().rev().collect()
    }

    bench_collection_with_different_sizes("vec", |slice| {
        assert_that!(slice).contains_exactly_in_any_order(exact_items(slice));
    }, group);

    bench_collection_with_different_sizes("hash", |slice| {
        assert_that!(slice).contains_exactly_in_any_order_using_hash(exact_items(slice));
    }, group);

    bench_collection_with_different_sizes("ord", |slice| {
        assert_that!(slice).contains_exactly_in_any_order_using_ord(exact_items(slice));
    }, group);
}

fn bench_map_with_different_sizes(name: &str, operation: impl Fn(&HashMap<u64, u64>),
        group: &mut BenchmarkGroup<WallTime>) {
    const SIZES: [usize; 4] = [ 64, 256, 1024, 4096 ];

    for size in SIZES {
        let id = format!("{}_{}", name, size);
        let map = (0..(size as u64))
            .map(|key| (key, key * key))
            .collect::<HashMap<_, _>>();

        group.bench_function(id, |bencher| bencher.iter(|| operation(&map)));
    }
}

fn bench_map_contains_values(group: &mut BenchmarkGroup<WallTime>) {
    fn contained_values(map: &HashMap<u64, u64>) -> Vec<u64> {
        let len = map.len() as u64;

        (0..(len / 2))
            .map(|offset| (len / 4 + offset) * (len / 4 + offset))
            .collect()
    }

    bench_map_with_different_sizes("vec", |map| {
        assert_that!(map).contains_values(contained_values(map));
    }, group);

    bench_map_with_different_sizes("hash", |map| {
        assert_that!(map).contains_values_using_hash(contained_values(map));
    }, group);

    bench_map_with_different_sizes("ord", |map| {
        assert_that!(map).contains_values_using_ord(contained_values(map));
    }, group);
}

fn bench_map_contains_exactly_values(group: &mut BenchmarkGroup<WallTime>) {
    fn contained_values(map: &HashMap<u64, u64>) -> Vec<u64> {
        (0..map.len() as u64).rev().map(|key| key * key).collect()
    }

    bench_map_with_different_sizes("vec", |map| {
        assert_that!(map).contains_exactly_values(contained_values(map));
    }, group);

    bench_map_with_different_sizes("hash", |map| {
        assert_that!(map).contains_exactly_values_using_hash(contained_values(map));
    }, group);

    bench_map_with_different_sizes("ord", |map| {
        assert_that!(map).contains_exactly_values_using_ord(contained_values(map));
    }, group);
}

fn make_group<'c>(name: &str, c: &'c mut Criterion) -> BenchmarkGroup<'c, WallTime> {
    let mut group = c.benchmark_group(name);

    group
        .measurement_time(Duration::from_secs(10))
        .sample_size(100);

    group
}

fn all_benches(c: &mut Criterion) {
    bench_collection_contains_all_of(
        &mut make_group("collection_contains_all_of", c));
    bench_collection_contains_none_of(
        &mut make_group("collection_contains_none_of", c));
    bench_collection_contains_exactly_in_any_order(
        &mut make_group("collection_contains_exactly_in_any_order", c));

    bench_map_contains_values(
        &mut make_group("map_contains_values", c));
    bench_map_contains_exactly_values(
        &mut make_group("map_contains_exactly_values", c));
}

criterion::criterion_group!(benches, all_benches);
criterion::criterion_main!(benches);
