use criterion::{criterion_group, criterion_main};

mod common;

criterion_group!(tick_bitmap_benches, common::bench_tick_bitmap);
criterion_main!(tick_bitmap_benches);
