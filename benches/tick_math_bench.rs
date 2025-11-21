use criterion::{criterion_group, criterion_main};

mod common;

criterion_group!(tick_math_benches, common::bench_tick_math,);
criterion_main!(tick_math_benches);
