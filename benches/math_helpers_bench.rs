use criterion::{criterion_group, criterion_main};

mod common;

criterion_group!(math_helpers_benches, common::bench_math_helpers);
criterion_main!(math_helpers_benches);
