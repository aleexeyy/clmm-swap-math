use criterion::{criterion_group, criterion_main};

mod common;

criterion_group!(bit_math_benches, common::bench_bit_math);
criterion_main!(bit_math_benches);
