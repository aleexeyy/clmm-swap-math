use criterion::{criterion_group, criterion_main};

mod common;

criterion_group!(swap_math_benches, common::bench_swap_math);
criterion_main!(swap_math_benches);
