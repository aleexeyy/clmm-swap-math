use criterion::{criterion_group, criterion_main};

mod common;

criterion_group!(sqrt_price_math_benches, common::bench_sqrt_price_math);
criterion_main!(sqrt_price_math_benches);
