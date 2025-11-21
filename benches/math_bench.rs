use criterion::{criterion_group, criterion_main};

mod common;

criterion_group!(
    math_benches,
    common::bench_tick_math,
    common::bench_sqrt_price_math,
    common::bench_swap_math,
    common::bench_math_helpers,
    common::bench_tick_bitmap,
    common::bench_bit_math,
);
criterion_main!(math_benches);
