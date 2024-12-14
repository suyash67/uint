use crate::prelude::*;

pub fn group(criterion: &mut Criterion) {
    // BN254 parameters
    const MOD: Uint<256, 4> =
        uint!(21888242871839275222246405745257275088548364400416034343698204186575808495617_U256);
    const MOD_INV: u64 = 14042775128853446655;

    bench_mul_redc::<256, 4>(criterion, MOD, MOD_INV);
    bench_mul_redc_cios::<256, 4>(criterion, MOD, MOD_INV);

    bench_square_redc::<256, 4>(criterion, MOD, MOD_INV);
    bench_square_redc_cios::<256, 4>(criterion, MOD, MOD_INV);
    bench_square_redc_cios_alternative::<256, 4>(criterion, MOD, MOD_INV);
    bench_square_redc_cios_optimal::<256, 4, 10>(criterion, MOD, MOD_INV);
}

fn bench_mul_redc<const BITS: usize, const LIMBS: usize>(
    criterion: &mut Criterion,
    modulus: Uint<BITS, LIMBS>,
    mod_inv: u64,
) {
    // Prepare input values for benchmarking
    let input = (
        Uint::<BITS, LIMBS>::arbitrary(), // Randomly generated value for `self`
        Uint::<BITS, LIMBS>::arbitrary(), // Randomly generated value for `other`
    );
    let mut runner = TestRunner::deterministic(); // Ensure reproducible benchmarks

    criterion.bench_function(&format!("mul_redc/{BITS}"), move |bencher| {
        bencher.iter_batched(
            || {
                let (self_val, other_val) = input.new_tree(&mut runner).unwrap().current();
                (self_val, other_val)
            },
            |(self_val, other_val)| {
                black_box(self_val.mul_redc(
                    black_box(other_val),
                    black_box(modulus),
                    black_box(mod_inv),
                ))
            },
            BatchSize::SmallInput,
        );
    });
}

fn bench_mul_redc_cios<const BITS: usize, const LIMBS: usize>(
    criterion: &mut Criterion,
    modulus: Uint<BITS, LIMBS>,
    mod_inv: u64,
) {
    // Prepare input values for benchmarking
    let input = (
        Uint::<BITS, LIMBS>::arbitrary(), // Randomly generated value for `self`
        Uint::<BITS, LIMBS>::arbitrary(), // Randomly generated value for `other`
    );
    let mut runner = TestRunner::deterministic(); // Ensure reproducible benchmarks

    criterion.bench_function(&format!("mul_redc_cios/{BITS}"), move |bencher| {
        bencher.iter_batched(
            || {
                let (self_val, other_val) = input.new_tree(&mut runner).unwrap().current();
                (self_val, other_val)
            },
            |(self_val, other_val)| {
                black_box(self_val.mul_redc_cios(
                    black_box(other_val),
                    black_box(modulus),
                    black_box(mod_inv),
                ))
            },
            BatchSize::SmallInput,
        );
    });
}

fn bench_square_redc<const BITS: usize, const LIMBS: usize>(
    criterion: &mut Criterion,
    modulus: Uint<BITS, LIMBS>,
    mod_inv: u64,
) {
    // Prepare input values for benchmarking
    let input = Uint::<BITS, LIMBS>::arbitrary();
    let mut runner = TestRunner::deterministic();

    criterion.bench_function(&format!("square_redc/{BITS}"), move |bencher| {
        bencher.iter_batched(
            || input.new_tree(&mut runner).unwrap().current(),
            |self_val| black_box(self_val.square_redc(black_box(modulus), black_box(mod_inv))),
            BatchSize::SmallInput,
        );
    });
}

fn bench_square_redc_cios<const BITS: usize, const LIMBS: usize>(
    criterion: &mut Criterion,
    modulus: Uint<BITS, LIMBS>,
    mod_inv: u64,
) {
    // Prepare input values for benchmarking
    let input = Uint::<BITS, LIMBS>::arbitrary();
    let mut runner = TestRunner::deterministic();

    criterion.bench_function(&format!("square_redc_cios/{BITS}"), move |bencher| {
        bencher.iter_batched(
            || input.new_tree(&mut runner).unwrap().current(),
            |self_val| black_box(self_val.square_redc_cios(black_box(modulus), black_box(mod_inv))),
            BatchSize::SmallInput,
        );
    });
}

fn bench_square_redc_cios_alternative<const BITS: usize, const LIMBS: usize>(
    criterion: &mut Criterion,
    modulus: Uint<BITS, LIMBS>,
    mod_inv: u64,
) {
    // Prepare input values for benchmarking
    let input = Uint::<BITS, LIMBS>::arbitrary();
    let mut runner = TestRunner::deterministic();

    criterion.bench_function(&format!("mul_redc_cios_alt/{BITS}"), move |bencher| {
        bencher.iter_batched(
            || input.new_tree(&mut runner).unwrap().current(),
            |self_val| {
                black_box(self_val.mul_redc_cios(
                    black_box(self_val),
                    black_box(modulus),
                    black_box(mod_inv),
                ))
            },
            BatchSize::SmallInput,
        );
    });
}

fn bench_square_redc_cios_optimal<const BITS: usize, const LIMBS: usize, const IM_SIZE: usize>(
    criterion: &mut Criterion,
    modulus: Uint<BITS, LIMBS>,
    mod_inv: u64,
) {
    // Prepare input values for benchmarking
    let input = Uint::<BITS, LIMBS>::arbitrary();
    let mut runner = TestRunner::deterministic();

    criterion.bench_function(&format!("square_redc_cios_opt/{BITS}"), move |bencher| {
        bencher.iter_batched(
            || input.new_tree(&mut runner).unwrap().current(),
            |self_val| {
                black_box(
                    self_val.square_redc_cios_optimal::<IM_SIZE>(
                        black_box(modulus),
                        black_box(mod_inv),
                    ),
                )
            },
            BatchSize::SmallInput,
        );
    });
}
