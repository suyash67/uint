use core::{cmp::Ordering, iter::zip};

/// Computes a * b * 2^(-BITS) mod modulus
///
/// Requires that `inv` is the inverse of `-modulus[0]` modulo `2^64`.
/// Requires that `a` and `b` are less than `modulus`.
#[inline]
#[must_use]
pub fn mul_redc<const N: usize>(a: [u64; N], b: [u64; N], modulus: [u64; N], inv: u64) -> [u64; N] {
    debug_assert_eq!(inv.wrapping_mul(modulus[0]), u64::MAX);
    debug_assert!(less_than(a, modulus));
    debug_assert!(less_than(b, modulus));

    // Coarsely Integrated Operand Scanning (CIOS)
    // See <https://www.microsoft.com/en-us/research/wp-content/uploads/1998/06/97Acar.pdf>
    // See <https://hackmd.io/@gnark/modular_multiplication#fn1>
    // See <https://tches.iacr.org/index.php/TCHES/article/view/10972>
    let mut result = [0; N];
    let mut carry = false;
    for b in b {
        let mut m = 0;
        let mut carry_1 = 0;
        let mut carry_2 = 0;
        for i in 0..N {
            // Add limb product
            let (value, next_carry) = carrying_mul_add(a[i], b, result[i], carry_1);
            carry_1 = next_carry;

            if i == 0 {
                // Compute reduction factor
                m = value.wrapping_mul(inv);
            }

            // Add m * modulus to acc to clear next_result[0]
            let (value, next_carry) = carrying_mul_add(modulus[i], m, value, carry_2);
            carry_2 = next_carry;

            // Shift result
            if i > 0 {
                result[i - 1] = value;
            } else {
                debug_assert_eq!(value, 0);
            }
        }

        // Add carries
        let (value, next_carry) = carrying_add(carry_1, carry_2, carry);
        result[N - 1] = value;
        if modulus[N - 1] >= 0x7fff_ffff_ffff_ffff {
            carry = next_carry;
        } else {
            debug_assert!(!next_carry);
        }
    }

    // Compute reduced product.
    reduce1_carry(result, modulus, carry)
}

/// Computes a^2 * 2^(-BITS) mod modulus
///
/// Requires that `inv` is the inverse of `-modulus[0]` modulo `2^64`.
/// Requires that `a` is less than `modulus`.
#[inline]
#[must_use]
#[allow(clippy::cast_possible_truncation)]
pub fn square_redc<const N: usize>(a: [u64; N], modulus: [u64; N], inv: u64) -> [u64; N] {
    debug_assert_eq!(inv.wrapping_mul(modulus[0]), u64::MAX);
    debug_assert!(less_than(a, modulus));

    let mut result = [0; N];
    let mut carry_outer = 0;
    for i in 0..N {
        // Add limb product
        let (value, mut carry_lo) = carrying_mul_add(a[i], a[i], result[i], 0);
        let mut carry_hi = false;
        result[i] = value;
        for j in (i + 1)..N {
            let (value, next_carry_lo, next_carry_hi) =
                carrying_double_mul_add(a[i], a[j], result[j], carry_lo, carry_hi);
            result[j] = value;
            carry_lo = next_carry_lo;
            carry_hi = next_carry_hi;
        }

        // Add m times modulus to result and shift one limb
        let m = result[0].wrapping_mul(inv);
        let (value, mut carry) = carrying_mul_add(m, modulus[0], result[0], 0);
        debug_assert_eq!(value, 0);
        for j in 1..N {
            let (value, next_carry) = carrying_mul_add(modulus[j], m, result[j], carry);
            result[j - 1] = value;
            carry = next_carry;
        }

        // Add carries
        if modulus[N - 1] >= 0x3fff_ffff_ffff_ffff {
            let wide = (carry_outer as u128)
                .wrapping_add(carry_lo as u128)
                .wrapping_add((carry_hi as u128) << 64)
                .wrapping_add(carry as u128);
            result[N - 1] = wide as u64;

            // Note carry_outer can be {0, 1, 2}.
            carry_outer = (wide >> 64) as u64;
            debug_assert!(carry_outer <= 2);
        } else {
            // `carry_outer` and `carry_high` are always zero.
            debug_assert!(!carry_hi);
            debug_assert_eq!(carry_outer, 0);
            let (value, carry) = carry_lo.overflowing_add(carry);
            debug_assert!(!carry);
            result[N - 1] = value;
        }
    }

    // Compute reduced product.
    debug_assert!(carry_outer <= 1);
    reduce1_carry(result, modulus, carry_outer > 0)
}

// Computes a^2 * 2^(-BITS) mod modulus
/// Requires that `inv` is the inverse of `-modulus[0]` modulo `2^64`.
/// Requires that `a` is less than `modulus`.
#[inline]
#[must_use]
#[allow(clippy::cast_possible_truncation)]
pub fn square_redc_carryless<const N: usize>(a: [u64; N], modulus: [u64; N], inv: u64) -> [u64; N] {
    debug_assert_eq!(inv.wrapping_mul(modulus[0]), u64::MAX);
    debug_assert!(less_than(a, modulus));

    let mut result = [0; N];
    for i in 0..N {
        // Add limb product
        let value = carryless_mul_add(a[i], a[i], result[i]);
        result[i] = value;
        for j in (i + 1)..N {
            let value = carryless_double_mul_add(a[i], a[j], result[j]);
            result[j] = value;
        }

        // Add m times modulus to result and shift one limb
        let m = result[0].wrapping_mul(inv);
        let value = carryless_mul_add(m, modulus[0], result[0]);
        debug_assert_eq!(value, 0);
        for j in 1..N {
            let value = carryless_mul_add(modulus[j], m, result[j]);
            result[j - 1] = value;
        }
    }

    // Compute reduced product.
    reduce1_carry(result, modulus, false)
}

#[inline]
#[must_use]
fn less_than<const N: usize>(lhs: [u64; N], rhs: [u64; N]) -> bool {
    for (lhs, rhs) in zip(lhs.iter().rev(), rhs.iter().rev()) {
        match lhs.cmp(rhs) {
            Ordering::Less => return true,
            Ordering::Greater => return false,
            Ordering::Equal => {}
        }
    }
    // lhs == rhs
    false
}

#[inline]
#[must_use]
#[allow(clippy::needless_bitwise_bool)]
fn reduce1_carry<const N: usize>(value: [u64; N], modulus: [u64; N], carry: bool) -> [u64; N] {
    let (reduced, borrow) = sub(value, modulus);
    // TODO: Ideally this turns into a cmov, which makes the whole mul_redc constant
    // time.
    if carry | !borrow {
        reduced
    } else {
        value
    }
}

#[inline]
#[must_use]
fn sub<const N: usize>(lhs: [u64; N], rhs: [u64; N]) -> ([u64; N], bool) {
    let mut result = [0; N];
    let mut borrow = false;
    for (result, (lhs, rhs)) in zip(&mut result, zip(lhs, rhs)) {
        let (value, next_borrow) = borrowing_sub(lhs, rhs, borrow);
        *result = value;
        borrow = next_borrow;
    }
    (result, borrow)
}

/// Compute `lhs * rhs + add + carry`.
/// The output can not overflow for any input values.
#[inline]
#[must_use]
#[allow(clippy::cast_possible_truncation)]
const fn carrying_mul_add(lhs: u64, rhs: u64, add: u64, carry: u64) -> (u64, u64) {
    let wide = (lhs as u128)
        .wrapping_mul(rhs as u128)
        .wrapping_add(add as u128)
        .wrapping_add(carry as u128);
    (wide as u64, (wide >> 64) as u64)
}

/// Compute `lhs * rhs + add`.
/// The output can not overflow for any input values.
#[inline]
#[must_use]
#[allow(clippy::cast_possible_truncation)]
const fn carryless_mul_add(lhs: u64, rhs: u64, add: u64) -> u64 {
    lhs.wrapping_mul(rhs).wrapping_add(add)
}

/// Compute `2 * lhs * rhs + add + carry_lo + 2^64 * carry_hi`.
/// The output can not overflow for any input values.
#[inline]
#[must_use]
#[allow(clippy::cast_possible_truncation)]
const fn carrying_double_mul_add(
    lhs: u64,
    rhs: u64,
    add: u64,
    carry_lo: u64,
    carry_hi: bool,
) -> (u64, u64, bool) {
    let wide = (lhs as u128).wrapping_mul(rhs as u128);
    let (wide, carry_1) = wide.overflowing_add(wide);
    let carries = (add as u128)
        .wrapping_add(carry_lo as u128)
        .wrapping_add((carry_hi as u128) << 64);
    let (wide, carry_2) = wide.overflowing_add(carries);
    (wide as u64, (wide >> 64) as u64, carry_1 | carry_2)
}

/// Compute `2 * lhs * rhs + add`.
/// The output can not overflow for any input values.
#[inline]
#[must_use]
#[allow(clippy::cast_possible_truncation)]
const fn carryless_double_mul_add(lhs: u64, rhs: u64, add: u64) -> u64 {
    let wide = lhs.wrapping_mul(rhs);
    let double_wide = wide.wrapping_add(wide);
    double_wide.wrapping_add(add)
}

// Helper while [Rust#85532](https://github.com/rust-lang/rust/issues/85532) stabilizes.
#[inline]
#[must_use]
const fn carrying_add(lhs: u64, rhs: u64, carry: bool) -> (u64, bool) {
    let (result, carry_1) = lhs.overflowing_add(rhs);
    let (result, carry_2) = result.overflowing_add(carry as u64);
    (result, carry_1 | carry_2)
}

// Helper while [Rust#85532](https://github.com/rust-lang/rust/issues/85532) stabilizes.
#[inline]
#[must_use]
const fn borrowing_sub(lhs: u64, rhs: u64, borrow: bool) -> (u64, bool) {
    let (result, borrow_1) = lhs.overflowing_sub(rhs);
    let (result, borrow_2) = result.overflowing_sub(borrow as u64);
    (result, borrow_1 | borrow_2)
}

#[cfg(test)]
mod test {
    use core::ops::Neg;
    use std::time::Instant;

    use super::{
        super::{addmul, div},
        *,
    };
    use crate::{aliases::U64, const_for, nlimbs, Uint};
    use proptest::{
        prelude::{any, prop, Arbitrary, Strategy},
        prop_assert_eq, proptest,
        strategy::ValueTree,
    };

    fn modmul<const N: usize>(a: [u64; N], b: [u64; N], modulus: [u64; N]) -> [u64; N] {
        // Compute a * b
        let mut product = vec![0; 2 * N];
        addmul(&mut product, &a, &b);

        // Compute product mod modulus
        let mut reduced = modulus;
        div(&mut product, &mut reduced);
        reduced
    }

    fn mul_base<const N: usize>(a: [u64; N], modulus: [u64; N]) -> [u64; N] {
        // Compute a * 2^(N * 64)
        let mut product = vec![0; 2 * N];
        product[N..].copy_from_slice(&a);

        // Compute product mod modulus
        let mut reduced = modulus;
        div(&mut product, &mut reduced);
        reduced
    }

    #[test]
    fn test_mul_redc() {
        const_for!(BITS in NON_ZERO if (BITS >= 16) {
            const LIMBS: usize = nlimbs(BITS);
            type U = Uint<BITS, LIMBS>;
            proptest!(|(mut a: U, mut b: U, mut m: U)| {
                m |= U::from(1_u64); // Make sure m is odd.
                a %= m; // Make sure a is less than m.
                b %= m; // Make sure b is less than m.
                let a = *a.as_limbs();
                let b = *b.as_limbs();
                let m = *m.as_limbs();
                let inv = U64::from(m[0]).inv_ring().unwrap().neg().as_limbs()[0];

                let result = mul_base(mul_redc(a, b, m, inv), m);
                let expected = modmul(a, b, m);

                prop_assert_eq!(result, expected);
            });
        });
    }

    #[test]
    fn test_square_redc() {
        const_for!(BITS in NON_ZERO if (BITS >= 16) {
            const LIMBS: usize = nlimbs(BITS);
            type U = Uint<BITS, LIMBS>;
            proptest!(|(mut a: U, mut m: U)| {
                m |= U::from(1_u64); // Make sure m is odd.
                a %= m; // Make sure a is less than m.
                let a = *a.as_limbs();
                let m = *m.as_limbs();
                let inv = U64::from(m[0]).inv_ring().unwrap().neg().as_limbs()[0];

                let result = mul_base(square_redc(a, m, inv), m);
                let expected = modmul(a, a, m);

                prop_assert_eq!(result, expected);
            });
        });
    }

    #[test]
    fn compare_square_redc_bn254_u305() {
        const BITS: usize = 305;
        const LIMBS: usize = nlimbs(BITS);
        type U305 = Uint<BITS, LIMBS>;
        const MOD: U305 = uint!(
            21888242871839275222246405745257275088548364400416034343698204186575808495617_U305
        );
        const MOD_INV: u64 = 14042775128853446655;

        const RUNS: usize = 1000_000;

        // Define the strategy for generating U305 values
        let strategy = prop::array::uniform5(any::<u64>()).prop_map(|mut limbs| {
            limbs[4] &= 0xff; // keep only 8 bits in the last limb
            Uint::<BITS, LIMBS>::from_limbs(limbs)
        });

        let mut total_duration_carryless = 0;
        let mut total_duration_square = 0;

        for _ in 0..RUNS {
            // Generate random input
            // Generate a random `Uint`
            let mut a = strategy
                .new_tree(&mut proptest::test_runner::TestRunner::deterministic())
                .unwrap()
                .current();
            a %= MOD; // Ensure `a` is less than MOD

            let a_limbs = *a.as_limbs();
            let m_limbs = *MOD.as_limbs();

            // Time `square_redc_carryless`
            let start = Instant::now();
            let _ = square_redc_carryless(a_limbs, m_limbs, MOD_INV);
            total_duration_carryless += start.elapsed().as_nanos();

            // Time `square_redc`
            let start = Instant::now();
            let _ = square_redc(a_limbs, m_limbs, MOD_INV);
            total_duration_square += start.elapsed().as_nanos();
        }

        let avg_duration_carryless = total_duration_carryless as f64 / RUNS as f64;
        let avg_duration_square = total_duration_square as f64 / RUNS as f64;

        // Print results
        println!(
            "`square_redc_carryless` over {} runs: {:.2} ns",
            RUNS, avg_duration_carryless
        );
        println!(
            "`square_redc` over {} runs: {:.2} ns",
            RUNS, avg_duration_square
        );
    }
}
