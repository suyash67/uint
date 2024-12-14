use core::{cmp::Ordering, f32::consts::E, iter::zip, u64};

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
    for (j, &b) in b.iter().enumerate() {
        let mut m = 0;
        let mut carry_1 = 0;
        let mut carry_2 = 0;
        // [b0 * a0   b0 * a1  ...]
        for i in 0..N {
            // println!("i = {}, j = {}", i, j);
            // Add limb product
            let (value, next_carry) = carrying_mul_add(a[i], b, result[i], carry_1);
            carry_1 = next_carry;

            // println!("  val1 = {:#016X}", value);
            // println!("  car1 = {:#016X}", carry_1);

            if i == 0 {
                // Compute reduction factor
                // TODO: this computes mod 2^64 because we're using u64 by default, fix for
                // general width.
                m = value.wrapping_mul(inv);

                // println!("  q_{} = {:#016X}", i, m);
            }

            // Add m * modulus to acc to clear next_result[0]
            let (value, next_carry) = carrying_mul_add(modulus[i], m, value, carry_2);
            carry_2 = next_carry;

            // println!("  val2 = {:#016X}", value);
            // println!("  car2 = {:#016X}", carry_2);

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

/// Computes a * b * 2^(-BITS) mod modulus
///
/// Requires that `inv` is the inverse of `-modulus[0]` modulo `2^64`.
/// Requires that `a` and `b` are less than `modulus`.
#[inline]
#[must_use]
pub fn mul_redc_cios<const N: usize>(
    a: [u64; N],
    b: [u64; N],
    modulus: [u64; N],
    inv: u64,
) -> [u64; N] {
    debug_assert_eq!(inv.wrapping_mul(modulus[0]), u64::MAX);
    debug_assert!(less_than(a, modulus));
    debug_assert!(less_than(b, modulus));

    let mut result = [0u64; N];
    let mut carry_1 = 0u64;
    let mut carry_2 = 0u64;

    for i in 0..N {
        // case j = 0
        let (value, local_carry) = carrying_mul_add(a[0], b[i], result[0], 0);
        result[0] = value;
        carry_2 = local_carry;

        let m = result[0].wrapping_mul(inv);

        // c1 = (t[0] + m * p[0]) / W
        let (_, local_carry) = carrying_mul_add(m, modulus[0], result[0], 0);
        carry_1 = local_carry;

        // case j = 1, ..., N - 1
        for j in 1..N {
            let (value, local_carry) = carrying_mul_add(a[j], b[i], result[j], carry_2);
            result[j] = value;
            carry_2 = local_carry;

            let (value, local_carry) = carrying_mul_add(m, modulus[j], result[j], carry_1);
            result[j - 1] = value;
            carry_1 = local_carry;
        }

        let (value, _) = carry_1.overflowing_add(carry_2);
        result[N - 1] = value;
    }

    reduce1_carry(result, modulus, false)
}

/// Computes a * b * 2^(-BITS) mod modulus
///
/// Requires that `inv` is the inverse of `-modulus[0]` modulo `2^64`.
/// Requires that `a` and `b` are less than `modulus`.
#[inline]
#[must_use]
pub fn square_redc_cios<const N: usize>(a: [u64; N], modulus: [u64; N], inv: u64) -> [u64; N] {
    debug_assert_eq!(inv.wrapping_mul(modulus[0]), u64::MAX);
    debug_assert!(less_than(a, modulus));

    let mut result = [0u64; N];
    let mut carry_1 = 0u64;
    let mut carry_2 = 0u64;

    for i in 0..N {
        // case j = 0
        let (value, local_carry) = carrying_mul_add(a[0], a[i], result[0], 0);
        result[0] = value;
        carry_2 = local_carry;

        let m = result[0].wrapping_mul(inv);

        // c1 = (t[0] + m * p[0]) / W
        let (_, local_carry) = carrying_mul_add(m, modulus[0], result[0], 0);
        carry_1 = local_carry;

        // case j = 1, ..., N - 1
        for j in 1..N {
            let (value, local_carry) = carrying_mul_add(a[j], a[i], result[j], carry_2);
            result[j] = value;
            carry_2 = local_carry;

            let (value, local_carry) = carrying_mul_add(m, modulus[j], result[j], carry_1);
            result[j - 1] = value;
            carry_1 = local_carry;
        }

        let (value, _) = carry_1.overflowing_add(carry_2);
        result[N - 1] = value;
    }

    reduce1_carry(result, modulus, false)
}

/// Computes a * b * 2^(-BITS) mod modulus
///
/// Requires that `inv` is the inverse of `-modulus[0]` modulo `2^64`.
/// Requires that `a` and `b` are less than `modulus`.
#[inline]
#[must_use]
pub fn square_redc_cios_optimal<const N: usize, const I: usize>(
    a: [u64; N],
    modulus: [u64; N],
    inv: u64,
) -> [u64; N] {
    debug_assert_eq!(inv.wrapping_mul(modulus[0]), u64::MAX);
    debug_assert!(less_than(a, modulus));

    let mut result = [0u64; N];
    let mut intermediate_array: [u128; I] = [0u128; I];
    let mut carry_1 = 0u64;
    let mut carry_2 = 0u64;

    let calc_index = |i: usize, j: usize| -> usize { N * i - ((i * i + i) >> 1) + j };

    for i in 0..N {
        // case j = 0
        (result[0], carry_2) = carrying_mul_add(a[0], a[i], result[0], 0);

        let m = result[0].wrapping_mul(inv);

        (_, carry_1) = carrying_mul_add(m, modulus[0], result[0], 0);

        // case j = 1, ..., N - 1
        for j in 1..N {
            let mut temp_mult = 0u128;
            if i <= j {
                // Upper half of matrix: perform mult
                temp_mult = (a[j] as u128).wrapping_mul(a[i] as u128);
                intermediate_array[calc_index(i, j)] = temp_mult;
            } else {
                // Lower half of matrix: no mult, only add
                temp_mult = intermediate_array[calc_index(j, i)];
            }

            let temp_result = temp_mult
                .wrapping_add(result[j] as u128)
                .wrapping_add(carry_2 as u128);

            result[j] = temp_result as u64;
            carry_2 = (temp_result >> 64) as u64;

            (result[j - 1], carry_1) = carrying_mul_add(m, modulus[j], result[j], carry_1);
        }

        (result[N - 1], _) = carry_1.overflowing_add(carry_2);
    }

    reduce1_carry(result, modulus, false)
}

/// Computes a * b * 2^(-BITS) mod modulus
///
/// Requires that `inv` is the inverse of `-modulus[0]` modulo `2^64`.
/// Requires that `a` and `b` are less than `modulus`.
#[inline]
#[must_use]
pub fn square_redc_simple<const N: usize>(a: [u64; N], modulus: [u64; N], inv: u64) -> [u64; N] {
    debug_assert_eq!(inv.wrapping_mul(modulus[0]), u64::MAX);
    debug_assert!(less_than(a, modulus));

    // Coarsely Integrated Operand Scanning (CIOS)
    // See <https://www.microsoft.com/en-us/research/wp-content/uploads/1998/06/97Acar.pdf>
    // See <https://hackmd.io/@gnark/modular_multiplication#fn1>
    // See <https://tches.iacr.org/index.php/TCHES/article/view/10972>
    let mut result = [0; N];
    let mut intermediate_matrix = [[(0, 0); N]; N];
    let mut carry = false;
    for j in 0..N {
        let mut m = 0;
        let mut carry_1 = 0;
        let mut carry_2 = 0;
        for i in 0..N {
            // Add limb product
            println!("i = {}, j = {}", i, j);
            let value = if i >= j {
                // Lower triangle of matrix (incl diagonal)
                let (val, next_carry) = carrying_mul_add(a[i], a[j], result[i], carry_1);
                carry_1 = next_carry;
                intermediate_matrix[i][j] = (val, next_carry);
                println!("  lower:\n    val = {}\n    car = {}", val, next_carry);
                val
            } else {
                // Upper triangle of matrix
                let (val, carry_bit) = carrying_add(intermediate_matrix[j][i].0, result[j], false);
                // TODO: check with yuval the carry bit shenanigans
                carry_1 = intermediate_matrix[j][i].1 + (carry_bit as u64);
                val
            };
            println!("  val1 = {:#016X}", value);
            println!("  car1 = {:#016X}", carry_1);

            if i == 0 {
                // Compute reduction factor
                m = value.wrapping_mul(inv);

                println!("  q_{} = {:#016X}", i, m);
            }

            // Add m * modulus to acc to clear next_result[0]
            let (value, next_carry) = carrying_mul_add(modulus[i], m, value, carry_2);
            carry_2 = next_carry;

            println!("  val2 = {:#016X}", value);
            println!("  car2 = {:#016X}", carry_2);

            // Shift result
            if i > 0 {
                result[i - 1] = value;
            } else {
                debug_assert_eq!(value, 0);
            }
            // println!("result = {:#032X}", result);
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

/// Computes a * b * 2^(-BITS) mod modulus
///
/// Requires that `inv` is the inverse of `-modulus[0]` modulo `2^64`.
/// Requires that `a` and `b` are less than `modulus`.
#[inline]
#[must_use]
pub fn lazy_mul_redc<const N: usize, const W: usize, const NSAFE: usize>(
    a: [u64; N],
    b: [u64; N],
    modulus: [u64; N],
    inv: u64,
) -> [u64; N] {
    debug_assert_eq!(inv.wrapping_mul(modulus[0]), u64::MAX);
    debug_assert!(less_than(a, modulus));
    debug_assert!(less_than(b, modulus));

    // See <https://github.com/mitschabaude/montgomery/blob/main/doc/zprize22.md>
    let mut result = [0; N];

    for i in 0..N {
        println!("\ni = {}\n", i);
        // Unroll the j = 0 case
        // First compute (t, c) = S_0 + x_i * y_0
        let value_with_carry = naive_mul_add(a[i], b[0], result[0] as u128);
        println!("j = 0:");
        println!("t0 = {:#032X}", value_with_carry);

        // Compute reduction factor q_i = t * inv
        let q_i = modulo::<W>(extract_limb::<W>(value_with_carry).wrapping_mul(inv));

        println!("q_{} = {:#016X}", i, q_i);

        // Compute (_, c) = t + q_i * p_0
        let value_with_carry = naive_mul_add(q_i, modulus[0], value_with_carry);
        let mut carry_internal = extract_carry::<W>(value_with_carry);
        println!("t0 = {:#032X}", value_with_carry);
        println!("carry = {:#016X}", carry_internal);

        for j in 1..(N - 1) {
            println!("j = {}:", j);
            println!("a[{}] = {}", i, a[i]);
            println!("b[{}] = {}", j, b[j]);
            println!("m[{}] = {}", j, modulus[j]);
            let mut value_with_carry =
                naive_mul_tuple_add(a[i], b[j], q_i, modulus[j], result[j] as u128);
            println!("t{} = {:#032X}", j, value_with_carry);
            if ((j - 1) % NSAFE) == 0 {
                value_with_carry = naive_add(value_with_carry, carry_internal);
            }
            if (j % NSAFE) == 0 {
                carry_internal = extract_carry::<W>(value_with_carry);
                println!("carry = {:#016X}", carry_internal);
            }
            println!("final t{} = {:#032X}", j, value_with_carry);
            result[j - 1] = extract_limb::<W>(value_with_carry);
        }

        // Unroll the j = N - 1 case
        println!("j = {}", N - 1);
        if (N - 2) % NSAFE == 0 {
            let value_with_carry =
                naive_mul_tuple_add(a[i], b[N - 1], q_i, modulus[N - 1], result[N - 1] as u128);
            result[N - 2] = extract_limb::<W>(value_with_carry);
            result[N - 1] = extract_carry::<W>(value_with_carry);
        } else {
            let value_with_carry = naive_mul_tuple_add(a[i], b[N - 1], q_i, modulus[N - 1], 0);
            result[N - 2] = extract_limb::<W>(value_with_carry);
        }
    }

    let mut carry_final = 0u64;
    for j in 0..N {
        let value_with_carry = naive_add(result[j] as u128, carry_final);
        result[j] = extract_limb::<W>(value_with_carry);
        carry_final = extract_carry::<W>(value_with_carry);
    }

    result
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

/// Computes a^2 * 2^(-BITS) mod modulus
///
/// Requires that `inv` is the inverse of `-modulus[0]` modulo `2^64`.
/// Requires that `a` is less than `modulus`.
#[inline]
#[must_use]
#[allow(clippy::cast_possible_truncation)]
pub fn carry_safe_square_redc<const N: usize, const NSAFE: usize>(
    a: [u64; N],
    modulus: [u64; N],
    inv: u64,
) -> [u64; N] {
    debug_assert_eq!(inv.wrapping_mul(modulus[0]), u64::MAX);
    debug_assert!(less_than(a, modulus));
    debug_assert!(NSAFE > 0);

    let mut result = [0; N];
    let mut result_products_counter = [0; N];
    let mut carry_outer = 0;
    for i in 0..N {
        // Add limb product
        let mut carry_lo: u64 = 0;
        let mut carry_hi = false;
        if (result_products_counter[i] - 1) % NSAFE == 0 {
            let value = (result[i] as u128)
                .wrapping_add(carry_lo as u128)
                .wrapping_add((carry_hi as u128) << 64);
            result[i] = (value as u64);
        }
        if result_products_counter[i] % NSAFE == 0 {
            let (value, carry_lo) = carrying_mul_add(a[i], a[i], result[i], 0);
            result[i] = value;
            result_products_counter[i] += 1;
        } else {
            let value = carryless_mul_add(a[i], a[i], result[i]);
            result[i] = value;
        }

        let (value, mut carry_lo) = carrying_mul_add(a[i], a[i], result[i], 0);
        let mut carry_hi = false;
        result[i] = value;
        for j in (i + 1)..N {
            if result_products_counter[i] % NSAFE == 0 {
                let (value, next_carry_lo, next_carry_hi) =
                    carrying_double_mul_add(a[i], a[j], result[j], carry_lo, carry_hi);
                result[j] = value;
                result_products_counter[j] += 2;
            }

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

/// Computes a^2 * 2^(-BITS) mod modulus
///
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
        println!("val[{}] = {}", i, value);
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
fn extract_limb<const W: usize>(value: u128) -> u64 {
    let mask = (1u128 << W) - 1;
    (value & mask) as u64
}

#[inline]
#[must_use]
fn extract_carry<const W: usize>(value: u128) -> u64 {
    modulo::<W>((value >> W) as u64)
}

#[inline]
#[must_use]
fn modulo<const W: usize>(value: u64) -> u64 {
    let mask = ((1u128 << W) - 1) as u64;
    println!("valu = {:#016X}", value);
    println!("mask = {:#016X}", mask);
    value & mask
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

/// Compute `lhs * rhs + add`.
/// The output can not overflow for any input values.
#[inline]
#[must_use]
#[allow(clippy::cast_possible_truncation)]
const fn carryless_mul_add(lhs: u64, rhs: u64, add: u64) -> u64 {
    lhs.wrapping_mul(rhs).wrapping_add(add)
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
const fn naive_mul_add(lhs: u64, rhs: u64, add: u128) -> u128 {
    (lhs as u128).wrapping_mul(rhs as u128).wrapping_add(add)
}

/// Compute `lhs_1 * rhs_1 + lhs_2 * rhs_2 + add`.
/// The output can not overflow for any input values.
#[inline]
#[must_use]
#[allow(clippy::cast_possible_truncation)]
// TODO : make const
fn naive_mul_tuple_add(lhs_1: u64, rhs_1: u64, lhs_2: u64, rhs_2: u64, add: u128) -> u128 {
    let wide_1 = (lhs_1 as u128).wrapping_mul(rhs_1 as u128);
    let wide_2 = (lhs_2 as u128).wrapping_mul(rhs_2 as u128);
    println!("    wide1 = {:#032X}", wide_1);
    println!("    wide2 = {:#032X}", wide_2);
    wide_1.wrapping_add(wide_2).wrapping_add(add)
}

/// Compute `lhs_1 * rhs_1 + lhs_2 * rhs_2 + add + carry`.
/// The output can not overflow for any input values.
#[inline]
#[must_use]
#[allow(clippy::cast_possible_truncation)]
const fn mul_add_tuple(lhs_1: u64, rhs_1: u64, lhs_2: u64, rhs_2: u64, add: u64) -> (u64, u64) {
    let wide_1 = (lhs_1 as u128).wrapping_mul(rhs_1 as u128);
    let wide_2 = (lhs_2 as u128).wrapping_mul(rhs_2 as u128);
    let wide = (wide_1 as u128)
        .wrapping_add(wide_2 as u128)
        .wrapping_add(add as u128);
    (wide as u64, (wide >> 64) as u64)
}

/// Compute `lhs_1 * rhs_1 + lhs_2 * rhs_2 + add + carry`.
/// The output can not overflow for any input values.
#[inline]
#[must_use]
#[allow(clippy::cast_possible_truncation)]
const fn unsafe_mul_add_tuple(lhs_1: u64, rhs_1: u64, lhs_2: u64, rhs_2: u64, add: u64) -> u64 {
    let wide_1 = lhs_1.wrapping_mul(rhs_1);
    let wide_2 = lhs_2.wrapping_mul(rhs_2);
    let wide = wide_1.wrapping_add(wide_2).wrapping_add(add);
    wide
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

const fn naive_add(value: u128, add: u64) -> u128 {
    value + (add as u128)
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
    // use proptest::{prop_assert_eq, proptest};

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
    fn test_mul_redc_python() {
        const BITS: usize = 256;
        const LIMBS: usize = nlimbs(BITS);
        type U = Uint<BITS, LIMBS>;

        const MODULUS: U = uint!(
            21888242871839275222246405745257275088548364400416034343698204186575808495617_U256
        );
        const MOD_INV: u64 = 14042775128853446655;

        // let a_val: U = U::from_limbs([2, 4, 7, 8]);
        // let b_val: U = U::from_limbs([5, 6, 8, 9]);
        // let a = *a_val.as_limbs();
        // let b = *b_val.as_limbs();
        let m: [u64; 4] = *MODULUS.as_limbs();

        // let result = mul_base(mul_redc_cios(a, b, m, MOD_INV), m);
        // let result_1 = mul_base(mul_redc(a, b, m, MOD_INV), m);
        // let expected = modmul(a, b, m);
        // assert_eq!(result, expected);
        // assert_eq!(result_1, expected);

        proptest!(|(mut a_value: U, mut b_value: U)| {
            a_value %= MODULUS; // Make sure a is less than m.
            b_value %= MODULUS; // Make sure b is less than m.
            let a = *a_value.as_limbs();
            let b = *b_value.as_limbs();

            let result = mul_base(mul_redc_cios(a, b, m, MOD_INV), m);
            let result_1 = mul_base(mul_redc(a, b, m, MOD_INV), m);
            let result_2 = mul_base(square_redc_cios_optimal::<4, 10>(a, m, MOD_INV), m);
            let expected = modmul(a, b, m);

            prop_assert_eq!(result, expected);
            prop_assert_eq!(result_1, expected);
            prop_assert_eq!(result_2, expected);
        });
    }

    #[test]
    fn test_square_redc_python() {
        const BITS: usize = 256;
        const LIMBS: usize = nlimbs(BITS);
        type U = Uint<BITS, LIMBS>;

        const MODULUS: U = uint!(
            21888242871839275222246405745257275088548364400416034343698204186575808495617_U256
        );
        const MOD_INV: u64 = 14042775128853446655;

        // let a_val: U = U::from_limbs([2, 0, 0, 0]);
        // let a = *a_val.as_limbs();
        let m: [u64; 4] = *MODULUS.as_limbs();

        // let result = mul_base(square_redc_cios_optimal(a, m, MOD_INV), m);
        // let expected = modmul(a, a, m);
        // assert_eq!(result, expected);

        proptest!(|(mut a_value: U, mut b_value: U)| {
            a_value %= MODULUS; // Make sure a is less than m.
            // b_value %= MODULUS; // Make sure b is less than m.
            let a = *a_value.as_limbs();
            // let b = *b_value.as_limbs();

            let result = mul_base(mul_redc_cios(a, a, m, MOD_INV), m);
            let result_1 = mul_base(mul_redc(a, a, m, MOD_INV), m);
            let result_2 = mul_base(square_redc_cios_optimal::<4, 10>(a, m, MOD_INV), m);
            let expected = modmul(a, a, m);

            prop_assert_eq!(result, expected);
            prop_assert_eq!(result_1, expected);
            prop_assert_eq!(result_2, expected);
        });
    }

    #[test]
    fn test_square_redc_simple() {
        const_for!(BITS in NON_ZERO if (BITS >= 16) {
            const LIMBS: usize = nlimbs(BITS);
            type U = Uint<BITS, LIMBS>;
            proptest!(|(mut a: U, mut m: U)| {
                m |= U::from(1_u64); // Make sure m is odd.
                a %= m; // Make sure a is less than m.
                let a = *a.as_limbs();
                let m = *m.as_limbs();
                let inv = U64::from(m[0]).inv_ring().unwrap().neg().as_limbs()[0];

                let result = mul_base(square_redc_simple(a, m, inv), m);
                let expected = modmul(a, a, m);

                prop_assert_eq!(result, expected);
            });
        });
    }

    #[test]
    fn test_square_redc_simple_1() {
        const BITS: usize = 128;
        const LIMBS: usize = nlimbs(BITS);
        type U = Uint<BITS, LIMBS>;

        let a: U = U::from_limbs([2, 3]);
        let m: U = U::from_limbs([11, 12]);
        let a = *a.as_limbs();
        let m = *m.as_limbs();
        let inv = U64::from(m[0]).inv_ring().unwrap().neg().as_limbs()[0];

        let result = mul_base(square_redc_simple(a, m, inv), m);
        println!("\n\nsimple done\n\n");
        let result_og = mul_base(mul_redc(a, a, m, inv), m);
        let expected = modmul(a, a, m);
        assert_eq!(result_og, expected);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_lazy_mul_redc() {
        const BITS: usize = 305;
        const LIMBS: usize = nlimbs(BITS);
        type U = Uint<BITS, LIMBS>;

        let a: U = U::from_limbs([5, 1, 0, 0, 0]);
        let b: U = U::from_limbs([6, 2, 0, 0, 0]);
        let m: U = U::from_limbs([11, 12, 0, 0, 0]);
        let a = *a.as_limbs();
        let b = *b.as_limbs();
        let m = *m.as_limbs();
        let inv = U64::from(m[0]).inv_ring().unwrap().neg().as_limbs()[0];

        println!("inv = {}", inv);

        let result = mul_base(lazy_mul_redc::<5, 63, 2>(a, b, m, inv), m);
        println!("\n\nLazy done\n\n");
        let result_1 = mul_base(mul_redc(a, b, m, inv), m);
        let expected = modmul(a, b, m);
        assert_eq!(result_1, expected);
        assert_eq!(result, expected);
    }

    #[test]
    fn compare_square_redc() {
        const BITS: usize = 305;
        const LIMBS: usize = nlimbs(BITS);
        type U = Uint<BITS, LIMBS>;

        proptest!(|(mut a: U, mut m: U)| {
            m |= U::from(1_u64); // Make sure m is odd.
            a %= m; // Make sure a is less than m.
            let a = *a.as_limbs();
            let m = *m.as_limbs();
            let inv = U64::from(m[0]).inv_ring().unwrap().neg().as_limbs()[0];

            let result = square_redc_carryless(a, m, inv);
        });
    }

    #[test]
    fn test_carryless_square_redc() {
        const BITS: usize = 305;
        const LIMBS: usize = nlimbs(BITS);
        type U = Uint<BITS, LIMBS>;

        let a: U = U::from(2); // [2, 0, 0, 0, 0]
        let m: U = U::from(17);
        let a = *a.as_limbs();
        let m = *m.as_limbs();
        let inv = U64::from(m[0]).inv_ring().unwrap().neg().as_limbs()[0];

        let result = mul_base(square_redc_carryless(a, m, inv), m);
        let expected = modmul(a, a, m);
        assert_eq!(result, expected);

        // proptest!(|(mut a: U, mut m: U)| {
        //     m |= U::from(1_u64); // Make sure m is odd.
        //     a %= m; // Make sure a is less than m.
        //     let a = *a.as_limbs();
        //     let m = *m.as_limbs();
        //     let inv =
        // U64::from(m[0]).inv_ring().unwrap().neg().as_limbs()[0];

        //     let result = mul_base(square_redc_carryless(a, m, inv), m);
        //     let expected = modmul(a, a, m);

        //     prop_assert_eq!(result, expected);
        // });
    }

    #[test]
    fn compare_square_redc_bn254_u256() {
        const BITS: usize = 256;
        const LIMBS: usize = nlimbs(BITS);
        type U305 = Uint<BITS, LIMBS>;
        const MOD: U305 = uint!(
            21888242871839275222246405745257275088548364400416034343698204186575808495617_U256
        );
        const MOD_INV: u64 = 14042775128853446655;

        const RUNS: usize = 1000_000;

        // Define the strategy for generating U305 values
        let strategy = prop::array::uniform4(any::<u64>()).prop_map(|mut limbs| {
            limbs[3] &= 0x3fff_ffff_ffff_ffff; // keep only 8 bits in the last limb
            Uint::<BITS, LIMBS>::from_limbs(limbs)
        });

        let mut total_duration_mul_python = 0;
        let mut total_duration_mul_rust = 0;
        let mut total_duration_sqr_python = 0;
        let mut total_duration_sqr_rust = 0;

        let mut total_duration_lazy_sqr = 0;
        let mut total_duration_sqr_remco = 0;

        for _ in 0..RUNS {
            // Generate random input
            // Generate a random `Uint`
            let mut a = strategy
                .new_tree(&mut proptest::test_runner::TestRunner::deterministic())
                .unwrap()
                .current();
            a %= MOD; // Ensure `a` is less than MOD

            let mut b = strategy
                .new_tree(&mut proptest::test_runner::TestRunner::deterministic())
                .unwrap()
                .current();
            b %= MOD; // Ensure `b` is less than MOD

            let a_limbs = *a.as_limbs();
            let b_limbs = *b.as_limbs();
            let m_limbs = *MOD.as_limbs();

            // Time `mul_redc_cios`
            let start = Instant::now();
            let result_a = mul_redc_cios(a_limbs, b_limbs, m_limbs, MOD_INV);
            total_duration_mul_python += start.elapsed().as_nanos();

            // Time `mul_redc`
            let start = Instant::now();
            let result_b = mul_redc(a_limbs, b_limbs, m_limbs, MOD_INV);
            total_duration_mul_rust += start.elapsed().as_nanos();

            assert_eq!(result_a, result_b);

            // Time squaring using `mul_redc_cios`
            let start = Instant::now();
            let result_a = square_redc_cios(a_limbs, m_limbs, MOD_INV);
            total_duration_sqr_python += start.elapsed().as_nanos();

            // Time squaring using `mul_redc`
            let start = Instant::now();
            let result_b = mul_redc(a_limbs, a_limbs, m_limbs, MOD_INV);
            total_duration_sqr_rust += start.elapsed().as_nanos();

            assert_eq!(result_a, result_b);

            // Time squaring using `square_redc_cios_optimal`
            let start = Instant::now();
            let result_a = square_redc_cios_optimal::<4, 10>(a_limbs, m_limbs, MOD_INV);
            total_duration_lazy_sqr += start.elapsed().as_nanos();

            assert_eq!(result_a, result_b);

            // Time squaring using `square_redc_cios_optimal`
            let start = Instant::now();
            let result_a = square_redc(a_limbs, m_limbs, MOD_INV);
            total_duration_sqr_remco += start.elapsed().as_nanos();

            assert_eq!(result_a, result_b);
        }

        let avg_duration_mul_python = total_duration_mul_python as f64 / RUNS as f64;
        let avg_duration_mul_rust = total_duration_mul_rust as f64 / RUNS as f64;
        let avg_duration_sqr_python = total_duration_sqr_python as f64 / RUNS as f64;
        let avg_duration_sqr_rust = total_duration_sqr_rust as f64 / RUNS as f64;

        let avg_duration_lazy_sqr = total_duration_lazy_sqr as f64 / RUNS as f64;
        let avg_duration_sqr_remco = total_duration_sqr_remco as f64 / RUNS as f64;

        // Print results
        println!(
            "Multiplication with python over {} runs: {:.2} ns",
            RUNS, avg_duration_mul_python
        );
        println!(
            "Multiplication with rust over {} runs: {:.2} ns",
            RUNS, avg_duration_mul_rust
        );
        println!(
            "Squaring with python over {} runs: {:.2} ns",
            RUNS, avg_duration_sqr_python
        );
        println!(
            "Squaring with rust over {} runs: {:.2} ns",
            RUNS, avg_duration_sqr_rust
        );

        println!(
            "Squaring with lazy carries over {} runs: {:.2} ns",
            RUNS, avg_duration_lazy_sqr
        );
        println!(
            "Squaring with remco over {} runs: {:.2} ns",
            RUNS, avg_duration_sqr_remco
        );
    }
}
