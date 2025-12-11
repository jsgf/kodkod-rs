//! Comprehensive tests for Int operations
//!
//! Following Java: kodkod.test.unit.IntTest
//! Tests integer arithmetic, bitwise, comparison, and shift operations
//! on both constant and circuit (non-constant) integers

use kodkod_rs::bool::{BooleanConstant, BooleanFactory, BoolValue, Int, Options};

#[test]
fn test_constant_addition() {
    // Test addition of constant integers
    let factory = BooleanFactory::new(10, Options::default());

    let a = factory.integer(5);
    let b = factory.integer(3);
    let sum = a.plus(&b, &factory);

    assert!(sum.is_constant());
    assert_eq!(sum.value(), Some(8));

    // Test with negative numbers
    let c = factory.integer(-2);
    let d = factory.integer(7);
    let sum2 = c.plus(&d, &factory);

    assert!(sum2.is_constant());
    assert_eq!(sum2.value(), Some(5));
}

#[test]
fn test_constant_subtraction() {
    let factory = BooleanFactory::new(10, Options::default());

    let a = factory.integer(10);
    let b = factory.integer(3);
    let diff = a.minus(&b, &factory);

    assert!(diff.is_constant());
    assert_eq!(diff.value(), Some(7));

    // Test with negative result
    let c = factory.integer(3);
    let d = factory.integer(10);
    let diff2 = c.minus(&d, &factory);

    assert!(diff2.is_constant());
    assert_eq!(diff2.value(), Some(-7));
}

#[test]
fn test_constant_bitwise_and() {
    let factory = BooleanFactory::new(10, Options::default());

    // 12 = 0b1100, 10 = 0b1010, 12 & 10 = 0b1000 = 8
    let a = factory.integer(12);
    let b = factory.integer(10);
    let result = a.and(&b, &factory);

    assert!(result.is_constant());
    assert_eq!(result.value(), Some(8));
}

#[test]
fn test_constant_bitwise_or() {
    let factory = BooleanFactory::new(10, Options::default());

    // 12 = 0b1100, 10 = 0b1010, 12 | 10 = 0b1110 = 14
    let a = factory.integer(12);
    let b = factory.integer(10);
    let result = a.or(&b, &factory);

    assert!(result.is_constant());
    assert_eq!(result.value(), Some(14));
}

#[test]
fn test_constant_bitwise_xor() {
    let factory = BooleanFactory::new(10, Options::default());

    // 12 = 0b1100, 10 = 0b1010, 12 ^ 10 = 0b0110 = 6
    let a = factory.integer(12);
    let b = factory.integer(10);
    let result = a.xor(&b, &factory);

    assert!(result.is_constant());
    assert_eq!(result.value(), Some(6));
}

#[test]
fn test_constant_shift_left() {
    let factory = BooleanFactory::new(10, Options::default());

    // 5 << 2 = 20
    let a = factory.integer(5);
    let shifted = a.shift_left(2);

    assert!(shifted.is_constant());
    assert_eq!(shifted.value(), Some(20));
}

#[test]
fn test_constant_shift_right() {
    let factory = BooleanFactory::new(10, Options::default());

    // 20 >> 2 = 5 (logical shift)
    let a = factory.integer(20);
    let shifted = a.shift_right(2);

    assert!(shifted.is_constant());
    assert_eq!(shifted.value(), Some(5));
}

#[test]
fn test_constant_shift_right_arithmetic() {
    let factory = BooleanFactory::new(10, Options::default());

    // -8 >>> 1 should preserve sign
    let a = factory.integer(-8);
    let shifted = a.shift_right_arithmetic(1);

    assert!(shifted.is_constant());
    // Arithmetic right shift of -8 by 1 should give -4
    assert_eq!(shifted.value(), Some(-4));
}

#[test]
fn test_constant_negate() {
    let factory = BooleanFactory::new(10, Options::default());

    let a = factory.integer(5);
    let neg = a.negate(&factory);

    assert!(neg.is_constant());
    assert_eq!(neg.value(), Some(-5));

    let b = factory.integer(-7);
    let neg2 = b.negate(&factory);

    assert!(neg2.is_constant());
    assert_eq!(neg2.value(), Some(7));
}

#[test]
fn test_constant_abs() {
    let factory = BooleanFactory::new(10, Options::default());

    let a = factory.integer(-5);
    let abs_val = a.abs(&factory);

    assert!(abs_val.is_constant());
    assert_eq!(abs_val.value(), Some(5));

    let b = factory.integer(7);
    let abs_val2 = b.abs(&factory);

    assert!(abs_val2.is_constant());
    assert_eq!(abs_val2.value(), Some(7));
}

#[test]
fn test_constant_sign() {
    let factory = BooleanFactory::new(10, Options::default());

    // Following Java: sgn() returns 2-bit int
    // bit[0] = non-zero, bit[1] = sign bit
    // Positive: [1, 0] = 1
    // Negative: [1, 1] = -1 (in 2-bit two's complement)
    // Zero: [0, 0] = 0

    // Positive number -> sign = [1, 0] = 1
    let a = factory.integer(5);
    let sign = a.sign(&factory);
    assert_eq!(sign.width(), 2);
    assert_eq!(sign.value(), Some(1));

    // Negative number -> sign = [1, 1] = -1 (in 2-bit two's complement)
    let b = factory.integer(-5);
    let sign2 = b.sign(&factory);
    assert_eq!(sign2.width(), 2);
    assert_eq!(sign2.value(), Some(-1));

    // Zero -> sign = [0, 0] = 0
    let c = factory.integer(0);
    let sign3 = c.sign(&factory);
    assert_eq!(sign3.width(), 2);
    assert_eq!(sign3.value(), Some(0));
}

#[test]
fn test_constant_not() {
    let factory = BooleanFactory::new(10, Options::default());

    // Bitwise NOT: ~5 = -6 in two's complement
    let a = factory.integer(5);
    let not_val = a.not(&factory);

    assert!(not_val.is_constant());
    assert_eq!(not_val.value(), Some(-6));
}

#[test]
fn test_constant_eq_comparison() {
    let factory = BooleanFactory::new(10, Options::default());

    let a = factory.integer(5);
    let b = factory.integer(5);
    let c = factory.integer(7);

    let eq1 = a.eq(&b, &factory);
    assert_eq!(eq1, BoolValue::Constant(BooleanConstant::TRUE));

    let eq2 = a.eq(&c, &factory);
    assert_eq!(eq2, BoolValue::Constant(BooleanConstant::FALSE));
}

#[test]
fn test_constant_lt_comparison() {
    let factory = BooleanFactory::new(10, Options::default());

    let a = factory.integer(3);
    let b = factory.integer(7);

    let lt = a.lt(&b, &factory);
    assert_eq!(lt, BoolValue::Constant(BooleanConstant::TRUE));

    let c = factory.integer(10);
    let lt2 = c.lt(&b, &factory);
    assert_eq!(lt2, BoolValue::Constant(BooleanConstant::FALSE));
}

#[test]
fn test_constant_lte_comparison() {
    let factory = BooleanFactory::new(10, Options::default());

    let a = factory.integer(5);
    let b = factory.integer(5);

    let lte = a.lte(&b, &factory);
    assert_eq!(lte, BoolValue::Constant(BooleanConstant::TRUE));

    let c = factory.integer(7);
    let lte2 = a.lte(&c, &factory);
    assert_eq!(lte2, BoolValue::Constant(BooleanConstant::TRUE));

    let lte3 = c.lte(&a, &factory);
    assert_eq!(lte3, BoolValue::Constant(BooleanConstant::FALSE));
}

#[test]
fn test_circuit_addition() {
    // Test addition with boolean circuits (non-constant)
    let factory = BooleanFactory::new(10, Options { bitwidth: 8, ..Default::default() });

    // Create an Int with a variable bit
    let v1 = factory.variable(1);
    let v2 = factory.variable(2);

    // Create Int: [v1, FALSE, TRUE, FALSE, ...] (value depends on v1)
    let bits1 = vec![
        v1,
        BoolValue::Constant(BooleanConstant::FALSE),
        BoolValue::Constant(BooleanConstant::TRUE),
        BoolValue::Constant(BooleanConstant::FALSE),
        BoolValue::Constant(BooleanConstant::FALSE),
        BoolValue::Constant(BooleanConstant::FALSE),
        BoolValue::Constant(BooleanConstant::FALSE),
        BoolValue::Constant(BooleanConstant::FALSE),
    ];
    let int1 = Int::new(bits1);

    // Create Int: [FALSE, v2, FALSE, ...] (value depends on v2)
    let bits2 = vec![
        BoolValue::Constant(BooleanConstant::FALSE),
        v2,
        BoolValue::Constant(BooleanConstant::FALSE),
        BoolValue::Constant(BooleanConstant::FALSE),
        BoolValue::Constant(BooleanConstant::FALSE),
        BoolValue::Constant(BooleanConstant::FALSE),
        BoolValue::Constant(BooleanConstant::FALSE),
        BoolValue::Constant(BooleanConstant::FALSE),
    ];
    let int2 = Int::new(bits2);

    let sum = int1.plus(&int2, &factory);

    // Sum should not be constant
    assert!(!sum.is_constant());
    assert_eq!(sum.value(), None);

    // But should have the right width
    assert!(sum.width() >= 8);
}

#[test]
fn test_circuit_comparisons() {
    // Test comparison with boolean circuits
    let factory = BooleanFactory::new(10, Options { bitwidth: 8, ..Default::default() });

    let v1 = factory.variable(1);

    // Create Int with variable bit
    let bits = vec![
        v1.clone(),
        BoolValue::Constant(BooleanConstant::FALSE),
        BoolValue::Constant(BooleanConstant::FALSE),
        BoolValue::Constant(BooleanConstant::FALSE),
        BoolValue::Constant(BooleanConstant::FALSE),
        BoolValue::Constant(BooleanConstant::FALSE),
        BoolValue::Constant(BooleanConstant::FALSE),
        BoolValue::Constant(BooleanConstant::FALSE),
    ];
    let int1 = Int::new(bits);

    let int2 = factory.integer(0);

    // Comparison should produce a circuit (not constant)
    let eq = int1.eq(&int2, &factory);
    assert_ne!(eq, BoolValue::Constant(BooleanConstant::TRUE));
    assert_ne!(eq, BoolValue::Constant(BooleanConstant::FALSE));
}

#[test]
fn test_two_complement_overflow() {
    // Test that operations handle two's complement overflow correctly
    let factory = BooleanFactory::new(10, Options { bitwidth: 8, ..Default::default() });

    // In 8-bit two's complement: 127 + 1 = -128
    let max_positive = factory.integer(127);
    let one = factory.integer(1);
    let sum = max_positive.plus(&one, &factory);

    assert!(sum.is_constant());
    assert_eq!(sum.value(), Some(-128));
}

#[test]
fn test_negative_number_representation() {
    // Verify negative numbers are correctly represented in two's complement
    let factory = BooleanFactory::new(10, Options { bitwidth: 8, ..Default::default() });

    let neg_one = factory.integer(-1);
    let bits = neg_one.twos_complement_bits();

    // -1 should be all 1s in two's complement
    for bit in bits {
        assert_eq!(*bit, BoolValue::Constant(BooleanConstant::TRUE));
    }
}

#[test]
fn test_chain_operations() {
    // Test chaining multiple operations
    let factory = BooleanFactory::new(10, Options::default());

    let a = factory.integer(10);
    let b = factory.integer(5);
    let c = factory.integer(3);

    // (10 + 5) - 3 = 12
    let result = a.plus(&b, &factory).minus(&c, &factory);

    assert!(result.is_constant());
    assert_eq!(result.value(), Some(12));
}

// ========== MULTIPLICATION TESTS ==========

#[test]
fn test_constant_multiply_positive() {
    let factory = BooleanFactory::new(10, Options { bitwidth: 8, ..Default::default() });

    // 5 * 3 = 15
    let a = factory.integer(5);
    let b = factory.integer(3);
    let product = a.multiply(&b, &factory);

    assert!(product.is_constant());
    assert_eq!(product.value(), Some(15));
}

#[test]
fn test_constant_multiply_negative() {
    let factory = BooleanFactory::new(10, Options { bitwidth: 8, ..Default::default() });

    // -5 * 3 = -15
    let a = factory.integer(-5);
    let b = factory.integer(3);
    let product = a.multiply(&b, &factory);

    assert!(product.is_constant());
    assert_eq!(product.value(), Some(-15));

    // 5 * -3 = -15
    let c = factory.integer(5);
    let d = factory.integer(-3);
    let product2 = c.multiply(&d, &factory);

    assert!(product2.is_constant());
    assert_eq!(product2.value(), Some(-15));
}

#[test]
fn test_constant_multiply_both_negative() {
    let factory = BooleanFactory::new(10, Options { bitwidth: 8, ..Default::default() });

    // -5 * -3 = 15
    let a = factory.integer(-5);
    let b = factory.integer(-3);
    let product = a.multiply(&b, &factory);

    assert!(product.is_constant());
    assert_eq!(product.value(), Some(15));
}

#[test]
fn test_constant_multiply_by_zero() {
    let factory = BooleanFactory::new(10, Options { bitwidth: 8, ..Default::default() });

    // 5 * 0 = 0
    let a = factory.integer(5);
    let zero = factory.integer(0);
    let product = a.multiply(&zero, &factory);

    assert!(product.is_constant());
    assert_eq!(product.value(), Some(0));

    // 0 * -3 = 0
    let b = factory.integer(-3);
    let product2 = zero.multiply(&b, &factory);

    assert!(product2.is_constant());
    assert_eq!(product2.value(), Some(0));
}

#[test]
fn test_constant_multiply_by_one() {
    let factory = BooleanFactory::new(10, Options { bitwidth: 8, ..Default::default() });

    // 7 * 1 = 7
    let a = factory.integer(7);
    let one = factory.integer(1);
    let product = a.multiply(&one, &factory);

    assert!(product.is_constant());
    assert_eq!(product.value(), Some(7));

    // -7 * 1 = -7
    let b = factory.integer(-7);
    let product2 = b.multiply(&one, &factory);

    assert!(product2.is_constant());
    assert_eq!(product2.value(), Some(-7));
}

#[test]
fn test_constant_multiply_overflow() {
    let factory = BooleanFactory::new(10, Options { bitwidth: 8, ..Default::default() });

    // In 8-bit: 16 * 16 = 256, which wraps to 0
    let a = factory.integer(16);
    let b = factory.integer(16);
    let product = a.multiply(&b, &factory);

    assert!(product.is_constant());
    // 256 & 0xFF = 0
    assert_eq!(product.value(), Some(0));

    // 20 * 10 = 200 (fits in 8-bit)
    let c = factory.integer(20);
    let d = factory.integer(10);
    let product2 = c.multiply(&d, &factory);

    assert!(product2.is_constant());
    assert_eq!(product2.value(), Some(-56)); // 200 in 8-bit signed is -56
}

#[test]
fn test_constant_multiply_various_values() {
    let factory = BooleanFactory::new(10, Options { bitwidth: 16, ..Default::default() });

    let test_cases = vec![
        (2, 3, 6),
        (7, 8, 56),
        (-2, 5, -10),
        (4, -3, -12),
        (-6, -7, 42),
        (0, 100, 0),
        (1, -50, -50),
    ];

    for (a_val, b_val, expected) in test_cases {
        let a = factory.integer(a_val);
        let b = factory.integer(b_val);
        let product = a.multiply(&b, &factory);

        assert!(product.is_constant(), "multiply({}, {}) should be constant", a_val, b_val);
        assert_eq!(
            product.value(),
            Some(expected),
            "multiply({}, {}) = {} expected, got {:?}",
            a_val,
            b_val,
            expected,
            product.value()
        );
    }
}

// ========== DIVISION TESTS ==========

#[test]
fn test_constant_divide_positive() {
    let factory = BooleanFactory::new(10, Options { bitwidth: 8, ..Default::default() });

    // 15 / 3 = 5
    let a = factory.integer(15);
    let b = factory.integer(3);
    let quotient = a.divide(&b, &factory);

    assert!(quotient.is_constant());
    assert_eq!(quotient.value(), Some(5));

    // 20 / 4 = 5
    let c = factory.integer(20);
    let d = factory.integer(4);
    let quotient2 = c.divide(&d, &factory);

    assert!(quotient2.is_constant());
    assert_eq!(quotient2.value(), Some(5));
}

#[test]
fn test_constant_divide_negative_dividend() {
    let factory = BooleanFactory::new(10, Options { bitwidth: 8, ..Default::default() });

    // -15 / 3 = -5
    let a = factory.integer(-15);
    let b = factory.integer(3);
    let quotient = a.divide(&b, &factory);

    assert!(quotient.is_constant());
    assert_eq!(quotient.value(), Some(-5));
}

#[test]
fn test_constant_divide_negative_divisor() {
    let factory = BooleanFactory::new(10, Options { bitwidth: 8, ..Default::default() });

    // 15 / -3 = -5
    let a = factory.integer(15);
    let b = factory.integer(-3);
    let quotient = a.divide(&b, &factory);

    assert!(quotient.is_constant());
    assert_eq!(quotient.value(), Some(-5));
}

#[test]
fn test_constant_divide_both_negative() {
    let factory = BooleanFactory::new(10, Options { bitwidth: 8, ..Default::default() });

    // -15 / -3 = 5
    let a = factory.integer(-15);
    let b = factory.integer(-3);
    let quotient = a.divide(&b, &factory);

    assert!(quotient.is_constant());
    assert_eq!(quotient.value(), Some(5));
}

#[test]
fn test_constant_divide_with_remainder() {
    let factory = BooleanFactory::new(10, Options { bitwidth: 8, ..Default::default() });

    // 17 / 5 = 3 (integer division, remainder 2)
    let a = factory.integer(17);
    let b = factory.integer(5);
    let quotient = a.divide(&b, &factory);

    assert!(quotient.is_constant());
    assert_eq!(quotient.value(), Some(3));

    // 22 / 7 = 3 (remainder 1)
    let c = factory.integer(22);
    let d = factory.integer(7);
    let quotient2 = c.divide(&d, &factory);

    assert!(quotient2.is_constant());
    assert_eq!(quotient2.value(), Some(3));
}

#[test]
fn test_constant_divide_by_one() {
    let factory = BooleanFactory::new(10, Options { bitwidth: 8, ..Default::default() });

    // 42 / 1 = 42
    let a = factory.integer(42);
    let one = factory.integer(1);
    let quotient = a.divide(&one, &factory);

    assert!(quotient.is_constant());
    assert_eq!(quotient.value(), Some(42));

    // -42 / 1 = -42
    let b = factory.integer(-42);
    let quotient2 = b.divide(&one, &factory);

    assert!(quotient2.is_constant());
    assert_eq!(quotient2.value(), Some(-42));
}

#[test]
fn test_constant_divide_zero_dividend() {
    let factory = BooleanFactory::new(10, Options { bitwidth: 8, ..Default::default() });

    // 0 / 5 = 0
    let zero = factory.integer(0);
    let b = factory.integer(5);
    let quotient = zero.divide(&b, &factory);

    assert!(quotient.is_constant());
    assert_eq!(quotient.value(), Some(0));
}

#[test]
fn test_constant_divide_various_values() {
    let factory = BooleanFactory::new(10, Options { bitwidth: 16, ..Default::default() });

    let test_cases = vec![
        (20, 4, 5),
        (100, 10, 10),
        (-50, 5, -10),
        (30, -6, -5),
        (-40, -8, 5),
        (7, 2, 3),
        (15, 4, 3),
    ];

    for (a_val, b_val, expected) in test_cases {
        let a = factory.integer(a_val);
        let b = factory.integer(b_val);
        let quotient = a.divide(&b, &factory);

        assert!(quotient.is_constant(), "divide({}, {}) should be constant", a_val, b_val);
        assert_eq!(
            quotient.value(),
            Some(expected),
            "divide({}, {}) = {} expected, got {:?}",
            a_val,
            b_val,
            expected,
            quotient.value()
        );
    }
}

// ========== MODULO TESTS ==========

#[test]
fn test_constant_modulo_positive() {
    let factory = BooleanFactory::new(10, Options { bitwidth: 8, ..Default::default() });

    // 17 % 5 = 2
    let a = factory.integer(17);
    let b = factory.integer(5);
    let remainder = a.modulo(&b, &factory);

    assert!(remainder.is_constant());
    assert_eq!(remainder.value(), Some(2));

    // 22 % 7 = 1
    let c = factory.integer(22);
    let d = factory.integer(7);
    let remainder2 = c.modulo(&d, &factory);

    assert!(remainder2.is_constant());
    assert_eq!(remainder2.value(), Some(1));
}

#[test]
fn test_constant_modulo_exact_division() {
    let factory = BooleanFactory::new(10, Options { bitwidth: 8, ..Default::default() });

    // 15 % 5 = 0 (exact division)
    let a = factory.integer(15);
    let b = factory.integer(5);
    let remainder = a.modulo(&b, &factory);

    assert!(remainder.is_constant());
    assert_eq!(remainder.value(), Some(0));

    // 20 % 4 = 0
    let c = factory.integer(20);
    let d = factory.integer(4);
    let remainder2 = c.modulo(&d, &factory);

    assert!(remainder2.is_constant());
    assert_eq!(remainder2.value(), Some(0));
}

#[test]
fn test_constant_modulo_negative_dividend() {
    let factory = BooleanFactory::new(10, Options { bitwidth: 8, ..Default::default() });

    // -17 % 5: In Java/Rust, this is -2
    let a = factory.integer(-17);
    let b = factory.integer(5);
    let remainder = a.modulo(&b, &factory);

    assert!(remainder.is_constant());
    assert_eq!(remainder.value(), Some(-2));
}

#[test]
fn test_constant_modulo_negative_divisor() {
    let factory = BooleanFactory::new(10, Options { bitwidth: 8, ..Default::default() });

    // 17 % -5: In Java/Rust, this is 2
    let a = factory.integer(17);
    let b = factory.integer(-5);
    let remainder = a.modulo(&b, &factory);

    assert!(remainder.is_constant());
    assert_eq!(remainder.value(), Some(2));
}

#[test]
fn test_constant_modulo_both_negative() {
    let factory = BooleanFactory::new(10, Options { bitwidth: 8, ..Default::default() });

    // -17 % -5: In Java/Rust, this is -2
    let a = factory.integer(-17);
    let b = factory.integer(-5);
    let remainder = a.modulo(&b, &factory);

    assert!(remainder.is_constant());
    assert_eq!(remainder.value(), Some(-2));
}

#[test]
fn test_constant_modulo_by_one() {
    let factory = BooleanFactory::new(10, Options { bitwidth: 8, ..Default::default() });

    // Any number % 1 = 0
    let a = factory.integer(42);
    let one = factory.integer(1);
    let remainder = a.modulo(&one, &factory);

    assert!(remainder.is_constant());
    assert_eq!(remainder.value(), Some(0));

    let b = factory.integer(-17);
    let remainder2 = b.modulo(&one, &factory);

    assert!(remainder2.is_constant());
    assert_eq!(remainder2.value(), Some(0));
}

#[test]
fn test_constant_modulo_zero_dividend() {
    let factory = BooleanFactory::new(10, Options { bitwidth: 8, ..Default::default() });

    // 0 % 5 = 0
    let zero = factory.integer(0);
    let b = factory.integer(5);
    let remainder = zero.modulo(&b, &factory);

    assert!(remainder.is_constant());
    assert_eq!(remainder.value(), Some(0));
}

#[test]
fn test_constant_modulo_various_values() {
    let factory = BooleanFactory::new(10, Options { bitwidth: 16, ..Default::default() });

    let test_cases = vec![
        (17, 5, 2),
        (22, 7, 1),
        (100, 9, 1),
        (-17, 5, -2),
        (17, -5, 2),
        (-17, -5, -2),
        (15, 5, 0),
        (7, 3, 1),
    ];

    for (a_val, b_val, expected) in test_cases {
        let a = factory.integer(a_val);
        let b = factory.integer(b_val);
        let remainder = a.modulo(&b, &factory);

        assert!(remainder.is_constant(), "modulo({}, {}) should be constant", a_val, b_val);
        assert_eq!(
            remainder.value(),
            Some(expected),
            "modulo({}, {}) = {} expected, got {:?}",
            a_val,
            b_val,
            expected,
            remainder.value()
        );
    }
}

// ========== COMBINED OPERATIONS TESTS ==========

#[test]
fn test_multiply_divide_roundtrip() {
    let factory = BooleanFactory::new(10, Options { bitwidth: 16, ..Default::default() });

    // (a * b) / b = a (for non-overflowing values)
    let a = factory.integer(7);
    let b = factory.integer(5);

    let product = a.multiply(&b, &factory);
    let quotient = product.divide(&b, &factory);

    assert!(quotient.is_constant());
    assert_eq!(quotient.value(), Some(7));
}

#[test]
fn test_divide_multiply_with_remainder() {
    let factory = BooleanFactory::new(10, Options { bitwidth: 16, ..Default::default() });

    // For a / b * b + a % b = a
    let a = factory.integer(23);
    let b = factory.integer(5);

    let quotient = a.divide(&b, &factory);
    let remainder = a.modulo(&b, &factory);
    let reconstructed = quotient.multiply(&b, &factory).plus(&remainder, &factory);

    assert!(reconstructed.is_constant());
    assert_eq!(reconstructed.value(), Some(23));
}

#[test]
fn test_chain_multiply_operations() {
    let factory = BooleanFactory::new(10, Options { bitwidth: 16, ..Default::default() });

    // 2 * 3 * 4 = 24
    let a = factory.integer(2);
    let b = factory.integer(3);
    let c = factory.integer(4);

    let result = a.multiply(&b, &factory).multiply(&c, &factory);

    assert!(result.is_constant());
    assert_eq!(result.value(), Some(24));
}

