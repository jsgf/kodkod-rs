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
