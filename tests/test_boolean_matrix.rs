//! Comprehensive unit tests for BooleanMatrix operations
//!
//! Each complex API function must have tests that exercise:
//! 1. Basic functionality with simple inputs
//! 2. Edge cases (empty matrices, single elements)
//! 3. Invariant properties (e.g., A transpose transpose = A)
//! 4. Correctness assertions that fail if implementation is wrong

use kodkod_rs::bool::{BooleanMatrix, BooleanFactory, Dimensions, BoolValue, BooleanConstant, Options};

#[test]
fn test_transpose_binary_relation_simple() {
    let dims = Dimensions::new(4, 2);
    let mut factory = BooleanFactory::new(2, Options::default());
    let mut matrix = BooleanMatrix::empty(dims);

    let val_true = BoolValue::Constant(BooleanConstant::TRUE);
    matrix.set(1, val_true.clone());
    matrix.set(2, val_true.clone());

    let transposed = matrix.transpose(&mut factory);

    assert_eq!(transposed.dimensions().capacity(), matrix.dimensions().capacity());
    assert_eq!(transposed.dimensions().arity(), matrix.dimensions().arity());
    assert_eq!(transposed.get(1), BoolValue::Constant(BooleanConstant::TRUE));
    assert_eq!(transposed.get(2), BoolValue::Constant(BooleanConstant::TRUE));
}

#[test]
fn test_transpose_binary_relation_asymmetric() {
    let dims = Dimensions::new(9, 2);
    let mut factory = BooleanFactory::new(3, Options::default());
    let mut matrix = BooleanMatrix::empty(dims);

    let val_true = BoolValue::Constant(BooleanConstant::TRUE);
    matrix.set(1, val_true.clone());

    let transposed = matrix.transpose(&mut factory);

    let val_10 = transposed.get(3);
    assert_eq!(val_10, BoolValue::Constant(BooleanConstant::TRUE));

    let val_01 = transposed.get(1);
    assert_eq!(val_01, BoolValue::Constant(BooleanConstant::FALSE));
}

#[test]
fn test_transpose_preserves_dimensions() {
    let dims = Dimensions::new(16, 2);
    let mut factory = BooleanFactory::new(4, Options::default());
    let matrix = BooleanMatrix::empty(dims);

    let transposed = matrix.transpose(&mut factory);

    assert_eq!(transposed.dimensions().capacity(), matrix.dimensions().capacity());
    assert_eq!(transposed.dimensions().arity(), matrix.dimensions().arity());
}

#[test]
fn test_transpose_double_transpose_identity() {
    let dims = Dimensions::new(9, 2);
    let mut factory = BooleanFactory::new(3, Options::default());
    let mut matrix = BooleanMatrix::empty(dims);

    let val_true = BoolValue::Constant(BooleanConstant::TRUE);
    matrix.set(1, val_true.clone());
    matrix.set(4, val_true.clone());
    matrix.set(7, val_true.clone());

    let transposed_once = matrix.transpose(&mut factory);
    let transposed_twice = transposed_once.transpose(&mut factory);

    assert_eq!(transposed_twice.get(1), matrix.get(1));
    assert_eq!(transposed_twice.get(4), matrix.get(4));
    assert_eq!(transposed_twice.get(7), matrix.get(7));
}

#[test]
fn test_transpose_empty_relation() {
    let dims = Dimensions::new(4, 2);
    let mut factory = BooleanFactory::new(2, Options::default());
    let matrix = BooleanMatrix::empty(dims);

    let transposed = matrix.transpose(&mut factory);

    for i in 0..4 {
        assert_eq!(transposed.get(i), BoolValue::Constant(BooleanConstant::FALSE));
    }
}

#[test]
fn test_equals_same_matrix() {
    let dims = Dimensions::new(4, 2);
    let mut factory = BooleanFactory::new(2, Options::default());
    let mut matrix = BooleanMatrix::empty(dims);

    let val_true = BoolValue::Constant(BooleanConstant::TRUE);
    matrix.set(1, val_true.clone());
    matrix.set(2, val_true.clone());

    let result = matrix.equals(&matrix, &mut factory);
    assert_eq!(result, BoolValue::Constant(BooleanConstant::TRUE));
}

#[test]
fn test_equals_different_matrices() {
    let dims = Dimensions::new(4, 2);
    let mut factory = BooleanFactory::new(2, Options::default());

    let mut matrix1 = BooleanMatrix::empty(dims);
    let mut matrix2 = BooleanMatrix::empty(dims);

    let val_true = BoolValue::Constant(BooleanConstant::TRUE);
    matrix1.set(1, val_true.clone());
    matrix2.set(2, val_true.clone());

    let result = matrix1.equals(&matrix2, &mut factory);
    assert_ne!(result, BoolValue::Constant(BooleanConstant::TRUE));
}

#[test]
fn test_equals_transposed_symmetric() {
    let dims = Dimensions::new(9, 2);
    let mut factory = BooleanFactory::new(3, Options::default());

    let mut matrix = BooleanMatrix::empty(dims);
    let val_true = BoolValue::Constant(BooleanConstant::TRUE);

    matrix.set(1, val_true.clone());
    matrix.set(3, val_true.clone());

    let transposed = matrix.transpose(&mut factory);
    let result = matrix.equals(&transposed, &mut factory);

    assert_eq!(result, BoolValue::Constant(BooleanConstant::TRUE));
}

#[test]
fn test_union_simple() {
    let dims = Dimensions::new(4, 2);
    let mut factory = BooleanFactory::new(2, Options::default());

    let mut matrix1 = BooleanMatrix::empty(dims);
    let mut matrix2 = BooleanMatrix::empty(dims);

    let val_true = BoolValue::Constant(BooleanConstant::TRUE);
    matrix1.set(1, val_true.clone());
    matrix2.set(2, val_true.clone());

    let union = matrix1.union(&matrix2, &mut factory);

    assert_eq!(union.get(1), BoolValue::Constant(BooleanConstant::TRUE));
    assert_eq!(union.get(2), BoolValue::Constant(BooleanConstant::TRUE));
}

#[test]
fn test_intersection_simple() {
    let dims = Dimensions::new(4, 2);
    let mut factory = BooleanFactory::new(2, Options::default());

    let mut matrix1 = BooleanMatrix::empty(dims);
    let mut matrix2 = BooleanMatrix::empty(dims);

    let val_true = BoolValue::Constant(BooleanConstant::TRUE);
    matrix1.set(1, val_true.clone());
    matrix1.set(2, val_true.clone());
    matrix2.set(2, val_true.clone());
    matrix2.set(3, val_true.clone());

    let intersection = matrix1.intersection(&matrix2, &mut factory);

    assert_eq!(intersection.get(2), BoolValue::Constant(BooleanConstant::TRUE));
    assert_eq!(intersection.get(1), BoolValue::Constant(BooleanConstant::FALSE));
}

#[test]
fn test_difference_simple() {
    let dims = Dimensions::new(4, 2);
    let mut factory = BooleanFactory::new(2, Options::default());

    let mut matrix1 = BooleanMatrix::empty(dims);
    let mut matrix2 = BooleanMatrix::empty(dims);

    let val_true = BoolValue::Constant(BooleanConstant::TRUE);
    matrix1.set(1, val_true.clone());
    matrix1.set(2, val_true.clone());
    matrix2.set(2, val_true.clone());

    let diff = matrix1.difference(&matrix2, &mut factory);

    assert_eq!(diff.get(1), BoolValue::Constant(BooleanConstant::TRUE));
    assert_eq!(diff.get(2), BoolValue::Constant(BooleanConstant::FALSE));
}

#[test]
fn test_closure_reflexive_property() {
    let dims = Dimensions::new(9, 2);
    let mut factory = BooleanFactory::new(3, Options::default());

    let mut matrix = BooleanMatrix::empty(dims);
    let val_true = BoolValue::Constant(BooleanConstant::TRUE);
    matrix.set(1, val_true.clone());

    let closed = matrix.closure(&mut factory);

    assert_eq!(closed.get(1), BoolValue::Constant(BooleanConstant::TRUE));
}

#[test]
fn test_product_dimensions() {
    let dims = Dimensions::new(4, 2);
    let mut factory = BooleanFactory::new(2, Options::default());
    let matrix = BooleanMatrix::empty(dims);

    let product = matrix.product(&matrix, &mut factory);

    assert_eq!(product.dimensions().arity(), 4);
    assert_eq!(product.dimensions().capacity(), 16);
}

#[test]
#[should_panic(expected = "transpose only works on binary relations")]
fn test_transpose_non_binary_panics() {
    let dims = Dimensions::new(8, 3);
    let mut factory = BooleanFactory::new(2, Options::default());
    let matrix = BooleanMatrix::empty(dims);

    let _ = matrix.transpose(&mut factory);
}
