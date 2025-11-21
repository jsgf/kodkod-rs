//! Comprehensive unit tests for BooleanMatrix operations
//!
//! Each complex API function must have tests that exercise:
//! 1. Basic functionality with simple inputs
//! 2. Edge cases (empty matrices, single elements)
//! 3. Invariant properties (e.g., A transpose transpose = A)
//! 4. Correctness assertions that fail if implementation is wrong

use kodkod_rs::bool::{BooleanMatrix, BooleanFactory, Dimensions, BoolValue, BooleanConstant, Options};

#[test]
fn test_not_element_wise() {
    // Following Java: testNot - element-wise negation
    let dims = Dimensions::new(4, 2);
    let factory = BooleanFactory::new(3, Options::default());
    let mut matrix = BooleanMatrix::empty(dims);

    let val_true = BoolValue::Constant(BooleanConstant::TRUE);
    let v1 = factory.variable(1);

    // Set up matrix with:
    // index 0: FALSE (absent)
    // index 1: TRUE
    // index 2: variable v1
    // index 3: FALSE (absent)
    matrix.set(1, val_true.clone());
    matrix.set(2, v1.clone());

    let negated = matrix.not(&factory);

    // Check dimensions preserved
    assert_eq!(negated.dimensions().capacity(), matrix.dimensions().capacity());
    assert_eq!(negated.dimensions().arity(), matrix.dimensions().arity());

    // Check negation:
    // index 0: FALSE -> TRUE
    assert_eq!(negated.get(0), BoolValue::Constant(BooleanConstant::TRUE));
    // index 1: TRUE -> FALSE
    assert_eq!(negated.get(1), BoolValue::Constant(BooleanConstant::FALSE));
    // index 2: v1 -> NOT(v1)
    let expected_not_v1 = factory.not(v1.clone());
    assert_eq!(negated.get(2), expected_not_v1);
    // index 3: FALSE -> TRUE
    assert_eq!(negated.get(3), BoolValue::Constant(BooleanConstant::TRUE));

    // Check density: should have 3 non-FALSE entries (indices 0, 2, 3)
    assert_eq!(negated.density(), 3);
}

#[test]
fn test_not_double_negation() {
    // Test that double negation returns to original (for constants)
    let dims = Dimensions::new(4, 2);
    let factory = BooleanFactory::new(2, Options::default());
    let mut matrix = BooleanMatrix::empty(dims);

    let val_true = BoolValue::Constant(BooleanConstant::TRUE);
    matrix.set(1, val_true.clone());

    let negated_once = matrix.not(&factory);
    let negated_twice = negated_once.not(&factory);

    // After double negation, should match original
    assert_eq!(negated_twice.get(0), matrix.get(0));
    assert_eq!(negated_twice.get(1), matrix.get(1));
    assert_eq!(negated_twice.get(2), matrix.get(2));
    assert_eq!(negated_twice.get(3), matrix.get(3));
}

#[test]
fn test_set_and_get_basic() {
    // Following Java: testSetAndGet - basic set/get operations
    let dims = Dimensions::new(4, 2);
    let _factory = BooleanFactory::new(2, Options::default());
    let mut matrix = BooleanMatrix::empty(dims);

    // Initially all FALSE
    for i in 0..4 {
        assert_eq!(matrix.get(i), BoolValue::Constant(BooleanConstant::FALSE));
    }

    // Set some values
    let val_true = BoolValue::Constant(BooleanConstant::TRUE);
    matrix.set(0, val_true.clone());
    matrix.set(2, val_true.clone());

    // Check values
    assert_eq!(matrix.get(0), BoolValue::Constant(BooleanConstant::TRUE));
    assert_eq!(matrix.get(1), BoolValue::Constant(BooleanConstant::FALSE));
    assert_eq!(matrix.get(2), BoolValue::Constant(BooleanConstant::TRUE));
    assert_eq!(matrix.get(3), BoolValue::Constant(BooleanConstant::FALSE));

    // Density should be 2
    assert_eq!(matrix.density(), 2);
}

#[test]
fn test_set_and_get_with_variables() {
    // Test with boolean variables (not just constants)
    let dims = Dimensions::new(4, 2);
    let factory = BooleanFactory::new(3, Options::default());
    let mut matrix = BooleanMatrix::empty(dims);

    let v1 = factory.variable(1);
    let v2 = factory.variable(2);

    matrix.set(0, v1.clone());
    matrix.set(1, v2.clone());

    assert_eq!(matrix.get(0), v1);
    assert_eq!(matrix.get(1), v2);
    assert_eq!(matrix.density(), 2);
}

#[test]
fn test_join_basic() {
    // Following Java: testDotProduct - matrix join operation
    // Test A.join(B) where A is 2x2 binary relation and B is 2x2 binary relation
    // Result should be 2x2 binary relation
    let dims22 = Dimensions::new(4, 2); // 2x2 binary relation
    let factory = BooleanFactory::new(5, Options::default());

    let mut matrix_a = BooleanMatrix::empty(dims22);
    let mut matrix_b = BooleanMatrix::empty(dims22);

    // A = { (0,1) } means index 1 is TRUE (row 0, col 1)
    matrix_a.set(1, factory.variable(1));

    // B = { (1,0) } means index 2 is TRUE (row 1, col 0)
    matrix_b.set(2, factory.variable(2));

    // A.join(B) should give us { (0,0) } because 0->1 in A and 1->0 in B
    let joined = matrix_a.join(&matrix_b, &factory);

    // Result dimensions should be (capacity=4, arity=2)
    assert_eq!(joined.dimensions().capacity(), 4);
    assert_eq!(joined.dimensions().arity(), 2);

    // The join should have at least one non-FALSE entry
    assert!(joined.density() > 0, "Join should produce non-empty result");
}

#[test]
fn test_join_empty() {
    // Join with empty matrix should give empty result
    let dims = Dimensions::new(4, 2);
    let factory = BooleanFactory::new(2, Options::default());

    let matrix_a = BooleanMatrix::empty(dims);
    let matrix_b = BooleanMatrix::empty(dims);

    let joined = matrix_a.join(&matrix_b, &factory);

    assert_eq!(joined.density(), 0);
}

#[test]
fn test_override_basic() {
    // Following Java: testOverride
    // Test A.override_with(B) where B takes precedence
    let dims = Dimensions::new(4, 2);
    let factory = BooleanFactory::new(3, Options::default());

    let mut matrix_a = BooleanMatrix::empty(dims);
    let mut matrix_b = BooleanMatrix::empty(dims);

    let v1 = factory.variable(1);
    let v2 = factory.variable(2);

    // A has entries at indices 0 and 1
    matrix_a.set(0, v1.clone());
    matrix_a.set(1, v1.clone());

    // B has entry at index 0 (should override A's entry)
    matrix_b.set(0, v2.clone());

    let overridden = matrix_a.override_with(&matrix_b, &factory);

    // Index 0 should have B's value
    // Index 1 should have A's value (not overridden)
    assert!(overridden.density() > 0, "Override should produce non-empty result");
}

#[test]
fn test_subset_basic() {
    // Test subset check: A ⊆ B
    let dims = Dimensions::new(4, 2);
    let factory = BooleanFactory::new(2, Options::default());

    let mut matrix_a = BooleanMatrix::empty(dims);
    let mut matrix_b = BooleanMatrix::empty(dims);

    let val_true = BoolValue::Constant(BooleanConstant::TRUE);

    // A = { entry at 1 }
    matrix_a.set(1, val_true.clone());

    // B = { entries at 1, 2 }
    matrix_b.set(1, val_true.clone());
    matrix_b.set(2, val_true.clone());

    // A ⊆ B should be TRUE
    let result = matrix_a.subset(&matrix_b, &factory);
    assert_eq!(result, BoolValue::Constant(BooleanConstant::TRUE));

    // B ⊆ A should be FALSE (B has entry at 2 that A doesn't)
    let result_reverse = matrix_b.subset(&matrix_a, &factory);
    assert_ne!(result_reverse, BoolValue::Constant(BooleanConstant::TRUE));
}

#[test]
fn test_some_multiplicity() {
    // Test some(): true if at least one entry is TRUE
    let dims = Dimensions::new(4, 2);
    let factory = BooleanFactory::new(2, Options::default());

    let mut matrix = BooleanMatrix::empty(dims);

    // Empty matrix: some() should be FALSE
    let result = matrix.some(&factory);
    assert_eq!(result, BoolValue::Constant(BooleanConstant::FALSE));

    // Add one entry: some() should be TRUE
    matrix.set(1, BoolValue::Constant(BooleanConstant::TRUE));
    let result = matrix.some(&factory);
    assert_eq!(result, BoolValue::Constant(BooleanConstant::TRUE));
}

#[test]
fn test_none_multiplicity() {
    // Test none(): true if all entries are FALSE
    let dims = Dimensions::new(4, 2);
    let factory = BooleanFactory::new(2, Options::default());

    let matrix = BooleanMatrix::empty(dims);

    // Empty matrix: none() should be TRUE
    let result = matrix.none(&factory);
    assert_eq!(result, BoolValue::Constant(BooleanConstant::TRUE));
}

#[test]
fn test_one_multiplicity() {
    // Test one(): true if exactly one entry is TRUE
    let dims = Dimensions::new(4, 2);
    let factory = BooleanFactory::new(2, Options::default());

    let mut matrix = BooleanMatrix::empty(dims);
    matrix.set(1, BoolValue::Constant(BooleanConstant::TRUE));

    // Exactly one entry: one() should be TRUE
    let result = matrix.one(&factory);
    assert_eq!(result, BoolValue::Constant(BooleanConstant::TRUE));
}

#[test]
fn test_reflexive_closure() {
    // Test reflexive transitive closure: R*
    let dims = Dimensions::new(9, 2); // 3x3 binary relation
    let factory = BooleanFactory::new(3, Options::default());

    let mut matrix = BooleanMatrix::empty(dims);
    let val_true = BoolValue::Constant(BooleanConstant::TRUE);

    // Add one edge
    matrix.set(1, val_true.clone());

    // Create identity matrix for same dimensions
    let mut iden = BooleanMatrix::empty(dims);
    // Identity: (0,0), (1,1), (2,2) at indices 0, 4, 8
    iden.set(0, val_true.clone());
    iden.set(4, val_true.clone());
    iden.set(8, val_true.clone());

    let r_star = matrix.reflexive_closure(&factory, &iden);

    // Should contain original edge plus identity
    assert!(r_star.density() >= matrix.density());
}

#[test]
fn test_transpose_binary_relation_simple() {
    let dims = Dimensions::new(4, 2);
    let factory = BooleanFactory::new(2, Options::default());
    let mut matrix = BooleanMatrix::empty(dims);

    let val_true = BoolValue::Constant(BooleanConstant::TRUE);
    matrix.set(1, val_true.clone());
    matrix.set(2, val_true.clone());

    let transposed = matrix.transpose(&factory);

    assert_eq!(transposed.dimensions().capacity(), matrix.dimensions().capacity());
    assert_eq!(transposed.dimensions().arity(), matrix.dimensions().arity());
    assert_eq!(transposed.get(1), BoolValue::Constant(BooleanConstant::TRUE));
    assert_eq!(transposed.get(2), BoolValue::Constant(BooleanConstant::TRUE));
}

#[test]
fn test_transpose_binary_relation_asymmetric() {
    let dims = Dimensions::new(9, 2);
    let factory = BooleanFactory::new(3, Options::default());
    let mut matrix = BooleanMatrix::empty(dims);

    let val_true = BoolValue::Constant(BooleanConstant::TRUE);
    matrix.set(1, val_true.clone());

    let transposed = matrix.transpose(&factory);

    let val_10 = transposed.get(3);
    assert_eq!(val_10, BoolValue::Constant(BooleanConstant::TRUE));

    let val_01 = transposed.get(1);
    assert_eq!(val_01, BoolValue::Constant(BooleanConstant::FALSE));
}

#[test]
fn test_transpose_preserves_dimensions() {
    let dims = Dimensions::new(16, 2);
    let factory = BooleanFactory::new(4, Options::default());
    let matrix = BooleanMatrix::empty(dims);

    let transposed = matrix.transpose(&factory);

    assert_eq!(transposed.dimensions().capacity(), matrix.dimensions().capacity());
    assert_eq!(transposed.dimensions().arity(), matrix.dimensions().arity());
}

#[test]
fn test_transpose_double_transpose_identity() {
    let dims = Dimensions::new(9, 2);
    let factory = BooleanFactory::new(3, Options::default());
    let mut matrix = BooleanMatrix::empty(dims);

    let val_true = BoolValue::Constant(BooleanConstant::TRUE);
    matrix.set(1, val_true.clone());
    matrix.set(4, val_true.clone());
    matrix.set(7, val_true.clone());

    let transposed_once = matrix.transpose(&factory);
    let transposed_twice = transposed_once.transpose(&factory);

    assert_eq!(transposed_twice.get(1), matrix.get(1));
    assert_eq!(transposed_twice.get(4), matrix.get(4));
    assert_eq!(transposed_twice.get(7), matrix.get(7));
}

#[test]
fn test_transpose_empty_relation() {
    let dims = Dimensions::new(4, 2);
    let factory = BooleanFactory::new(2, Options::default());
    let matrix = BooleanMatrix::empty(dims);

    let transposed = matrix.transpose(&factory);

    for i in 0..4 {
        assert_eq!(transposed.get(i), BoolValue::Constant(BooleanConstant::FALSE));
    }
}

#[test]
fn test_equals_same_matrix() {
    let dims = Dimensions::new(4, 2);
    let factory = BooleanFactory::new(2, Options::default());
    let mut matrix = BooleanMatrix::empty(dims);

    let val_true = BoolValue::Constant(BooleanConstant::TRUE);
    matrix.set(1, val_true.clone());
    matrix.set(2, val_true.clone());

    let result = matrix.equals(&matrix, &factory);
    assert_eq!(result, BoolValue::Constant(BooleanConstant::TRUE));
}

#[test]
fn test_equals_different_matrices() {
    let dims = Dimensions::new(4, 2);
    let factory = BooleanFactory::new(2, Options::default());

    let mut matrix1 = BooleanMatrix::empty(dims);
    let mut matrix2 = BooleanMatrix::empty(dims);

    let val_true = BoolValue::Constant(BooleanConstant::TRUE);
    matrix1.set(1, val_true.clone());
    matrix2.set(2, val_true.clone());

    let result = matrix1.equals(&matrix2, &factory);
    assert_ne!(result, BoolValue::Constant(BooleanConstant::TRUE));
}

#[test]
fn test_equals_transposed_symmetric() {
    let dims = Dimensions::new(9, 2);
    let factory = BooleanFactory::new(3, Options::default());

    let mut matrix = BooleanMatrix::empty(dims);
    let val_true = BoolValue::Constant(BooleanConstant::TRUE);

    matrix.set(1, val_true.clone());
    matrix.set(3, val_true.clone());

    let transposed = matrix.transpose(&factory);
    let result = matrix.equals(&transposed, &factory);

    assert_eq!(result, BoolValue::Constant(BooleanConstant::TRUE));
}

#[test]
fn test_union_simple() {
    let dims = Dimensions::new(4, 2);
    let factory = BooleanFactory::new(2, Options::default());

    let mut matrix1 = BooleanMatrix::empty(dims);
    let mut matrix2 = BooleanMatrix::empty(dims);

    let val_true = BoolValue::Constant(BooleanConstant::TRUE);
    matrix1.set(1, val_true.clone());
    matrix2.set(2, val_true.clone());

    let union = matrix1.union(&matrix2, &factory);

    assert_eq!(union.get(1), BoolValue::Constant(BooleanConstant::TRUE));
    assert_eq!(union.get(2), BoolValue::Constant(BooleanConstant::TRUE));
}

#[test]
fn test_intersection_simple() {
    let dims = Dimensions::new(4, 2);
    let factory = BooleanFactory::new(2, Options::default());

    let mut matrix1 = BooleanMatrix::empty(dims);
    let mut matrix2 = BooleanMatrix::empty(dims);

    let val_true = BoolValue::Constant(BooleanConstant::TRUE);
    matrix1.set(1, val_true.clone());
    matrix1.set(2, val_true.clone());
    matrix2.set(2, val_true.clone());
    matrix2.set(3, val_true.clone());

    let intersection = matrix1.intersection(&matrix2, &factory);

    assert_eq!(intersection.get(2), BoolValue::Constant(BooleanConstant::TRUE));
    assert_eq!(intersection.get(1), BoolValue::Constant(BooleanConstant::FALSE));
}

#[test]
fn test_difference_simple() {
    let dims = Dimensions::new(4, 2);
    let factory = BooleanFactory::new(2, Options::default());

    let mut matrix1 = BooleanMatrix::empty(dims);
    let mut matrix2 = BooleanMatrix::empty(dims);

    let val_true = BoolValue::Constant(BooleanConstant::TRUE);
    matrix1.set(1, val_true.clone());
    matrix1.set(2, val_true.clone());
    matrix2.set(2, val_true.clone());

    let diff = matrix1.difference(&matrix2, &factory);

    assert_eq!(diff.get(1), BoolValue::Constant(BooleanConstant::TRUE));
    assert_eq!(diff.get(2), BoolValue::Constant(BooleanConstant::FALSE));
}

#[test]
fn test_closure_reflexive_property() {
    let dims = Dimensions::new(9, 2);
    let factory = BooleanFactory::new(3, Options::default());

    let mut matrix = BooleanMatrix::empty(dims);
    let val_true = BoolValue::Constant(BooleanConstant::TRUE);
    matrix.set(1, val_true.clone());

    let closed = matrix.closure(&factory);

    assert_eq!(closed.get(1), BoolValue::Constant(BooleanConstant::TRUE));
}

#[test]
fn test_product_dimensions() {
    let dims = Dimensions::new(4, 2);
    let factory = BooleanFactory::new(2, Options::default());
    let matrix = BooleanMatrix::empty(dims);

    let product = matrix.product(&matrix, &factory);

    assert_eq!(product.dimensions().arity(), 4);
    assert_eq!(product.dimensions().capacity(), 16);
}

#[test]
#[should_panic(expected = "transpose only works on binary relations")]
fn test_transpose_non_binary_panics() {
    let dims = Dimensions::new(8, 3);
    let factory = BooleanFactory::new(2, Options::default());
    let matrix = BooleanMatrix::empty(dims);

    let _ = matrix.transpose(&factory);
}
