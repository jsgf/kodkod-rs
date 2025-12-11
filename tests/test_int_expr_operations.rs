//! Integration tests for IntExpression operations through the solver
//!
//! Following Java: kodkod.test.unit.IntTest.test2sComplementBinOps()
//! Tests integer operations through the full pipeline: AST → Translation → SAT → Evaluation

use kodkod_rs::ast::IntExpression;
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

fn setup_solver(bitwidth: usize) -> (Solver, Bounds, Universe) {
    let universe = Universe::new(&["A", "B", "C", "D", "E"]).unwrap();
    let bounds = Bounds::new(universe.clone());

    let mut options = Options::default();
    options.bool_options.bitwidth = bitwidth;
    let solver = Solver::new(options);

    (solver, bounds, universe)
}

fn test_bin_op<F>(op_name: &str, a: i32, b: i32, expected: i32, mask: i32, op: F)
where
    F: Fn(IntExpression, IntExpression) -> IntExpression,
{
    let (solver, bounds, _universe) = setup_solver(8);

    let a_expr = IntExpression::constant(a);
    let b_expr = IntExpression::constant(b);
    let result_expr = op(a_expr.clone(), b_expr.clone());

    // Formula: a == a_val && b == b_val && result == expected
    let formula = a_expr.eq(IntExpression::constant(a))
        .and(b_expr.eq(IntExpression::constant(b)))
        .and(result_expr.clone().eq(IntExpression::constant(expected)));

    let solution = solver.solve(&formula, &bounds).unwrap();
    assert!(
        solution.is_sat(),
        "{} failed: {} {} {} = {} (expected {}), mask=0x{:x}",
        op_name, a, op_name, b, expected, expected & mask, mask
    );

    // Verify by evaluating the result in the solution instance
    if let Some(instance) = solution.instance() {
        let evaluator = kodkod_rs::engine::evaluator::Evaluator::new(instance);
        let actual = evaluator.evaluate_int_expression(&result_expr);
        assert_eq!(
            actual & mask,
            expected & mask,
            "{} evaluation mismatch: {} {} {} = {} (expected {} & 0x{:x} = {})",
            op_name, a, op_name, b, actual, expected, mask, expected & mask
        );
    }
}

// ========== MULTIPLY TESTS ==========

#[test]
fn test_constant_multiply_through_solver() {
    let mask = 0xFF; // 8-bit mask

    // Test various multiplication cases
    test_bin_op("multiply", 5, 3, 5 * 3, mask, |a, b| a.multiply(b));
    test_bin_op("multiply", -5, 3, -5 * 3, mask, |a, b| a.multiply(b));
    test_bin_op("multiply", 5, -3, 5 * (-3), mask, |a, b| a.multiply(b));
    test_bin_op("multiply", -5, -3, (-5) * (-3), mask, |a, b| a.multiply(b));
    test_bin_op("multiply", 0, 7, 0, mask, |a, b| a.multiply(b));
    test_bin_op("multiply", 7, 0, 0, mask, |a, b| a.multiply(b));
    test_bin_op("multiply", 1, 42, 42, mask, |a, b| a.multiply(b));
    test_bin_op("multiply", 42, 1, 42, mask, |a, b| a.multiply(b));
}

#[test]
fn test_multiply_range_constants() {
    let mask = 0xFF; // 8-bit mask

    // Test a range of values like Java IntTest
    let test_values = [-4, -3, -2, -1, 0, 1, 2, 3, 4];

    for &i in &test_values {
        for &j in &test_values {
            let expected = i * j;
            test_bin_op("multiply", i, j, expected, mask, |a, b| a.multiply(b));
        }
    }
}

#[test]
fn test_multiply_overflow() {
    let mask = 0xFF; // 8-bit mask

    // Test overflow cases
    test_bin_op("multiply", 16, 16, 16 * 16, mask, |a, b| a.multiply(b)); // 256 wraps to 0
    test_bin_op("multiply", 20, 10, 20 * 10, mask, |a, b| a.multiply(b)); // 200 wraps to -56
}

// ========== DIVIDE TESTS ==========

#[test]
fn test_constant_divide_through_solver() {
    let mask = 0xFF; // 8-bit mask

    // Test various division cases
    test_bin_op("divide", 15, 3, 15 / 3, mask, |a, b| a.divide(b));
    test_bin_op("divide", 20, 4, 20 / 4, mask, |a, b| a.divide(b));
    test_bin_op("divide", -15, 3, -15 / 3, mask, |a, b| a.divide(b));
    test_bin_op("divide", 15, -3, 15 / (-3), mask, |a, b| a.divide(b));
    test_bin_op("divide", -15, -3, (-15) / (-3), mask, |a, b| a.divide(b));
    test_bin_op("divide", 17, 5, 17 / 5, mask, |a, b| a.divide(b)); // with remainder
    test_bin_op("divide", 42, 1, 42 / 1, mask, |a, b| a.divide(b));
    test_bin_op("divide", 0, 5, 0 / 5, mask, |a, b| a.divide(b));
}

#[test]
fn test_divide_range_constants() {
    let mask = 0xFF; // 8-bit mask

    // Test a range of values like Java IntTest
    let test_values = [-4, -3, -2, -1, 1, 2, 3, 4]; // exclude 0 divisor

    for &i in &[-8, -4, -2, 0, 2, 4, 8] {
        for &j in &test_values {
            let expected = i / j;
            test_bin_op("divide", i, j, expected, mask, |a, b| a.divide(b));
        }
    }
}

// ========== MODULO TESTS ==========

#[test]
fn test_constant_modulo_through_solver() {
    let mask = 0xFF; // 8-bit mask

    // Test various modulo cases
    test_bin_op("modulo", 17, 5, 17 % 5, mask, |a, b| a.modulo(b));
    test_bin_op("modulo", 22, 7, 22 % 7, mask, |a, b| a.modulo(b));
    test_bin_op("modulo", -17, 5, -17 % 5, mask, |a, b| a.modulo(b));
    test_bin_op("modulo", 17, -5, 17 % (-5), mask, |a, b| a.modulo(b));
    test_bin_op("modulo", -17, -5, (-17) % (-5), mask, |a, b| a.modulo(b));
    test_bin_op("modulo", 15, 5, 15 % 5, mask, |a, b| a.modulo(b)); // exact division -> 0
    test_bin_op("modulo", 42, 1, 42 % 1, mask, |a, b| a.modulo(b));
    test_bin_op("modulo", 0, 5, 0 % 5, mask, |a, b| a.modulo(b));
}

#[test]
fn test_modulo_range_constants() {
    let mask = 0xFF; // 8-bit mask

    // Test a range of values like Java IntTest
    let test_values = [-4, -3, -2, -1, 1, 2, 3, 4]; // exclude 0 divisor

    for &i in &[-8, -4, -2, 0, 2, 4, 8] {
        for &j in &test_values {
            let expected = i % j;
            test_bin_op("modulo", i, j, expected, mask, |a, b| a.modulo(b));
        }
    }
}

// ========== COMBINED OPERATIONS ==========

#[test]
fn test_multiply_divide_combined() {
    let (solver, bounds, _universe) = setup_solver(16);

    // Test: (a * b) / b == a (for values that don't overflow)
    let a = IntExpression::constant(7);
    let b = IntExpression::constant(5);

    let product = a.clone().multiply(b.clone());
    let quotient = product.divide(b.clone());

    let formula = quotient.eq(a.clone());

    let solution = solver.solve(&formula, &bounds).unwrap();
    assert!(solution.is_sat(), "(a * b) / b == a should be SAT");
}

#[test]
fn test_divide_modulo_reconstruction() {
    let (solver, bounds, _universe) = setup_solver(16);

    // Test: (a / b) * b + (a % b) == a
    let a = IntExpression::constant(23);
    let b = IntExpression::constant(5);

    let quotient = a.clone().divide(b.clone());
    let remainder = a.clone().modulo(b.clone());
    let reconstructed = quotient.multiply(b).plus(remainder);

    let formula = reconstructed.eq(a.clone());

    let solution = solver.solve(&formula, &bounds).unwrap();
    assert!(solution.is_sat(), "(a / b) * b + (a % b) == a should be SAT");
}

#[test]
fn test_multiply_associative() {
    let (solver, bounds, _universe) = setup_solver(16);

    // Test: (a * b) * c == a * (b * c)
    let a = IntExpression::constant(2);
    let b = IntExpression::constant(3);
    let c = IntExpression::constant(4);

    let left = a.clone().multiply(b.clone()).multiply(c.clone());
    let right = a.clone().multiply(b.clone().multiply(c.clone()));

    let formula = left.eq(right);

    let solution = solver.solve(&formula, &bounds).unwrap();
    assert!(solution.is_sat(), "multiply should be associative");
}

#[test]
fn test_multiply_commutative() {
    let (solver, bounds, _universe) = setup_solver(16);

    // Test: a * b == b * a
    let a = IntExpression::constant(7);
    let b = IntExpression::constant(13);

    let left = a.clone().multiply(b.clone());
    let right = b.clone().multiply(a.clone());

    let formula = left.eq(right);

    let solution = solver.solve(&formula, &bounds).unwrap();
    assert!(solution.is_sat(), "multiply should be commutative");
}
