//! Tests for unsatisfiable core extraction
//!
//! Ports UCoreTest.java - validates that unsat cores are minimal and correct.
//! Following Java: kodkod.test.unit.UCoreTest

use kodkod_rs::ast::Formula;
use kodkod_rs::instance::Bounds;
use kodkod_rs::solver::{Options, Solution, Solver};

/// Helper trait for examples that can be tested for unsat cores
trait UCoreExample {
    /// Returns the check formulas for this example
    fn check_formulas(&self) -> Vec<(&'static str, Formula)>;

    /// Returns bounds for the given scope (if applicable)
    fn bounds(&self, scope: usize) -> Result<Bounds, kodkod_rs::error::KodkodError>;

    /// Returns bounds with no scope parameter (for fixed-scope examples)
    fn bounds_fixed(&self) -> Result<Bounds, kodkod_rs::error::KodkodError> {
        self.bounds(0)
    }
}

/// Verifies that a core is minimal
///
/// Following Java: UCoreTest.verify()
/// Checks:
/// 1. AND(core) is UNSAT
/// 2. Removing any single formula from core makes it SAT (minimal)
fn verify_minimal_core(core_formulas: &[Formula], bounds: &Bounds) {
    // Create a verification solver (no logging needed)
    let solver = Solver::new(Options::default());

    // 1. Check that AND(core) is UNSAT
    let core_conjunction = Formula::and_all(core_formulas.to_vec());
    let solution = solver.solve(&core_conjunction, bounds)
        .expect("Failed to solve core conjunction");
    assert!(solution.is_unsat(), "Core conjunction should be UNSAT");

    // 2. Check minimality: removing any formula should make it SAT
    for i in 0..core_formulas.len() {
        let without_i: Vec<Formula> = core_formulas.iter()
            .enumerate()
            .filter(|(idx, _)| *idx != i)
            .map(|(_, f)| f.clone())
            .collect();

        if without_i.is_empty() {
            // Single formula core - it must be necessary
            continue;
        }

        let without_conjunction = Formula::and_all(without_i);
        let solution = solver.solve(&without_conjunction, bounds)
            .expect("Failed to solve reduced core");

        assert!(
            solution.is_sat(),
            "Core is not minimal: removing formula {} still gives UNSAT",
            i
        );
    }
}

/// Minimizes and verifies a proof
///
/// Following Java: UCoreTest.minimizeAndVerify()
fn minimize_and_verify(_formula: &Formula, bounds: &Bounds, solution: Solution, core_granularity: u8) {
    // Get proof from solution
    let proof = solution.proof().expect("Solution should have a proof");

    // Note: proof.minimize() is a no-op in current Rust implementation
    // The core is already minimized during solving via deletion-based minimization
    // In Java, this would call proof.minimize(strategy)

    // Get the high-level core (translated formulas -> original formulas)
    let core_map = proof.core().expect("Proof should have a core");
    let core_formulas: Vec<Formula> = core_map.keys().cloned().collect();

    eprintln!("Core has {} formulas", core_formulas.len());

    // Verify against the bounds from the translation log
    let log_bounds = proof.log().bounds().expect("Log should have bounds");
    verify_minimal_core(&core_formulas, log_bounds);

    // For granularity 0, also verify against original bounds
    if core_granularity == 0 {
        verify_minimal_core(&core_formulas, bounds);
    }
}

/// Tests trivial proof extraction for examples at various scopes
fn test_trivial_proof_extractor(examples: &[Box<dyn UCoreExample>], max_scope: usize, core_granularity: u8) {
    let mut options = Options::default();
    options.log_translation = true;
    options.core_granularity = core_granularity;

    let solver = Solver::new(options);

    for example in examples {
        let checks = example.check_formulas();
        for (name, formula) in checks {
            for scope in 1..=max_scope {
                let bounds = example.bounds(scope).expect("Failed to create bounds");
                let solution = solver.solve(&formula, &bounds).expect("Failed to solve");

                if matches!(solution, kodkod_rs::solver::Solution::TriviallyUnsat { .. }) {
                    eprintln!("Testing trivial proof: {} scope {}", name, scope);
                    minimize_and_verify(&formula, &bounds, solution, core_granularity);
                } else {
                    // Not trivially UNSAT at this scope, try next scope
                    break;
                }
            }
        }
    }
}

/// Tests proof extraction for fixed-scope examples
fn test_trivial_proof_extractor_fixed(examples: &[Box<dyn UCoreExample>], core_granularity: u8) {
    let mut options = Options::default();
    options.log_translation = true;
    options.core_granularity = core_granularity;

    let solver = Solver::new(options);

    for example in examples {
        let checks = example.check_formulas();
        for (name, formula) in checks {
            let bounds = example.bounds_fixed().expect("Failed to create bounds");
            let solution = solver.solve(&formula, &bounds).expect("Failed to solve");

            if matches!(solution, kodkod_rs::solver::Solution::TriviallyUnsat { .. }) {
                eprintln!("Testing trivial proof (fixed): {}", name);
                minimize_and_verify(&formula, &bounds, solution, core_granularity);
            }
        }
    }
}

/// Tests non-trivial proof extraction (SAT solver UNSAT)
fn test_proof_extractor(examples: &[Box<dyn UCoreExample>], max_scope: usize, core_granularity: u8) {
    let mut options = Options::default();
    options.log_translation = true;
    options.core_granularity = core_granularity;
    options.flatten_formulas = true;  // Enable flattening for better cores

    let solver = Solver::new(options);

    for example in examples {
        let checks = example.check_formulas();
        for (name, formula) in checks {
            for scope in 1..=max_scope {
                let bounds = example.bounds(scope).expect("Failed to create bounds");
                let solution = solver.solve(&formula, &bounds).expect("Failed to solve");

                if matches!(solution, kodkod_rs::solver::Solution::Unsat { .. }) {
                    eprintln!("Testing non-trivial proof: {} scope {}", name, scope);
                    minimize_and_verify(&formula, &bounds, solution, core_granularity);
                }
            }
        }
    }
}

/// Tests non-trivial proof extraction for fixed-scope examples
fn test_proof_extractor_fixed(examples: &[Box<dyn UCoreExample>], core_granularity: u8) {
    let mut options = Options::default();
    options.log_translation = true;
    options.core_granularity = core_granularity;
    options.flatten_formulas = true;

    let solver = Solver::new(options);

    for example in examples {
        let checks = example.check_formulas();
        for (name, formula) in checks {
            let bounds = example.bounds_fixed().expect("Failed to create bounds");
            let solution = solver.solve(&formula, &bounds).expect("Failed to solve");

            if matches!(solution, kodkod_rs::solver::Solution::Unsat { .. }) {
                eprintln!("Testing non-trivial proof (fixed): {}", name);
                minimize_and_verify(&formula, &bounds, solution, core_granularity);
            }
        }
    }
}

// Example implementations for testing
mod examples {
    use super::*;
    use kodkod_rs::ast::{Decl, Decls, Expression, Relation, Variable};
    use kodkod_rs::instance::Universe;

    /// Toughnut example
    pub struct Toughnut {
        cell: Relation,
        covered: Relation,
        ord: Relation,
    }

    impl Toughnut {
        pub fn new() -> Self {
            Self {
                cell: Relation::unary("Cell"),
                covered: Relation::nary("covered", 4),
                ord: Relation::binary("ord"),
            }
        }

        fn next(&self, e: Expression) -> Expression {
            e.join(Expression::from(self.ord.clone()))
        }

        fn prev(&self, e: Expression) -> Expression {
            Expression::from(self.ord.clone()).join(e)
        }
    }

    impl UCoreExample for Toughnut {
        fn check_formulas(&self) -> Vec<(&'static str, Formula)> {
            let x = Variable::unary("x");
            let y = Variable::unary("y");
            let d = Decls::from(Decl::one_of(x.clone(), Expression::from(self.cell.clone())))
                .and(Decl::one_of(y.clone(), Expression::from(self.cell.clone())));

            let xy = Expression::from(y.clone())
                .join(Expression::from(x.clone()).join(Expression::from(self.covered.clone())));

            let symm = Formula::forall(d.clone(),
                xy.clone().product(Expression::from(x.clone()).product(Expression::from(y.clone())))
                    .in_set(Expression::from(self.covered.clone()))
            );

            let x_neighbors = self.prev(Expression::from(x.clone()))
                .union(self.next(Expression::from(x.clone())))
                .product(Expression::from(y.clone()));

            let y_neighbors = Expression::from(x.clone())
                .product(self.prev(Expression::from(y.clone()))
                    .union(self.next(Expression::from(y.clone()))));

            let covering = Formula::forall(d,
                xy.clone().one().and(xy.in_set(x_neighbors.union(y_neighbors)))
            );

            vec![("checkBelowTooDoublePrime", symm.and(covering))]
        }

        fn bounds(&self, n: usize) -> Result<Bounds, kodkod_rs::error::KodkodError> {
            assert!(n > 0);

            let atoms: Vec<String> = (0..n).map(|i| i.to_string()).collect();
            let atom_strs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
            let universe = Universe::new(&atom_strs)?;
            let factory = universe.factory();
            let mut bounds = Bounds::new(universe);

            bounds.bound_exactly(&self.cell, factory.all(1))?;

            // Ordering: linear chain 0→1→2→...→n-1
            if n > 1 {
                let mut ord_tuples = Vec::new();
                for i in 0..n-1 {
                    ord_tuples.push(vec![i.to_string(), (i+1).to_string()]);
                }
                let ord_refs: Vec<Vec<&str>> = ord_tuples.iter()
                    .map(|v| v.iter().map(|s| s.as_str()).collect())
                    .collect();
                let ord_tuple_refs: Vec<&[&str]> = ord_refs.iter().map(|v| v.as_slice()).collect();
                let ord_bound = factory.tuple_set(&ord_tuple_refs)?;
                bounds.bound_exactly(&self.ord, ord_bound)?;
            } else {
                // For n=1, ord is empty
                bounds.bound_exactly(&self.ord, factory.none(2))?;
            }

            // Board without opposite corners
            let mut board = factory.all(2);
            let corner1 = factory.tuple(&["0", "0"])?;
            board.remove(&corner1);

            if n > 1 {
                let last_idx = (n-1).to_string();
                let corner2 = factory.tuple(&[&last_idx, &last_idx])?;
                board.remove(&corner2);
            }

            // covered is 4-ary: (x, y, x', y') where x,y is covered by a domino covering x',y'
            // upper bound is board × board (all pairs of valid board positions)
            let covered_upper = board.clone().product(&board)?;
            bounds.bound(&self.covered, factory.none(4), covered_upper)?;

            Ok(bounds)
        }
    }
}

#[test]
fn test_fixed_trivial_0() {
    // Test trivial UNSAT cases with core granularity 0
    let examples: Vec<Box<dyn UCoreExample>> = vec![
        Box::new(examples::Toughnut::new()),
    ];

    test_trivial_proof_extractor(&examples, 5, 0);
}

#[test]
fn test_fixed_trivial_1() {
    // Test trivial UNSAT cases with core granularity 1
    let examples: Vec<Box<dyn UCoreExample>> = vec![
        Box::new(examples::Toughnut::new()),
    ];

    test_trivial_proof_extractor(&examples, 5, 1);
}

#[test]
fn test_easy_non_trivial_0() {
    // Test non-trivial UNSAT cases (SAT solver) with core granularity 0
    let examples: Vec<Box<dyn UCoreExample>> = vec![
        Box::new(examples::Toughnut::new()),
    ];

    test_proof_extractor(&examples, 5, 0);
}
