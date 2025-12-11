//! SAT solver trait and implementations

pub mod rustsat_adapter;
pub mod symmetry_detector;
pub mod symmetry_breaker;
pub mod evaluator;

pub use symmetry_detector::SymmetryDetector;
pub use symmetry_breaker::SymmetryBreaker;
pub use evaluator::Evaluator;

/// Core SAT solver trait
///
/// This trait defines the interface that all SAT solver backends must implement.
/// Variables are 1-indexed, and literals are represented as signed integers
/// (positive for true, negative for false).
pub trait SATSolver {
    /// Adds the given number of variables to the solver
    fn add_variables(&mut self, num_vars: u32);

    /// Adds a clause to the solver
    ///
    /// Returns false if the clause is trivially unsatisfiable
    ///
    /// # Arguments
    /// * `lits` - Slice of literals (1-indexed, negated by sign)
    fn add_clause(&mut self, lits: &[i32]) -> bool;

    /// Solves the current formula
    ///
    /// Returns true if satisfiable, false if unsatisfiable
    fn solve(&mut self) -> bool;

    /// Solves the current formula with assumptions
    ///
    /// Returns true if satisfiable under the given assumptions, false if unsatisfiable.
    /// When UNSAT, the core can be retrieved via unsat_core().
    ///
    /// # Arguments
    /// * `assumptions` - Literals that must be true (1-indexed, negated by sign)
    fn solve_with_assumptions(&mut self, assumptions: &[i32]) -> bool;

    /// Gets the unsat core after an UNSAT solve with assumptions
    ///
    /// Returns the subset of assumptions that caused the UNSAT.
    /// Only valid after solve_with_assumptions() returns false.
    fn unsat_core(&mut self) -> Vec<i32>;

    /// Returns the assignment of a variable in the solution
    ///
    /// Only valid after solve() returns true.
    /// Variables are 1-indexed.
    fn value_of(&self, var: u32) -> bool;

    /// Returns the number of variables in the solver
    fn num_variables(&self) -> u32;

    /// Returns the number of clauses added
    fn num_clauses(&self) -> u32;
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::rustsat_adapter::RustSatAdapter;
    use rustsat_batsat::BasicSolver;

    #[test]
    fn batsat_basic_sat() {
        let mut solver = RustSatAdapter::new(BasicSolver::default());
        solver.add_variables(3);

        // (x1 ∨ x2) ∧ (¬x1 ∨ x3)
        solver.add_clause(&[1, 2]);
        solver.add_clause(&[-1, 3]);

        assert!(solver.solve());
    }

    #[test]
    fn batsat_basic_unsat() {
        let mut solver = RustSatAdapter::new(BasicSolver::default());
        solver.add_variables(1);

        // x1 ∧ ¬x1
        solver.add_clause(&[1]);
        solver.add_clause(&[-1]);

        assert!(!solver.solve());
    }

    #[test]
    fn batsat_value() {
        let mut solver = RustSatAdapter::new(BasicSolver::default());
        solver.add_variables(2);

        // x1 must be true, x2 must be false
        solver.add_clause(&[1]);
        solver.add_clause(&[-2]);

        assert!(solver.solve());
        assert!(solver.value_of(1));
        assert!(!solver.value_of(2));
    }
}
