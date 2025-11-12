//! SAT solver trait and implementations

#[cfg(test)]
pub mod rustsat_adapter;

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

/// Extension for solvers that support UNSAT core extraction
pub trait SATProver: SATSolver {
    /// Extracts an unsatisfiable core after solve() returns false
    ///
    /// Returns indices of clauses in the core
    fn unsat_core(&self) -> Vec<usize>;
}

/// A simple mock SAT solver for testing
///
/// This solver doesn't actually solve anything - it just tracks
/// variables and clauses. Useful for testing the translation pipeline.
pub struct MockSolver {
    num_vars: u32,
    clauses: Vec<Vec<i32>>,
    solution: Vec<bool>,
}

impl MockSolver {
    /// Creates a new mock solver
    pub fn new() -> Self {
        Self {
            num_vars: 0,
            clauses: Vec::new(),
            solution: Vec::new(),
        }
    }
}

impl Default for MockSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl SATSolver for MockSolver {
    fn add_variables(&mut self, num_vars: u32) {
        self.num_vars += num_vars;
        // Initialize solution to all false
        for _ in 0..num_vars {
            self.solution.push(false);
        }
    }

    fn add_clause(&mut self, lits: &[i32]) -> bool {
        self.clauses.push(lits.to_vec());
        true // Assume not trivially unsat
    }

    fn solve(&mut self) -> bool {
        // Mock implementation: return true if we have variables
        self.num_vars > 0
    }

    fn value_of(&self, var: u32) -> bool {
        if var == 0 || var > self.num_vars {
            false
        } else {
            self.solution[(var - 1) as usize]
        }
    }

    fn num_variables(&self) -> u32 {
        self.num_vars
    }

    fn num_clauses(&self) -> u32 {
        self.clauses.len() as u32
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mock_solver_basic() {
        let mut solver = MockSolver::new();

        solver.add_variables(3);
        assert_eq!(solver.num_variables(), 3);

        solver.add_clause(&[1, 2]);
        solver.add_clause(&[-1, 3]);
        assert_eq!(solver.num_clauses(), 2);

        assert!(solver.solve());
    }

    #[test]
    fn mock_solver_value() {
        let mut solver = MockSolver::new();
        solver.add_variables(2);

        // Default values are false
        assert!(!solver.value_of(1));
        assert!(!solver.value_of(2));

        // Out of bounds returns false
        assert!(!solver.value_of(0));
        assert!(!solver.value_of(3));
    }

    #[test]
    fn mock_solver_empty() {
        let mut solver = MockSolver::new();

        // Empty solver should return false
        assert!(!solver.solve());
    }
}
