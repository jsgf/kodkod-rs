//! Adapters for rustsat solver backends
//!
//! Provides adapters to use rustsat-compatible SAT solvers with kodkod.

use super::SATSolver;

/// Adapter that wraps rustsat solvers to implement our SATSolver trait
///
/// This allows any rustsat-compatible solver to be used with kodkod.
///
/// # Example
///
/// ```ignore
/// use rustsat_batsat::BasicSolver;
/// let solver = RustSatAdapter::new(BasicSolver::default());
/// ```
pub struct RustSatAdapter<S> {
    solver: S,
    num_vars: u32,
    num_clauses: u32,
}

impl<S> RustSatAdapter<S> {
    /// Creates a new adapter wrapping the given solver
    pub fn new(solver: S) -> Self {
        Self {
            solver,
            num_vars: 0,
            num_clauses: 0,
        }
    }
}

impl<S: rustsat::solvers::Solve> SATSolver for RustSatAdapter<S> {
    fn add_variables(&mut self, num_vars: u32) {
        // RustSat auto-creates variables as needed when clauses are added
        // Just track the count for our interface
        self.num_vars += num_vars;
    }

    fn add_clause(&mut self, lits: &[i32]) -> bool {
        use rustsat::types::{Clause, Lit, Var};

        let lits_vec: Vec<Lit> = lits
            .iter()
            .map(|&lit| {
                let abs_lit = lit.abs();
                let var_idx = (abs_lit - 1) as u32;

                // DEBUG: Check if variable index is too high
                if var_idx > Var::MAX_IDX {
                    eprintln!("ERROR: Variable index {} (from literal {}) exceeds MAX_IDX {}",
                              var_idx, lit, Var::MAX_IDX);
                    eprintln!("  num_vars reported: {}", self.num_vars);
                    panic!("Variable index too high: {} > {}", var_idx, Var::MAX_IDX);
                }

                let var = Var::new(var_idx);
                if lit > 0 { var.pos_lit() } else { var.neg_lit() }
            })
            .collect();

        let clause = Clause::from(&lits_vec[..]);
        self.num_clauses += 1;
        self.solver.add_clause(clause).is_ok()
    }

    fn solve(&mut self) -> bool {
        use rustsat::solvers::SolverResult;
        matches!(self.solver.solve(), Ok(SolverResult::Sat))
    }

    fn value_of(&self, var: u32) -> bool {
        use rustsat::types::{TernaryVal, Var};
        if var == 0 || var > self.num_vars {
            return false;
        }
        let v = Var::new(var - 1);
        // Get the assignment from the solution
        match self.solver.solution(v) {
            Ok(assignment) => matches!(assignment.var_value(v), TernaryVal::True),
            Err(_) => false,
        }
    }

    fn num_variables(&self) -> u32 {
        self.num_vars
    }

    fn num_clauses(&self) -> u32 {
        self.num_clauses
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustsat_batsat::BasicSolver;

    #[test]
    fn test_batsat_adapter_basic() {
        // Test basic SAT solving with batsat adapter
        let mut solver = RustSatAdapter::new(BasicSolver::default());

        // Add 2 variables
        solver.add_variables(2);
        assert_eq!(solver.num_variables(), 2);

        // Add clause: x1 OR x2
        assert!(solver.add_clause(&[1, 2]));
        assert_eq!(solver.num_clauses(), 1);

        // Should be satisfiable
        assert!(solver.solve());
    }

    #[test]
    fn test_batsat_adapter_unsat() {
        // Test unsatisfiable formula
        let mut solver = RustSatAdapter::new(BasicSolver::default());

        solver.add_variables(1);

        // Add contradictory clauses
        solver.add_clause(&[1]);   // x1 must be true
        solver.add_clause(&[-1]);  // x1 must be false

        // Should be unsatisfiable
        assert!(!solver.solve());
    }

    #[test]
    fn test_batsat_adapter_solution() {
        // Test retrieving solution values
        let mut solver = RustSatAdapter::new(BasicSolver::default());

        solver.add_variables(2);
        solver.add_clause(&[1]);   // x1 must be true
        solver.add_clause(&[-2]);  // x2 must be false

        assert!(solver.solve());
        assert!(solver.value_of(1));   // x1 should be true
        assert!(!solver.value_of(2));  // x2 should be false
    }
}
