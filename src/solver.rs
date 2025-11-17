//! Main solver API
//!
//! The solver translates relational formulas to SAT and finds solutions.

use crate::ast::*;
use crate::bool::Options as BoolOptions;
use crate::cnf::CNFTranslator;
use crate::engine::{rustsat_adapter::RustSatAdapter, SATSolver};
use crate::instance::{Bounds, Instance, TupleSet};
use crate::translator::{Translator, LeafInterpreter};
use crate::Result;
use rustsat_batsat::BasicSolver;
use std::time::{Duration, Instant};

/// Solver options
#[derive(Debug, Clone)]
pub struct Options {
    /// Boolean circuit options
    pub bool_options: BoolOptions,
    /// Solver timeout in milliseconds (None = no timeout)
    pub timeout_ms: Option<u64>,
    /// Symmetry breaking bound (0 = disabled, default = 20)
    ///
    /// Controls the maximum length of the lex-leader symmetry breaking
    /// predicate (SBP) that will be generated. Higher values break more
    /// symmetries but may increase overhead. Set to 0 to disable.
    pub symmetry_breaking: i32,
}

impl Default for Options {
    fn default() -> Self {
        Self {
            bool_options: BoolOptions::default(),
            timeout_ms: None,
            symmetry_breaking: 20,
        }
    }
}

/// Main Kodkod solver (uses batsat by default)
///
/// Translates relational logic formulas to SAT and finds satisfying instances.
pub struct Solver {
    options: Options,
}

impl Solver {
    /// Creates a new solver with the given options (uses batsat backend)
    pub fn new(options: Options) -> Self {
        Self { options }
    }

    /// Solves a formula with the given bounds using batsat backend
    ///
    /// Returns a Solution indicating SAT/UNSAT and containing
    /// statistics and (if SAT) a satisfying instance.
    pub fn solve(&self, formula: &Formula, bounds: &Bounds) -> Result<Solution> {
        let mut sat_solver = RustSatAdapter::new(BasicSolver::default());
        self.solve_with(&mut sat_solver, formula, bounds)
    }

    /// Solves a formula with a custom SAT solver
    pub fn solve_with<S: SATSolver>(
        &self,
        sat_solver: &mut S,
        formula: &Formula,
        bounds: &Bounds,
    ) -> Result<Solution> {
        // Step 1: Translate formula to boolean circuit
        let translation_start = Instant::now();
        let translation_result = Translator::evaluate(formula, bounds, &self.options.bool_options);
        let translation_time = translation_start.elapsed();

        // Step 2: Convert boolean circuit to CNF
        let cnf_start = Instant::now();
        let bool_circuit = translation_result.value();
        let interpreter = translation_result.interpreter();
        let cnf_translator = CNFTranslator::new(interpreter.arena());
        let (_top_level_var, cnf) = cnf_translator.translate(bool_circuit);
        let cnf_time = cnf_start.elapsed();

        // Step 3: Run SAT solver
        let solving_start = Instant::now();
        sat_solver.add_variables(cnf.num_variables);

        // Add all clauses to the SAT solver
        for clause in &cnf.clauses {
            sat_solver.add_clause(clause);
        }

        // Solve
        let is_sat = sat_solver.solve();
        let solving_time = solving_start.elapsed();

        let stats = Statistics {
            translation_time: translation_time + cnf_time,
            solving_time,
            num_variables: cnf.num_variables,
            num_clauses: cnf.num_clauses() as u32,
        };

        if is_sat {
            // Extract solution from SAT model
            let instance = self.extract_instance(sat_solver, &interpreter, bounds)?;
            Ok(Solution::Sat { instance, stats })
        } else {
            Ok(Solution::Unsat { stats })
        }
    }

    /// Extracts an Instance from a SAT model
    /// Following Java: similar logic in Translator
    fn extract_instance(
        &self,
        sat_solver: &impl SATSolver,
        interpreter: &LeafInterpreter,
        bounds: &Bounds,
    ) -> Result<Instance> {
        let mut instance = Instance::new(bounds.universe().clone());
        let factory = bounds.universe().factory();

        // For each relation, extract its tuples from the SAT model
        for relation in bounds.relations() {
            let mut tuple_set = TupleSet::empty(bounds.universe().clone(), relation.arity());

            // Start with lower bound (definitely TRUE)
            if let Some(lower) = interpreter.lower_bounds().get(relation) {
                for tuple in lower.iter() {
                    tuple_set.add(tuple.clone())?;
                }
            }

            // Check variables for uncertain tuples
            if let Some(var_range) = interpreter.variable_ranges().get(relation) {
                if let (Some(lower), Some(upper)) = (
                    interpreter.lower_bounds().get(relation),
                    interpreter.upper_bounds().get(relation),
                ) {
                    let lower_indices = LeafInterpreter::tuple_set_to_indices(lower, interpreter.universe());
                    let upper_indices = LeafInterpreter::tuple_set_to_indices(upper, interpreter.universe());

                    let mut var_id = var_range.start;
                    for &idx in &upper_indices {
                        if !lower_indices.contains(&idx) {
                            // This is an uncertain tuple - check SAT model
                            if sat_solver.value_of(var_id) {
                                // Variable is TRUE - add this tuple
                                let tuple = factory.tuple_from_index(relation.arity(), idx)?;
                                tuple_set.add(tuple)?;
                            }
                            var_id += 1;
                        }
                    }
                }
            }

            instance.add(relation.clone(), tuple_set)?;
        }

        Ok(instance)
    }
}

/// Solution to a relational formula
#[derive(Debug)]
pub enum Solution {
    /// Formula is satisfiable
    Sat {
        /// Satisfying instance
        instance: Instance,
        /// Solving statistics
        stats: Statistics,
    },
    /// Formula is unsatisfiable
    Unsat {
        /// Solving statistics
        stats: Statistics,
    },
    /// Formula is trivially true/false
    Trivial {
        /// Whether formula is trivially true
        is_true: bool,
        /// Solving statistics
        stats: Statistics,
    },
}

impl Solution {
    /// Returns true if the formula is satisfiable
    pub fn is_sat(&self) -> bool {
        matches!(self, Solution::Sat { .. })
    }

    /// Returns true if the formula is unsatisfiable
    pub fn is_unsat(&self) -> bool {
        matches!(self, Solution::Unsat { .. })
    }

    /// Returns true if the formula is trivial
    pub fn is_trivial(&self) -> bool {
        matches!(self, Solution::Trivial { .. })
    }

    /// Returns the instance if the solution is SAT
    pub fn instance(&self) -> Option<&Instance> {
        match self {
            Solution::Sat { instance, .. } => Some(instance),
            _ => None,
        }
    }

    /// Returns the statistics
    pub fn statistics(&self) -> &Statistics {
        match self {
            Solution::Sat { stats, .. } => stats,
            Solution::Unsat { stats } => stats,
            Solution::Trivial { stats, .. } => stats,
        }
    }
}

/// Statistics collected during solving
#[derive(Debug, Clone)]
pub struct Statistics {
    translation_time: Duration,
    solving_time: Duration,
    num_variables: u32,
    num_clauses: u32,
}

impl Statistics {
    /// Returns translation time in milliseconds
    pub fn translation_time(&self) -> u64 {
        self.translation_time.as_millis() as u64
    }

    /// Returns solving time in milliseconds
    pub fn solving_time(&self) -> u64 {
        self.solving_time.as_millis() as u64
    }

    /// Returns total time in milliseconds
    pub fn total_time(&self) -> u64 {
        self.translation_time() + self.solving_time()
    }

    /// Returns number of variables
    pub fn num_variables(&self) -> u32 {
        self.num_variables
    }

    /// Returns number of clauses
    pub fn num_clauses(&self) -> u32 {
        self.num_clauses
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::instance::Universe;

    #[test]
    fn solver_basic_sat() {
        let universe = Universe::new(&["A", "B", "C"]).unwrap();
        let mut bounds = Bounds::new(universe);

        let person = Relation::unary("Person");
        let factory = bounds.universe().factory();
        bounds.bound(
            &person,
            factory.none(1),
            factory.tuple_set(&[&["A"], &["B"], &["C"]]).unwrap(),
        ).unwrap();

        let formula = Expression::from(person.clone()).some();

        let solver = Solver::new(Options::default());
        let solution = solver.solve(&formula, &bounds).unwrap();

        assert!(solution.is_sat());

        let instance = solution.instance().unwrap();
        assert_eq!(instance.universe().size(), 3);
    }

    #[test]
    fn solver_basic_unsat() {
        let universe = Universe::new(&["A"]).unwrap();
        let mut bounds = Bounds::new(universe);

        let r = Relation::unary("R");
        let factory = bounds.universe().factory();
        bounds.bound_exactly(&r, factory.none(1)).unwrap();

        // R must be non-empty, but we bound it to empty
        let formula = Expression::from(r).some();

        let solver = Solver::new(Options::default());
        let solution = solver.solve(&formula, &bounds).unwrap();

        assert!(solution.is_unsat());
    }

    #[test]
    fn solver_statistics() {
        let universe = Universe::new(&["A", "B"]).unwrap();
        let mut bounds = Bounds::new(universe);

        let r = Relation::binary("R");
        let factory = bounds.universe().factory();
        bounds.bound(&r, factory.none(2), factory.all(2)).unwrap();

        let formula = Expression::from(r).some();

        let solver = Solver::new(Options::default());
        let solution = solver.solve(&formula, &bounds).unwrap();

        let stats = solution.statistics();
        // Times should be >= 0
        assert!(stats.translation_time() >= 0);
        assert!(stats.solving_time() >= 0);
        // Now we actually generate variables and clauses
        assert!(stats.num_variables() > 0);
        assert!(stats.num_clauses() > 0);
    }

    #[test]
    fn solver_options() {
        let options = Options {
            bool_options: BoolOptions::default(),
            timeout_ms: Some(5000),
            symmetry_breaking: 20,
        };

        let solver = Solver::new(options);
        assert!(solver.options.timeout_ms.is_some());
    }
}
