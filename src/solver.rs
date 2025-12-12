//! Main solver API
//!
//! The solver translates relational formulas to SAT and finds solutions.

use crate::ast::*;
use crate::bool::{BoolValue, Options as BoolOptions};
use crate::cnf::CNFTranslator;
use crate::engine::{rustsat_adapter::RustSatAdapter, SATSolver};
use crate::instance::{Bounds, Instance, TupleSet};
use crate::proof::Proof;
use crate::translator::{Translator, LeafInterpreter};
use crate::Result;
use rustc_hash::FxHashMap;
use rustsat_batsat::BasicSolver;
use std::ops::Range;
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
    /// Whether to flatten formulas to NNF (default = true)
    pub flatten_formulas: bool,
    /// Whether to break up quantifiers when flattening (default = false)
    pub breakup_quantifiers: bool,
    /// Whether to log translation for proof/core extraction (default = false)
    ///
    /// When enabled, the solver tracks the mapping from formulas to CNF clauses,
    /// allowing unsatisfiable cores to be extracted from UNSAT results.
    pub log_translation: bool,
    /// Core granularity level (0-3, default = 0)
    ///
    /// Controls how finely the formula is subdivided for core extraction:
    /// - 0: No subdivision (minimal logging overhead)
    /// - 1: Flatten top-level AND conjuncts
    /// - 2: Also flatten nested conjuncts
    /// - 3: Also push negations through quantifiers
    ///
    /// Higher values produce more precise cores but increase overhead.
    pub core_granularity: u8,
}

impl Default for Options {
    fn default() -> Self {
        Self {
            bool_options: BoolOptions::default(),
            timeout_ms: None,
            symmetry_breaking: 20,
            flatten_formulas: true,
            breakup_quantifiers: false,
            log_translation: false,
            core_granularity: 0,
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
        // Step 0: Simplify formula before translation
        let simplification_start = Instant::now();
        let simplified_formula = crate::simplify::simplify_formula(formula, bounds);

        // Step 0.5: Flatten formula to NNF if enabled
        let flattened_formula = if self.options.flatten_formulas {
            let mut flattener = crate::simplify::FormulaFlattener::new(self.options.breakup_quantifiers);
            let conjuncts = flattener.flatten(&simplified_formula);
            // Combine conjuncts back into a single formula
            Formula::and_all(conjuncts)
        } else {
            simplified_formula
        };

        // Step 0.75: Skolemize if enabled
        let (skolemized_formula, mut final_bounds) = if self.options.bool_options.skolem_depth.is_some() {
            // Check if formula has quantifiers before cloning/skolemizing
            if crate::simplify::skolemizer::has_quantifiers(&flattened_formula) {
                // Skolemization modifies bounds by adding Skolem relations
                let mut mutable_bounds = bounds.clone();
                let mut skolemizer = crate::simplify::Skolemizer::new(&mut mutable_bounds, &self.options);
                let result = skolemizer.skolemize(&flattened_formula);
                (result, mutable_bounds)
            } else {
                // No quantifiers, skip skolemization entirely
                (flattened_formula.clone(), bounds.clone())
            }
        } else {
            (flattened_formula.clone(), bounds.clone())
        };

        // Step 0.8: Break matrix symmetries for relation predicates
        // This modifies bounds to make predicates trivially true, reducing CNF size
        let optimized_formula = if self.options.symmetry_breaking > 0 {
            let predicates = extract_predicates(&skolemized_formula);
            if !predicates.is_empty() {
                let mut breaker = crate::engine::SymmetryBreaker::new(final_bounds.clone());
                let broken = breaker.break_matrix_symmetries(&predicates, true);
                if !broken.is_empty() {
                    // Update bounds with the modified bounds from the breaker
                    final_bounds = breaker.into_bounds();
                    // Replace broken predicates with TRUE (they're now enforced by bounds)
                    replace_predicates(&skolemized_formula, &broken)
                } else {
                    skolemized_formula
                }
            } else {
                skolemized_formula
            }
        } else {
            skolemized_formula
        };

        let simplification_time = simplification_start.elapsed();

        eprintln!("DEBUG: Simplification took {:?}", simplification_time);

        // Check if formula simplified to a constant
        match &*optimized_formula.inner() {
            FormulaInner::Constant(true) => {
                eprintln!("DEBUG: Formula simplified to TRUE");
                // Create an instance from lower bounds
                let instance = Instance::new(final_bounds.universe().clone());
                // TODO: populate with lower bounds
                return Ok(Solution::TriviallySat {
                    instance,
                    stats: Statistics {
                        translation_time: simplification_time,
                        solving_time: Duration::from_micros(0),
                        primary_variables: 0,
                        num_variables: 0,
                        num_clauses: 0,
                    },
                });
            }
            FormulaInner::Constant(false) => {
                eprintln!("DEBUG: Formula simplified to FALSE");

                // Generate proof for trivially UNSAT formula
                let proof = if self.options.log_translation {
                    Some(Proof::trivial(formula.clone(), final_bounds.clone()))
                } else {
                    None
                };

                return Ok(Solution::TriviallyUnsat {
                    stats: Statistics {
                        translation_time: simplification_time,
                        solving_time: Duration::from_micros(0),
                        primary_variables: 0,
                        num_variables: 0,
                        num_clauses: 0,
                    },
                    proof,
                });
            }
            _ => {}
        }

        // Step 1: Translate formula to boolean circuit
        let translation_start = Instant::now();

        let translation_result = Translator::evaluate(
            &optimized_formula,
            &final_bounds,
            &self.options.bool_options,
            self.options.symmetry_breaking,
        );
        let translation_time = translation_start.elapsed() + simplification_time;

        // Step 2: Convert boolean circuit to CNF
        let cnf_start = Instant::now();
        let bool_circuit = translation_result.value();

        // Check if the circuit is constant (trivially sat/unsat)
        if let BoolValue::Constant(c) = bool_circuit {
            eprintln!("DEBUG: Boolean circuit is constant: {}", c.boolean_value());
            if c.boolean_value() {
                // Circuit is constant TRUE - lower bounds satisfy the formula
                let solving_time = cnf_start.elapsed();
                let stats = Statistics {
                    translation_time: translation_time + solving_time,
                    solving_time: Duration::from_micros(0),
                    primary_variables: translation_result.interpreter().num_primary_variables(),
                    num_variables: 0,
                    num_clauses: 0,
                };
                // Extract instance from lower bounds
                let instance = extract_lower_bound_instance(&final_bounds)?;
                return Ok(Solution::TriviallySat { instance, stats });
            } else {
                // Circuit is constant FALSE
                let solving_time = cnf_start.elapsed();
                let stats = Statistics {
                    translation_time: translation_time + solving_time,
                    solving_time: Duration::from_micros(0),
                    primary_variables: translation_result.interpreter().num_primary_variables(),
                    num_variables: 0,
                    num_clauses: 0,
                };

                // Generate proof for trivially UNSAT formula
                let proof = if self.options.log_translation {
                    Some(Proof::trivial(optimized_formula.clone(), final_bounds.clone()))
                } else {
                    None
                };

                return Ok(Solution::TriviallyUnsat { stats, proof });
            }
        }
        eprintln!("DEBUG: Boolean circuit is not constant (has variables)");

        let interpreter = translation_result.interpreter();

        // Extract formula conjuncts for proof tracking if enabled
        let _formula_conjuncts = if self.options.log_translation {
            extract_conjuncts(&optimized_formula)
        } else {
            Vec::new()
        };

        let cnf_translator = CNFTranslator::new();
        let (_top_level_var, cnf) = cnf_translator.translate(bool_circuit);
        let cnf_time = cnf_start.elapsed();

        eprintln!("DEBUG: CNF has {} variables, {} clauses", cnf.num_variables, cnf.num_clauses());

        // Step 3: Run SAT solver
        let solving_start = Instant::now();
        sat_solver.add_variables(cnf.num_variables);

        // Add all clauses to the SAT solver
        for clause in &cnf.clauses {
            sat_solver.add_clause(clause);
        }

        // Prepare for proof extraction if logging enabled
        let formula_conjuncts = if self.options.log_translation {
            extract_conjuncts(&optimized_formula)
        } else {
            Vec::new()
        };

        // Solve (with or without assumptions)
        let is_sat = if !formula_conjuncts.is_empty() {
            // When proof logging is enabled, we'll use assumptions to track conjuncts
            // For now, just solve normally - we'll add assumption tracking in next iteration
            sat_solver.solve()
        } else {
            sat_solver.solve()
        };
        let solving_time = solving_start.elapsed();

        let stats = Statistics {
            translation_time: translation_time + cnf_time,
            solving_time,
            primary_variables: interpreter.num_primary_variables(),
            num_variables: cnf.num_variables,
            num_clauses: cnf.num_clauses() as u32,
        };

        if is_sat {
            // Extract solution from SAT model
            let instance = self.extract_instance(sat_solver, interpreter, &final_bounds)?;
            Ok(Solution::Sat { instance, stats })
        } else {
            // UNSAT - extract proof if logging enabled
            let proof = if !formula_conjuncts.is_empty() {
                // Create a proof with all conjuncts as the core
                use crate::proof::TranslationLog;
                use std::sync::Arc;

                let mut log = TranslationLog::new();
                log.set_roots(formula_conjuncts.clone());
                log.set_bounds(final_bounds.clone());

                // Minimize the core by checking if each conjunct is necessary
                let minimal_core = minimize_core(&formula_conjuncts, &final_bounds, &self.options);

                // Update the log with the minimal core
                log.set_roots(minimal_core);

                Some(Proof::new(Arc::new(log)))
            } else {
                None
            };

            Ok(Solution::Unsat { stats, proof })
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
        extract_instance_from_solver(sat_solver, interpreter, bounds)
    }

    /// Returns an iterator over all solutions to the formula
    ///
    /// The iterator yields Solution::Sat for each satisfying instance,
    /// followed by a final Solution::Unsat when no more solutions exist.
    /// For trivially satisfiable/unsatisfiable formulas, appropriate
    /// trivial solutions are returned.
    ///
    /// # Example
    /// ```rust
    /// use kodkod_rs::ast::{Relation, Expression, Formula};
    /// use kodkod_rs::instance::{Universe, Bounds};
    /// use kodkod_rs::solver::{Solver, Options, Solution};
    ///
    /// let universe = Universe::new(&["A", "B"]).unwrap();
    /// let r = Relation::unary("R");
    /// let mut bounds = Bounds::new(universe);
    /// let factory = bounds.universe().factory();
    /// // R can be empty, {A}, or {B}
    /// bounds.bound(&r, factory.none(1), factory.all(1)).unwrap();
    ///
    /// let formula = Expression::from(r).some();
    /// let solver = Solver::new(Options::default());
    ///
    /// let mut count = 0;
    /// for solution in solver.solve_all(&formula, &bounds) {
    ///     match solution.unwrap() {
    ///         Solution::Sat { .. } => count += 1,
    ///         Solution::Unsat { .. } => break,
    ///         _ => {}
    ///     }
    /// }
    /// assert_eq!(count, 2); // {A} and {B}
    /// ```
    pub fn solve_all(&self, formula: &Formula, bounds: &Bounds) -> SolutionIterator {
        SolutionIterator::new(&self.options, formula, bounds)
    }
}

/// Extracts an Instance from a SAT model (standalone function)
fn extract_instance_from_solver(
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
        if let Some(var_range) = interpreter.variable_ranges().get(relation)
            && let (Some(lower), Some(upper)) = (
                interpreter.lower_bounds().get(relation),
                interpreter.upper_bounds().get(relation),
            ) {
                let lower_indices = LeafInterpreter::tuple_set_to_indices(lower);
                let upper_indices = LeafInterpreter::tuple_set_to_indices(upper);

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

        instance.add(relation.clone(), tuple_set)?;
    }

    Ok(instance)
}

/// Iterator over all solutions to a formula
///
/// Following Java: Solver.SolutionIterator
pub struct SolutionIterator {
    /// SAT solver (None after UNSAT)
    sat_solver: Option<RustSatAdapter<BasicSolver>>,
    /// Data needed for solution extraction (cloned from interpreter)
    extractor: SolutionExtractorData,
    /// Bounds for solution extraction
    bounds: Bounds,
    /// Number of primary variables (for blocking clause)
    num_primary_vars: u32,
    /// Translation time for statistics
    translation_time: Duration,
    /// Total CNF variables
    cnf_num_variables: u32,
    /// Total CNF clauses (initial)
    cnf_num_clauses: u32,
    /// Whether we've returned the final UNSAT yet
    finished: bool,
    /// For trivial cases: the solution to return
    trivial_solution: Option<Solution>,
}

/// Data extracted from LeafInterpreter needed for solution extraction
/// This is cloned from the interpreter so we can drop the TranslationResult
#[derive(Default)]
struct SolutionExtractorData {
    var_ranges: FxHashMap<Relation, Range<u32>>,
    lower_bounds: FxHashMap<Relation, TupleSet>,
    upper_bounds: FxHashMap<Relation, TupleSet>,
}


impl SolutionExtractorData {
    fn from_interpreter(interpreter: &LeafInterpreter) -> Self {
        Self {
            var_ranges: interpreter.variable_ranges().clone(),
            lower_bounds: interpreter.lower_bounds().clone(),
            upper_bounds: interpreter.upper_bounds().clone(),
        }
    }
}

impl SolutionIterator {
    /// Creates a new solution iterator
    fn new(options: &Options, formula: &Formula, bounds: &Bounds) -> Self {
        let simplification_start = Instant::now();

        // Preprocess formula (same as solve_with)
        let simplified_formula = crate::simplify::simplify_formula(formula, bounds);

        let flattened_formula = if options.flatten_formulas {
            let mut flattener = crate::simplify::FormulaFlattener::new(options.breakup_quantifiers);
            let conjuncts = flattener.flatten(&simplified_formula);
            Formula::and_all(conjuncts)
        } else {
            simplified_formula
        };

        let (skolemized_formula, mut final_bounds) = if options.bool_options.skolem_depth.is_some() {
            if crate::simplify::skolemizer::has_quantifiers(&flattened_formula) {
                let mut mutable_bounds = bounds.clone();
                let mut skolemizer = crate::simplify::Skolemizer::new(&mut mutable_bounds, options);
                let result = skolemizer.skolemize(&flattened_formula);
                (result, mutable_bounds)
            } else {
                (flattened_formula.clone(), bounds.clone())
            }
        } else {
            (flattened_formula.clone(), bounds.clone())
        };

        let optimized_formula = if options.symmetry_breaking > 0 {
            let predicates = extract_predicates(&skolemized_formula);
            if !predicates.is_empty() {
                let mut breaker = crate::engine::SymmetryBreaker::new(final_bounds.clone());
                let broken = breaker.break_matrix_symmetries(&predicates, true);
                if !broken.is_empty() {
                    final_bounds = breaker.into_bounds();
                    replace_predicates(&skolemized_formula, &broken)
                } else {
                    skolemized_formula
                }
            } else {
                skolemized_formula
            }
        } else {
            skolemized_formula
        };

        let simplification_time = simplification_start.elapsed();

        // Check for trivial formulas
        match &*optimized_formula.inner() {
            FormulaInner::Constant(true) => {
                // Extract instance from lower bounds
                let instance = match extract_lower_bound_instance(&final_bounds) {
                    Ok(inst) => inst,
                    Err(_) => Instance::new(final_bounds.universe().clone()),
                };
                return Self {
                    sat_solver: None,
                    extractor: SolutionExtractorData::default(),
                    bounds: final_bounds,
                    num_primary_vars: 0,
                    translation_time: simplification_time,
                    cnf_num_variables: 0,
                    cnf_num_clauses: 0,
                    finished: false,
                    trivial_solution: Some(Solution::TriviallySat {
                        instance,
                        stats: Statistics {
                            translation_time: simplification_time,
                            solving_time: Duration::from_micros(0),
                            primary_variables: 0,
                            num_variables: 0,
                            num_clauses: 0,
                        },
                    }),
                };
            }
            FormulaInner::Constant(false) => {
                // Generate proof for trivially UNSAT formula
                let proof = if options.log_translation {
                    Some(Proof::trivial(formula.clone(), final_bounds.clone()))
                } else {
                    None
                };

                return Self {
                    sat_solver: None,
                    extractor: SolutionExtractorData::default(),
                    bounds: final_bounds,
                    num_primary_vars: 0,
                    translation_time: simplification_time,
                    cnf_num_variables: 0,
                    cnf_num_clauses: 0,
                    finished: false,
                    trivial_solution: Some(Solution::TriviallyUnsat {
                        stats: Statistics {
                            translation_time: simplification_time,
                            solving_time: Duration::from_micros(0),
                            primary_variables: 0,
                            num_variables: 0,
                            num_clauses: 0,
                        },
                        proof,
                    }),
                };
            }
            _ => {}
        }

        // Translate to boolean circuit
        let translation_start = Instant::now();
        let translation_result = Translator::evaluate(
            &optimized_formula,
            &final_bounds,
            &options.bool_options,
            options.symmetry_breaking,
        );
        let translation_time = translation_start.elapsed() + simplification_time;

        // Extract data from interpreter for solution extraction
        // This must be done while translation_result is alive
        let interpreter = translation_result.interpreter();
        let num_primary_vars = interpreter.num_primary_variables();
        let extractor = SolutionExtractorData::from_interpreter(interpreter);

        // Convert to CNF
        let cnf_translator = CNFTranslator::new();
        let (_top_level_var, cnf) = cnf_translator.translate(translation_result.value());

        // Initialize SAT solver with CNF
        let mut sat_solver = RustSatAdapter::new(BasicSolver::default());
        sat_solver.add_variables(cnf.num_variables);
        for clause in &cnf.clauses {
            sat_solver.add_clause(clause);
        }

        Self {
            sat_solver: Some(sat_solver),
            extractor,
            bounds: final_bounds,
            num_primary_vars,
            translation_time,
            cnf_num_variables: cnf.num_variables,
            cnf_num_clauses: cnf.num_clauses() as u32,
            finished: false,
            trivial_solution: None,
        }
    }
}

impl Iterator for SolutionIterator {
    type Item = Result<Solution>;

    fn next(&mut self) -> Option<Self::Item> {
        // Handle trivial cases first
        if let Some(trivial) = self.trivial_solution.take() {
            // If trivially UNSAT, we're done - no more solutions possible
            // If trivially SAT, continue enumerating non-trivial solutions beyond lower bound
            if matches!(trivial, Solution::TriviallyUnsat { .. }) {
                self.finished = true;
            }
            return Some(Ok(trivial));
        }

        // If we've already finished, return None
        if self.finished {
            return None;
        }

        // Get mutable reference to solver
        let sat_solver = self.sat_solver.as_mut()?;

        // Solve
        let solving_start = Instant::now();
        let is_sat = sat_solver.solve();
        let solving_time = solving_start.elapsed();

        let stats = Statistics {
            translation_time: self.translation_time,
            solving_time,
            primary_variables: self.num_primary_vars,
            num_variables: self.cnf_num_variables,
            num_clauses: self.cnf_num_clauses,
        };

        if is_sat {
            // Extract solution
            let instance = match extract_instance_with_extractor(sat_solver, &self.extractor, &self.bounds) {
                Ok(inst) => inst,
                Err(e) => {
                    self.finished = true;
                    self.sat_solver = None;
                    return Some(Err(e));
                }
            };

            // Add blocking clause: negate the current model
            // For each primary variable, if true in model, add negative literal, else positive
            let mut blocking_clause = Vec::with_capacity(self.num_primary_vars as usize);
            for var in 1..=self.num_primary_vars {
                if sat_solver.value_of(var) {
                    blocking_clause.push(-(var as i32));
                } else {
                    blocking_clause.push(var as i32);
                }
            }
            sat_solver.add_clause(&blocking_clause);

            Some(Ok(Solution::Sat { instance, stats }))
        } else {
            // UNSAT - no more solutions
            self.finished = true;
            self.sat_solver = None;
            Some(Ok(Solution::Unsat { stats, proof: None })) // TODO: Generate proof when log_translation enabled
        }
    }
}

/// Extracts an Instance from a SAT model using SolutionExtractorData
fn extract_instance_with_extractor(
    sat_solver: &impl SATSolver,
    extractor: &SolutionExtractorData,
    bounds: &Bounds,
) -> Result<Instance> {
    let mut instance = Instance::new(bounds.universe().clone());
    let factory = bounds.universe().factory();

    // For each relation, extract its tuples from the SAT model
    for relation in bounds.relations() {
        let mut tuple_set = TupleSet::empty(bounds.universe().clone(), relation.arity());

        // Start with lower bound (definitely TRUE)
        if let Some(lower) = extractor.lower_bounds.get(relation) {
            for tuple in lower.iter() {
                tuple_set.add(tuple.clone())?;
            }
        }

        // Check variables for uncertain tuples
        if let Some(var_range) = extractor.var_ranges.get(relation)
            && let (Some(lower), Some(upper)) = (
                extractor.lower_bounds.get(relation),
                extractor.upper_bounds.get(relation),
            ) {
                let lower_indices = LeafInterpreter::tuple_set_to_indices(lower);
                let upper_indices = LeafInterpreter::tuple_set_to_indices(upper);

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

        instance.add(relation.clone(), tuple_set)?;
    }

    Ok(instance)
}

/// Extracts an Instance from lower bounds only
/// Used when the formula is trivially satisfied by lower bounds
fn extract_lower_bound_instance(bounds: &Bounds) -> Result<Instance> {
    let mut instance = Instance::new(bounds.universe().clone());

    for relation in bounds.relations() {
        // Use lower bound as the tuple set for this relation
        if let Some(lower) = bounds.lower_bound(relation) {
            instance.add(relation.clone(), lower.clone())?;
        } else {
            // No lower bound means empty set
            let empty = TupleSet::empty(bounds.universe().clone(), relation.arity());
            instance.add(relation.clone(), empty)?;
        }
    }

    Ok(instance)
}

/// Solution to a relational formula
#[derive(Debug)]
pub enum Solution {
    /// Formula is satisfiable (found by SAT solver)
    Sat {
        /// Satisfying instance
        instance: Instance,
        /// Solving statistics
        stats: Statistics,
    },
    /// Formula is trivially satisfiable (lower bounds satisfy it)
    TriviallySat {
        /// Satisfying instance (from lower bounds)
        instance: Instance,
        /// Solving statistics
        stats: Statistics,
    },
    /// Formula is unsatisfiable (SAT solver found UNSAT)
    Unsat {
        /// Solving statistics
        stats: Statistics,
        /// Proof of unsatisfiability (if log_translation was enabled)
        proof: Option<Proof>,
    },
    /// Formula is trivially unsatisfiable (constant false)
    TriviallyUnsat {
        /// Solving statistics
        stats: Statistics,
        /// Proof of unsatisfiability (if log_translation was enabled)
        proof: Option<Proof>,
    },
}

impl Solution {
    /// Returns true if the formula is satisfiable
    pub fn is_sat(&self) -> bool {
        matches!(self, Solution::Sat { .. } | Solution::TriviallySat { .. })
    }

    /// Returns true if the formula is unsatisfiable
    pub fn is_unsat(&self) -> bool {
        matches!(self, Solution::Unsat { .. } | Solution::TriviallyUnsat { .. })
    }

    /// Returns true if the solution is trivial (either trivially sat or trivially unsat)
    pub fn is_trivial(&self) -> bool {
        matches!(self, Solution::TriviallySat { .. } | Solution::TriviallyUnsat { .. })
    }

    /// Returns the instance if the solution is SAT (including trivially SAT)
    pub fn instance(&self) -> Option<&Instance> {
        match self {
            Solution::Sat { instance, .. } | Solution::TriviallySat { instance, .. } => Some(instance),
            _ => None,
        }
    }

    /// Returns the statistics
    pub fn statistics(&self) -> &Statistics {
        match self {
            Solution::Sat { stats, .. } => stats,
            Solution::TriviallySat { stats, .. } => stats,
            Solution::Unsat { stats, .. } => stats,
            Solution::TriviallyUnsat { stats, .. } => stats,
        }
    }

    /// Returns the proof of unsatisfiability if available
    ///
    /// Only present for UNSAT solutions when log_translation was enabled.
    pub fn proof(&self) -> Option<&Proof> {
        match self {
            Solution::Unsat { proof, .. } | Solution::TriviallyUnsat { proof, .. } => proof.as_ref(),
            _ => None,
        }
    }
}

/// Statistics collected during solving
#[derive(Debug, Clone)]
pub struct Statistics {
    translation_time: Duration,
    solving_time: Duration,
    primary_variables: u32,
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

    /// Returns number of primary variables (relation encoding)
    pub fn primary_variables(&self) -> u32 {
        self.primary_variables
    }

    /// Returns number of clauses
    pub fn num_clauses(&self) -> u32 {
        self.num_clauses
    }
}

/// Minimizes an unsat core using brute-force deletion
///
/// For each formula in the core, try removing it and check if the remainder is still UNSAT.
/// If removing a formula makes the remainder SAT, then that formula is necessary for UNSAT.
/// This is O(n²) but produces a minimal core.
///
/// Following Java: Similar to RCEStrategy core reduction
fn minimize_core(core: &[Formula], bounds: &Bounds, options: &Options) -> Vec<Formula> {
    if core.is_empty() || core.len() == 1 {
        // Empty or single-formula cores are already minimal
        return core.to_vec();
    }

    let mut minimal_core = Vec::new();
    let mut candidates: Vec<Formula> = core.to_vec();

    // Try to remove each formula
    for i in 0..candidates.len() {
        let test_formula = candidates[i].clone();

        // Build formula without this conjunct
        let without: Vec<Formula> = candidates.iter()
            .enumerate()
            .filter(|(idx, _)| *idx != i)
            .map(|(_, f)| f.clone())
            .collect();

        if without.is_empty() {
            // If this is the last formula, it must be in the core
            minimal_core.push(test_formula);
            continue;
        }

        // Check if the formula without this conjunct is still UNSAT
        let test_without = Formula::and_all(without.clone());

        // Create a minimal solver to test (no logging to avoid recursion)
        let mut test_options = options.clone();
        test_options.log_translation = false;

        let solver = Solver::new(test_options);
        match solver.solve(&test_without, bounds) {
            Ok(solution) => {
                if solution.is_unsat() {
                    // Still UNSAT without this formula, so it's not needed
                    candidates.remove(i);
                    // Restart the loop since we modified candidates
                    return minimize_core(&candidates, bounds, options);
                } else {
                    // SAT without this formula, so this formula is necessary
                    minimal_core.push(test_formula);
                }
            }
            Err(_) => {
                // Error solving - keep the formula to be safe
                minimal_core.push(test_formula);
            }
        }
    }

    minimal_core
}

/// Extracts top-level conjuncts from a formula
///
/// Recursively flattens AND operations at the top level to get a vector of conjuncts.
/// For proof extraction, we want to identify which conjuncts cause UNSAT.
fn extract_conjuncts(formula: &Formula) -> Vec<Formula> {
    let mut conjuncts = Vec::new();

    fn collect(f: &Formula, acc: &mut Vec<Formula>) {
        match &*f.inner() {
            FormulaInner::Nary { op: BinaryFormulaOp::And, formulas } => {
                for sub in formulas {
                    collect(sub, acc);
                }
            }
            FormulaInner::Binary { op: BinaryFormulaOp::And, left, right } => {
                collect(left, acc);
                collect(right, acc);
            }
            _ => {
                // Not an AND - this is a leaf conjunct
                acc.push(f.clone());
            }
        }
    }

    collect(formula, &mut conjuncts);
    conjuncts
}

/// Extracts all RelationPredicates from a formula
fn extract_predicates(formula: &Formula) -> Vec<crate::ast::RelationPredicate> {
    use crate::ast::RelationPredicate;

    let mut predicates = Vec::new();

    fn visit(f: &Formula, preds: &mut Vec<RelationPredicate>) {
        match &*f.inner() {
            FormulaInner::RelationPredicate(pred) => {
                preds.push(pred.clone());
            }
            FormulaInner::Not(inner) => visit(inner, preds),
            FormulaInner::Binary { left, right, .. } => {
                visit(left, preds);
                visit(right, preds);
            }
            FormulaInner::Nary { formulas, .. } => {
                for sub in formulas {
                    visit(sub, preds);
                }
            }
            FormulaInner::Quantified { body, .. } => {
                visit(body, preds);
            }
            _ => {}
        }
    }

    visit(formula, &mut predicates);
    predicates
}

/// Replaces RelationPredicates in a formula with their replacement formulas
fn replace_predicates(
    formula: &Formula,
    replacements: &rustc_hash::FxHashMap<crate::ast::RelationPredicate, Formula>,
) -> Formula {
    fn visit(
        f: &Formula,
        reps: &rustc_hash::FxHashMap<crate::ast::RelationPredicate, Formula>,
    ) -> Formula {
        match &*f.inner() {
            FormulaInner::RelationPredicate(pred) => {
                if let Some(replacement) = reps.get(pred) {
                    replacement.clone()
                } else {
                    f.clone()
                }
            }
            FormulaInner::Not(inner) => visit(inner, reps).not(),
            FormulaInner::Binary { op, left, right } => {
                let l = visit(left, reps);
                let r = visit(right, reps);
                match op {
                    BinaryFormulaOp::And => l.and(r),
                    BinaryFormulaOp::Or => l.or(r),
                    BinaryFormulaOp::Implies => l.implies(r),
                    BinaryFormulaOp::Iff => l.iff(r),
                }
            }
            FormulaInner::Nary { op, formulas } => {
                let replaced: Vec<Formula> = formulas.iter().map(|sub| visit(sub, reps)).collect();
                match op {
                    BinaryFormulaOp::And => Formula::and_all(replaced),
                    BinaryFormulaOp::Or => Formula::or_all(replaced),
                    _ => Formula::and_all(replaced),
                }
            }
            FormulaInner::Quantified { quantifier, declarations, body } => {
                match quantifier {
                    Quantifier::All => Formula::forall(declarations.clone(), visit(body, reps)),
                    Quantifier::Some => Formula::exists(declarations.clone(), visit(body, reps)),
                }
            }
            _ => f.clone(),
        }
    }

    visit(formula, replacements)
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
        // Check statistics are generated
        assert!(stats.num_variables() > 0);
        assert!(stats.num_clauses() > 0);
    }

    #[test]
    fn solver_options() {
        let options = Options {
            bool_options: BoolOptions::default(),
            timeout_ms: Some(5000),
            symmetry_breaking: 20,
            flatten_formulas: true,
            breakup_quantifiers: false,
            log_translation: false,
            core_granularity: 0,
        };

        let solver = Solver::new(options);
        assert!(solver.options.timeout_ms.is_some());
    }
}
