/*
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
 * Rust port -- Copyright (c) 2024
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */

//! Unsatisfiable core extraction and proof generation
//!
//! Following Java: kodkod.engine.Proof, kodkod.engine.fol2sat.TranslationLog

use crate::ast::Formula;
use crate::instance::Bounds;
use rustc_hash::FxHashMap;
use std::rc::Rc;

/// Record of a single translation event
///
/// Tracks the mapping from a formula to its CNF literal representation.
/// Following Java: kodkod.engine.fol2sat.TranslationRecord
#[derive(Debug, Clone)]
pub struct TranslationRecord {
    /// The original formula (before optimizations like skolemization)
    pub original: Formula,
    /// The formula after optimizations
    pub translated: Formula,
    /// The CNF literal representing this formula's meaning
    pub literal: i32,
}

/// Log of formula-to-CNF translations
///
/// Tracks how formulas are translated to CNF clauses, enabling
/// extraction of unsatisfiable cores from UNSAT results.
/// Following Java: kodkod.engine.fol2sat.TranslationLog
#[derive(Debug, Clone)]
pub struct TranslationLog {
    /// Translation records in order of generation
    records: Vec<TranslationRecord>,
    /// Top-level formula roots (conjuncts)
    roots: Vec<Formula>,
    /// Bounds used for this translation
    bounds: Option<Bounds>,
}

impl TranslationLog {
    /// Creates a new empty translation log
    pub fn new() -> Self {
        Self {
            records: Vec::new(),
            roots: Vec::new(),
            bounds: None,
        }
    }

    /// Adds a translation record to the log
    pub fn record(&mut self, original: Formula, translated: Formula, literal: i32) {
        self.records.push(TranslationRecord {
            original,
            translated,
            literal,
        });
    }

    /// Sets the formula roots (top-level conjuncts)
    pub fn set_roots(&mut self, roots: Vec<Formula>) {
        self.roots = roots;
    }

    /// Sets the bounds used for this translation
    pub fn set_bounds(&mut self, bounds: Bounds) {
        self.bounds = Some(bounds);
    }

    /// Returns the formula roots
    pub fn roots(&self) -> &[Formula] {
        &self.roots
    }

    /// Returns the bounds if available
    pub fn bounds(&self) -> Option<&Bounds> {
        self.bounds.as_ref()
    }

    /// Returns an iterator over translation records
    pub fn records(&self) -> impl Iterator<Item = &TranslationRecord> {
        self.records.iter()
    }
}

impl Default for TranslationLog {
    fn default() -> Self {
        Self::new()
    }
}

/// Proof of unsatisfiability
///
/// Contains the minimal subset of formulas that form an unsatisfiable core.
/// Following Java: kodkod.engine.Proof
#[derive(Debug)]
pub struct Proof {
    log: Rc<TranslationLog>,
    core: Option<FxHashMap<Formula, Formula>>,
}

impl Proof {
    /// Creates a new proof from a translation log
    ///
    /// For non-trivial UNSAT (from SAT solver), the core is extracted from the log.
    pub fn new(log: Rc<TranslationLog>) -> Self {
        // Initialize core from the log's roots
        let mut core = FxHashMap::default();
        for root in log.roots() {
            core.insert(root.clone(), root.clone());
        }

        Self {
            log,
            core: Some(core),
        }
    }

    /// Creates a proof for a trivially UNSAT formula (constant FALSE)
    ///
    /// The core contains the minimal subset of conjuncts that cause UNSAT.
    /// Following Java: TrivialProof with minimize() logic
    pub fn trivial(formula: Formula, bounds: Bounds) -> Self {
        use crate::ast::{BinaryFormulaOp, FormulaInner};
        use crate::solver::Solver;
        use crate::solver::Options as SolverOptions;

        // Extract conjuncts from the formula if it's an AND
        fn extract_conjuncts_from_formula(f: &Formula) -> Vec<Formula> {
            let mut result = Vec::new();
            fn collect(formula: &Formula, acc: &mut Vec<Formula>) {
                match &*formula.inner() {
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
                        acc.push(formula.clone());
                    }
                }
            }
            collect(f, &mut result);
            result
        }

        let conjuncts = extract_conjuncts_from_formula(&formula);

        // Minimize the core using deletion-based minimization with actual solving
        // Repeatedly try to remove each conjunct
        let mut minimal_core: Vec<Formula> = conjuncts.clone();
        let mut changed = true;

        while changed {
            changed = false;
            let mut i = 0;
            while i < minimal_core.len() {
                if minimal_core.len() == 1 {
                    // Can't remove the last formula
                    break;
                }

                // Try removing this formula
                let without: Vec<Formula> = minimal_core.iter()
                    .enumerate()
                    .filter(|(idx, _)| *idx != i)
                    .map(|(_, f)| f.clone())
                    .collect();

                let test_without = Formula::and_all(without.clone());

                // Use actual solving to check if still UNSAT
                // Create a fresh solver without logging to avoid circular dependency
                let mut test_options = SolverOptions::default();
                test_options.log_translation = false;
                let test_solver = Solver::new(test_options);

                match test_solver.solve(&test_without, &bounds) {
                    Ok(solution) if solution.is_unsat() => {
                        // Still UNSAT without this formula, remove it
                        minimal_core.remove(i);
                        changed = true;
                        // Don't increment i since we removed an element
                    }
                    _ => {
                        // SAT or error without this formula, keep it and move to next
                        i += 1;
                    }
                }
            }
        }

        let mut log = TranslationLog::new();
        log.set_roots(minimal_core.clone());
        log.set_bounds(bounds);
        log.record(formula.clone(), formula.clone(), -i32::MAX);

        let mut core = FxHashMap::default();
        for conjunct in &minimal_core {
            core.insert(conjunct.clone(), conjunct.clone());
        }

        Self {
            log: Rc::new(log),
            core: Some(core),
        }
    }

    /// Returns the minimal unsatisfiable core
    ///
    /// Maps each formula in the core to its original formula before optimizations.
    /// Returns None if the core hasn't been extracted yet.
    pub fn core(&self) -> Option<&FxHashMap<Formula, Formula>> {
        self.core.as_ref()
    }

    /// Returns the translation log
    pub fn log(&self) -> &TranslationLog {
        &self.log
    }

    /// Minimizes the core
    ///
    /// For trivial proofs (constant FALSE), the core is already minimal.
    /// For resolution-based proofs, this would apply strategies like RCE/SCE.
    pub fn minimize(&mut self) {
        // For trivial proofs, core is already minimal (single formula = FALSE)
        // Full implementation would use resolution traces to minimize non-trivial cores
    }
}
