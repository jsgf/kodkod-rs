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
use rustc_hash::FxHashMap;
use std::sync::Arc;

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
}

impl TranslationLog {
    /// Creates a new empty translation log
    pub fn new() -> Self {
        Self {
            records: Vec::new(),
            roots: Vec::new(),
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

    /// Returns the formula roots
    pub fn roots(&self) -> &[Formula] {
        &self.roots
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
    log: Arc<TranslationLog>,
    core: Option<FxHashMap<Formula, Formula>>,
}

impl Proof {
    /// Creates a new proof from a translation log
    ///
    /// For trivially UNSAT formulas (constant FALSE), creates a minimal core.
    /// For non-trivial UNSAT, core extraction requires SAT solver proof traces.
    pub fn new(log: Arc<TranslationLog>) -> Self {
        Self { log, core: None }
    }

    /// Creates a proof for a trivially UNSAT formula (constant FALSE)
    ///
    /// The core contains the formula that simplified to FALSE.
    pub fn trivial(formula: Formula) -> Self {
        let mut log = TranslationLog::new();
        log.set_roots(vec![formula.clone()]);
        log.record(formula.clone(), formula.clone(), -i32::MAX);

        let mut core = FxHashMap::default();
        core.insert(formula.clone(), formula);

        Self {
            log: Arc::new(log),
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
