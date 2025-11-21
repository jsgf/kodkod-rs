//! Boolean circuit to CNF translation
//!
//! Converts boolean gates to CNF clauses using Tseitin transformation.

use crate::bool::{BoolValue, BooleanFormula, FormulaKind, MatrixArena};
use std::collections::HashSet;

/// CNF representation
#[derive(Debug, Clone, Default)]
pub struct CNF {
    /// Number of variables
    pub num_variables: u32,
    /// CNF clauses (each clause is a vec of literals, negative = negated)
    pub clauses: Vec<Vec<i32>>,
}

impl CNF {
    /// Creates a new empty CNF
    pub fn new() -> Self {
        Self::default()
    }

    /// Adds a clause to the CNF
    pub fn add_clause(&mut self, clause: Vec<i32>) {
        // Update max variable
        for &lit in &clause {
            let var = lit.abs() as u32;
            if var > self.num_variables {
                self.num_variables = var;
            }
        }
        self.clauses.push(clause);
    }

    /// Number of clauses
    pub fn num_clauses(&self) -> usize {
        self.clauses.len()
    }
}

/// Translates boolean circuits to CNF
pub struct CNFTranslator<'a> {
    cnf: CNF,
    arena: &'a MatrixArena,
    /// Track which formulas have already been translated (by label)
    visited: HashSet<i32>,
}

impl<'a> CNFTranslator<'a> {
    /// Creates a new CNF translator
    pub fn new(arena: &'a MatrixArena) -> Self {
        Self {
            cnf: CNF::new(),
            arena,
            visited: HashSet::new(),
        }
    }

    /// Translates a boolean value to CNF
    ///
    /// Returns the label of the value and the CNF clauses.
    /// The formula is satisfiable iff the returned label is true.
    pub fn translate(mut self, value: &BoolValue) -> (i32, CNF) {
        let label = self.translate_value(value);

        // Special handling for constants
        match value {
            BoolValue::Constant(c) => {
                if c.label() == -1 {
                    // FALSE: add empty clause to make formula UNSAT
                    self.cnf.add_clause(vec![]);
                }
                // For TRUE (label 0), don't add any clauses - formula is trivially SAT
                // Note: We don't assert [0] because 0 is not a valid DIMACS literal
            }
            _ => {
                // For non-constants, assert that the top-level formula is true
                // Skip if label is 0 (shouldn't happen for non-constants but be safe)
                if label != 0 {
                    self.cnf.add_clause(vec![label]);
                }
            }
        }

        (label, self.cnf)
    }

    /// Translates a boolean value and returns its label
    fn translate_value(&mut self, value: &BoolValue) -> i32 {
        match value {
            BoolValue::Constant(c) => c.label(),
            BoolValue::Variable(v) => v.label(),
            BoolValue::Formula(f) => self.translate_formula(f),
        }
    }

    /// Translates a boolean formula using Tseitin transformation
    fn translate_formula(&mut self, formula: &BooleanFormula) -> i32 {
        let output = formula.label();

        // Skip if already translated
        if self.visited.contains(&output) {
            return output;
        }
        self.visited.insert(output);

        match formula.kind() {
            FormulaKind::And(handle) => {
                let inputs = self.arena.resolve_handle(*handle);
                self.translate_and(output, inputs);
            }
            FormulaKind::Or(handle) => {
                let inputs = self.arena.resolve_handle(*handle);
                self.translate_or(output, inputs);
            }
            FormulaKind::Not(handle) => {
                let input = self.arena.resolve_handle(*handle);
                self.translate_not(output, input);
            }
            FormulaKind::Ite { condition, then_val, else_val } => {
                let cond = self.arena.resolve_handle(*condition);
                let then = self.arena.resolve_handle(*then_val);
                let else_val = self.arena.resolve_handle(*else_val);
                self.translate_ite(output, cond, then, else_val);
            }
        }

        output
    }

    /// Translates AND gate: output = a1 ∧ a2 ∧ ... ∧ an
    ///
    /// CNF encoding:
    /// - (¬a1 ∨ ¬a2 ∨ ... ∨ ¬an ∨ output) - if all inputs true, output true
    /// - (a1 ∨ ¬output) - if output true, each input must be true
    /// - (a2 ∨ ¬output)
    /// - ...
    fn translate_and(&mut self, output: i32, inputs: &[BoolValue]) {
        if inputs.is_empty() {
            return;
        }

        let input_labels: Vec<i32> = inputs.iter().map(|v| self.translate_value(v)).collect();

        // If all inputs are true, output must be true
        let mut clause = input_labels.iter().map(|&l| -l).collect::<Vec<_>>();
        clause.push(output);
        self.cnf.add_clause(clause);

        // If output is true, each input must be true
        for &input in &input_labels {
            self.cnf.add_clause(vec![input, -output]);
        }
    }

    /// Translates OR gate: output = a1 ∨ a2 ∨ ... ∨ an
    ///
    /// CNF encoding:
    /// - (a1 ∨ a2 ∨ ... ∨ an ∨ ¬output) - if any input true, output can be true
    /// - (¬a1 ∨ output) - if output false, each input must be false
    /// - (¬a2 ∨ output)
    /// - ...
    fn translate_or(&mut self, output: i32, inputs: &[BoolValue]) {
        if inputs.is_empty() {
            return;
        }

        let input_labels: Vec<i32> = inputs.iter().map(|v| self.translate_value(v)).collect();

        // If any input is true, output can be true
        let mut clause = input_labels.clone();
        clause.push(-output);
        self.cnf.add_clause(clause);

        // If output is false, all inputs must be false
        for &input in &input_labels {
            self.cnf.add_clause(vec![-input, output]);
        }
    }

    /// Translates NOT gate: output = ¬input
    ///
    /// CNF encoding:
    /// - (input ∨ output) - if input false, output true
    /// - (¬input ∨ ¬output) - if input true, output false
    fn translate_not(&mut self, output: i32, input: &BoolValue) {
        let input_label = self.translate_value(input);

        self.cnf.add_clause(vec![input_label, output]);
        self.cnf.add_clause(vec![-input_label, -output]);
    }

    /// Translates ITE gate: output = if cond then then_val else else_val
    ///
    /// CNF encoding:
    /// - (¬cond ∨ ¬then ∨ output) - if cond and then true, output true
    /// - (¬cond ∨ then ∨ ¬output) - if cond true and output false, then false
    /// - (cond ∨ ¬else ∨ output) - if ¬cond and else true, output true
    /// - (cond ∨ else ∨ ¬output) - if ¬cond true and output false, else false
    fn translate_ite(&mut self, output: i32, condition: &BoolValue, then_val: &BoolValue, else_val: &BoolValue) {
        let cond = self.translate_value(condition);
        let then_label = self.translate_value(then_val);
        let else_label = self.translate_value(else_val);

        // cond → (then → output)
        self.cnf.add_clause(vec![-cond, -then_label, output]);
        // cond → (output → then)
        self.cnf.add_clause(vec![-cond, then_label, -output]);
        // ¬cond → (else → output)
        self.cnf.add_clause(vec![cond, -else_label, output]);
        // ¬cond → (output → else)
        self.cnf.add_clause(vec![cond, else_label, -output]);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bool::{BooleanConstant, BooleanFactory, BooleanVariable, Options};

    #[test]
    fn cnf_empty() {
        let cnf = CNF::new();
        assert_eq!(cnf.num_variables, 0);
        assert_eq!(cnf.num_clauses(), 0);
    }

    #[test]
    fn cnf_add_clause() {
        let mut cnf = CNF::new();
        cnf.add_clause(vec![1, -2, 3]);
        assert_eq!(cnf.num_variables, 3);
        assert_eq!(cnf.num_clauses(), 1);
    }

    #[test]
    fn translate_constant() {
        let arena = crate::bool::MatrixArena::new();
        let translator = CNFTranslator::new(&arena);
        let value = BoolValue::Constant(BooleanConstant::TRUE);
        let (_label, cnf) = translator.translate(&value);

        // TRUE constant: no clauses needed (trivially SAT)
        assert_eq!(cnf.num_clauses(), 0);
    }

    #[test]
    fn translate_variable() {
        let arena = crate::bool::MatrixArena::new();
        let translator = CNFTranslator::new(&arena);
        let value = BoolValue::Variable(BooleanVariable::new(5));
        let (label, cnf) = translator.translate(&value);

        assert_eq!(label, 5);
        // Should have one unit clause asserting variable 5
        assert_eq!(cnf.num_clauses(), 1);
        assert_eq!(cnf.clauses[0], vec![5]);
    }

    #[test]
    fn translate_and_gate() {
        let arena = crate::bool::MatrixArena::new();
        let factory = BooleanFactory::new(10, Options::default());
        let v1 = factory.variable(1);
        let v2 = factory.variable(2);
        let and = factory.and(v1, v2);

        let translator = CNFTranslator::new(&arena);
        let (_label, cnf) = translator.translate(&and);

        // Should have clauses for AND encoding plus assertion
        assert!(cnf.num_clauses() > 0);
        assert!(cnf.num_variables >= 2);
    }

    #[test]
    fn translate_shared_subexpressions() {
        // Test that memoization works: shared subexpressions should be translated only once
        // Create circuit: (v1 AND v2) OR (v1 AND v2)
        // Without memoization, (v1 AND v2) would be translated twice
        let arena = crate::bool::MatrixArena::new();
        let factory = BooleanFactory::new(10, Options::default());
        let v1 = factory.variable(1);
        let v2 = factory.variable(2);

        // Create shared subexpression
        let and = factory.and(v1.clone(), v2);

        // Use the same AND gate in two places
        let or = factory.or(and.clone(), and.clone());

        let translator = CNFTranslator::new(&arena);
        let (_label, cnf) = translator.translate(&or);

        // With memoization: AND gate translated once, OR gate uses its label
        // Expected clauses:
        // - AND gate: 3 clauses (Tseitin encoding)
        // - OR gate: 3 clauses (Tseitin encoding with 2 identical inputs)
        // - Top-level assertion: 1 clause
        // Total: ~7 clauses
        //
        // Without memoization, the AND would be translated twice, giving ~10+ clauses
        assert!(cnf.num_clauses() < 10, "Memoization should prevent duplicate translation");
        assert!(cnf.num_clauses() >= 4, "Should have at least AND + OR + assertion clauses");
    }

    #[test]
    fn translate_or_gate() {
        let arena = crate::bool::MatrixArena::new();
        let factory = BooleanFactory::new(10, Options::default());
        let v1 = factory.variable(1);
        let v2 = factory.variable(2);
        let or = factory.or(v1, v2);

        let translator = CNFTranslator::new(&arena);
        let (_label, cnf) = translator.translate(&or);

        // Should have clauses for OR encoding plus assertion
        assert!(cnf.num_clauses() > 0);
        assert!(cnf.num_variables >= 2);
    }

    #[test]
    fn translate_not_gate() {
        let arena = crate::bool::MatrixArena::new();
        let factory = BooleanFactory::new(10, Options::default());
        let v1 = factory.variable(1);
        let not = factory.not(v1);

        let translator = CNFTranslator::new(&arena);
        let (_label, cnf) = translator.translate(&not);

        // Should have clauses for NOT encoding plus assertion
        assert!(cnf.num_clauses() > 0);
        assert!(cnf.num_variables >= 1);
    }

    #[test]
    fn translate_complex_formula() {
        let arena = crate::bool::MatrixArena::new();
        let factory = BooleanFactory::new(10, Options::default());
        let v1 = factory.variable(1);
        let v2 = factory.variable(2);
        let v3 = factory.variable(3);

        // (v1 ∧ v2) ∨ v3
        let and = factory.and(v1, v2);
        let formula = factory.or(and, v3);

        let translator = CNFTranslator::new(&arena);
        let (_label, cnf) = translator.translate(&formula);

        // Should produce multiple clauses
        assert!(cnf.num_clauses() >= 3);
        assert!(cnf.num_variables >= 3);
    }
}
