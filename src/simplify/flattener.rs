//! Formula flattening - converts formulas to Negation Normal Form (NNF) and breaks up quantifiers
//!
//! Based on Java: kodkod.engine.fol2sat.FormulaFlattener

use crate::ast::{Formula, BinaryFormulaOp, Quantifier, Decls};
use std::collections::HashMap;

/// Flattens a formula by:
/// 1. Converting to Negation Normal Form (NNF) - pushing negations to literals
/// 2. Optionally breaking up universal quantifiers when possible
/// 3. Extracting top-level conjuncts
pub struct FormulaFlattener {
    /// Whether to break up quantifiers
    breakup_quantifiers: bool,
    /// Map from flattened formulas to their sources
    conjuncts: HashMap<Formula, Formula>,
    /// Track whether we're under a negation
    negated: bool,
    /// Cache of visited nodes to avoid recomputation
    visited: HashMap<(Formula, bool), Formula>,
}

impl FormulaFlattener {
    /// Creates a new flattener
    pub fn new(breakup_quantifiers: bool) -> Self {
        Self {
            breakup_quantifiers,
            conjuncts: HashMap::new(),
            negated: false,
            visited: HashMap::new(),
        }
    }

    /// Flattens a formula and returns the list of top-level conjuncts
    pub fn flatten(&mut self, formula: &Formula) -> Vec<Formula> {
        // Visit the formula to flatten it
        let flattened = self.visit_formula(formula, false);

        // If it's a conjunction at the top level, extract conjuncts
        match flattened {
            Formula::Nary { op: BinaryFormulaOp::And, formulas } => formulas,
            Formula::Binary { op: BinaryFormulaOp::And, left, right } => {
                let mut result = Vec::new();
                self.extract_conjuncts(*left, &mut result);
                self.extract_conjuncts(*right, &mut result);
                result
            }
            other => vec![other],
        }
    }

    /// Recursively extract conjuncts from a formula
    fn extract_conjuncts(&self, formula: Formula, result: &mut Vec<Formula>) {
        match formula {
            Formula::Nary { op: BinaryFormulaOp::And, formulas } => {
                for f in formulas {
                    self.extract_conjuncts(f, result);
                }
            }
            Formula::Binary { op: BinaryFormulaOp::And, left, right } => {
                self.extract_conjuncts(*left, result);
                self.extract_conjuncts(*right, result);
            }
            other => result.push(other),
        }
    }

    /// Visit a formula and return its flattened form
    fn visit_formula(&mut self, formula: &Formula, negated: bool) -> Formula {
        // Check cache
        let key = (formula.clone(), negated);
        if let Some(cached) = self.visited.get(&key) {
            return cached.clone();
        }

        let result = match formula {
            Formula::Constant(b) => {
                // Negating a constant flips it
                Formula::Constant(if negated { !b } else { *b })
            }

            Formula::Not(inner) => {
                // Double negation cancels out
                self.visit_formula(inner, !negated)
            }

            Formula::Binary { op, left, right } => {
                self.visit_binary(*op, left, right, negated)
            }

            Formula::Nary { op, formulas } => {
                self.visit_nary(*op, formulas, negated)
            }

            Formula::Quantified { quantifier, declarations, body } => {
                self.visit_quantified(*quantifier, declarations, body, negated)
            }

            // For other formulas (comparisons, multiplicity, etc.),
            // just wrap in NOT if negated
            other => {
                if negated {
                    Formula::Not(Box::new(other.clone()))
                } else {
                    other.clone()
                }
            }
        };

        self.visited.insert(key, result.clone());
        result
    }

    /// Visit a binary formula
    fn visit_binary(&mut self, op: BinaryFormulaOp, left: &Formula, right: &Formula, negated: bool) -> Formula {
        match op {
            BinaryFormulaOp::And => {
                if negated {
                    // ¬(A ∧ B) = ¬A ∨ ¬B (De Morgan's law)
                    Formula::Binary {
                        op: BinaryFormulaOp::Or,
                        left: Box::new(self.visit_formula(left, true)),
                        right: Box::new(self.visit_formula(right, true)),
                    }
                } else {
                    Formula::Binary {
                        op: BinaryFormulaOp::And,
                        left: Box::new(self.visit_formula(left, false)),
                        right: Box::new(self.visit_formula(right, false)),
                    }
                }
            }

            BinaryFormulaOp::Or => {
                if negated {
                    // ¬(A ∨ B) = ¬A ∧ ¬B (De Morgan's law)
                    Formula::Binary {
                        op: BinaryFormulaOp::And,
                        left: Box::new(self.visit_formula(left, true)),
                        right: Box::new(self.visit_formula(right, true)),
                    }
                } else {
                    Formula::Binary {
                        op: BinaryFormulaOp::Or,
                        left: Box::new(self.visit_formula(left, false)),
                        right: Box::new(self.visit_formula(right, false)),
                    }
                }
            }

            BinaryFormulaOp::Implies => {
                if negated {
                    // ¬(A → B) = A ∧ ¬B
                    Formula::Binary {
                        op: BinaryFormulaOp::And,
                        left: Box::new(self.visit_formula(left, false)),
                        right: Box::new(self.visit_formula(right, true)),
                    }
                } else {
                    // A → B = ¬A ∨ B
                    Formula::Binary {
                        op: BinaryFormulaOp::Or,
                        left: Box::new(self.visit_formula(left, true)),
                        right: Box::new(self.visit_formula(right, false)),
                    }
                }
            }

            BinaryFormulaOp::Iff => {
                if negated {
                    // ¬(A ↔ B) = (A ∧ ¬B) ∨ (¬A ∧ B)
                    let a = self.visit_formula(left, false);
                    let not_a = self.visit_formula(left, true);
                    let b = self.visit_formula(right, false);
                    let not_b = self.visit_formula(right, true);

                    Formula::Binary {
                        op: BinaryFormulaOp::Or,
                        left: Box::new(Formula::Binary {
                            op: BinaryFormulaOp::And,
                            left: Box::new(a),
                            right: Box::new(not_b),
                        }),
                        right: Box::new(Formula::Binary {
                            op: BinaryFormulaOp::And,
                            left: Box::new(not_a),
                            right: Box::new(b),
                        }),
                    }
                } else {
                    // A ↔ B = (A ∧ B) ∨ (¬A ∧ ¬B)
                    let a = self.visit_formula(left, false);
                    let not_a = self.visit_formula(left, true);
                    let b = self.visit_formula(right, false);
                    let not_b = self.visit_formula(right, true);

                    Formula::Binary {
                        op: BinaryFormulaOp::Or,
                        left: Box::new(Formula::Binary {
                            op: BinaryFormulaOp::And,
                            left: Box::new(a),
                            right: Box::new(b),
                        }),
                        right: Box::new(Formula::Binary {
                            op: BinaryFormulaOp::And,
                            left: Box::new(not_a),
                            right: Box::new(not_b),
                        }),
                    }
                }
            }
        }
    }

    /// Visit an n-ary formula
    fn visit_nary(&mut self, op: BinaryFormulaOp, formulas: &[Formula], negated: bool) -> Formula {
        match op {
            BinaryFormulaOp::And => {
                if negated {
                    // ¬(A ∧ B ∧ C) = ¬A ∨ ¬B ∨ ¬C
                    Formula::Nary {
                        op: BinaryFormulaOp::Or,
                        formulas: formulas.iter().map(|f| self.visit_formula(f, true)).collect(),
                    }
                } else {
                    Formula::Nary {
                        op: BinaryFormulaOp::And,
                        formulas: formulas.iter().map(|f| self.visit_formula(f, false)).collect(),
                    }
                }
            }

            BinaryFormulaOp::Or => {
                if negated {
                    // ¬(A ∨ B ∨ C) = ¬A ∧ ¬B ∧ ¬C
                    Formula::Nary {
                        op: BinaryFormulaOp::And,
                        formulas: formulas.iter().map(|f| self.visit_formula(f, true)).collect(),
                    }
                } else {
                    Formula::Nary {
                        op: BinaryFormulaOp::Or,
                        formulas: formulas.iter().map(|f| self.visit_formula(f, false)).collect(),
                    }
                }
            }

            _ => {
                // IFF and IMPLIES shouldn't appear in n-ary formulas
                panic!("Invalid n-ary operator: {:?}", op);
            }
        }
    }

    /// Visit a quantified formula
    fn visit_quantified(&mut self, quantifier: Quantifier, declarations: &Decls, body: &Formula, negated: bool) -> Formula {
        if negated {
            // ¬(∀x.P) = ∃x.¬P
            // ¬(∃x.P) = ∀x.¬P
            let new_quantifier = match quantifier {
                Quantifier::All => Quantifier::Some,
                Quantifier::Some => Quantifier::All,
            };

            Formula::Quantified {
                quantifier: new_quantifier,
                declarations: declarations.clone(),
                body: Box::new(self.visit_formula(body, true)),
            }
        } else if self.breakup_quantifiers && quantifier == Quantifier::All {
            // Try to break up universal quantifiers if enabled
            // ∀x.(P ∧ Q) = (∀x.P) ∧ (∀x.Q) if x is not free in one of them
            // This is a simplified version - full implementation would need free variable analysis
            match body {
                Formula::Binary { op: BinaryFormulaOp::And, left: _, right: _ } => {
                    // For now, just flatten the body without breaking up
                    // Full implementation would check free variables
                    Formula::Quantified {
                        quantifier,
                        declarations: declarations.clone(),
                        body: Box::new(self.visit_formula(body, false)),
                    }
                }
                _ => {
                    Formula::Quantified {
                        quantifier,
                        declarations: declarations.clone(),
                        body: Box::new(self.visit_formula(body, false)),
                    }
                }
            }
        } else {
            Formula::Quantified {
                quantifier,
                declarations: declarations.clone(),
                body: Box::new(self.visit_formula(body, false)),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Variable, Decl, Expression};

    #[test]
    fn test_double_negation() {
        let mut flattener = FormulaFlattener::new(false);

        // ¬¬A = A
        let a = Formula::TRUE;
        let not_not_a = Formula::not(Formula::not(a.clone()));
        let result = flattener.flatten(&not_not_a);
        assert_eq!(result.len(), 1);
        assert_eq!(result[0], a);
    }

    #[test]
    fn test_de_morgan_and() {
        let mut flattener = FormulaFlattener::new(false);

        // ¬(A ∧ B) = ¬A ∨ ¬B
        let a = Formula::TRUE;
        let b = Formula::FALSE;
        let not_and = Formula::not(Formula::and(a.clone(), b.clone()));
        let result = flattener.flatten(&not_and);

        assert_eq!(result.len(), 1);
        match &result[0] {
            Formula::Binary { op: BinaryFormulaOp::Or, left, right } => {
                assert_eq!(**left, Formula::Constant(false)); // ¬TRUE
                assert_eq!(**right, Formula::Constant(true));  // ¬FALSE
            }
            _ => panic!("Expected OR formula"),
        }
    }

    #[test]
    fn test_de_morgan_or() {
        let mut flattener = FormulaFlattener::new(false);

        // ¬(A ∨ B) = ¬A ∧ ¬B
        let a = Formula::TRUE;
        let b = Formula::FALSE;
        let not_or = Formula::not(Formula::or(a.clone(), b.clone()));
        let result = flattener.flatten(&not_or);

        assert_eq!(result.len(), 2); // Top-level AND gets flattened
        assert_eq!(result[0], Formula::Constant(false)); // ¬TRUE
        assert_eq!(result[1], Formula::Constant(true));  // ¬FALSE
    }

    #[test]
    fn test_implies_to_or() {
        let mut flattener = FormulaFlattener::new(false);

        // A → B = ¬A ∨ B
        let a = Formula::TRUE;
        let b = Formula::FALSE;
        let implies = Formula::implies(a.clone(), b.clone());
        let result = flattener.flatten(&implies);

        assert_eq!(result.len(), 1);
        match &result[0] {
            Formula::Binary { op: BinaryFormulaOp::Or, left, right } => {
                assert_eq!(**left, Formula::Constant(false)); // ¬TRUE
                assert_eq!(**right, Formula::FALSE);
            }
            _ => panic!("Expected OR formula"),
        }
    }

    #[test]
    fn test_extract_conjuncts() {
        let mut flattener = FormulaFlattener::new(false);

        // (A ∧ B) ∧ (C ∧ D) should extract to [A, B, C, D]
        let a = Formula::TRUE;
        let b = Formula::FALSE;
        let c = Formula::TRUE;
        let d = Formula::FALSE;

        let and1 = Formula::and(a.clone(), b.clone());
        let and2 = Formula::and(c.clone(), d.clone());
        let top = Formula::and(and1, and2);

        let result = flattener.flatten(&top);
        assert_eq!(result.len(), 4);
    }
}