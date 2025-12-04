//! Formula flattening - converts formulas to Negation Normal Form (NNF) and breaks up quantifiers
//!
//! Based on Java: kodkod.engine.fol2sat.FormulaFlattener

use crate::ast::{Formula, FormulaInner, BinaryFormulaOp, Quantifier, Decls};

/// Flattens a formula by:
/// 1. Converting to Negation Normal Form (NNF) - pushing negations to literals
/// 2. Optionally breaking up universal quantifiers when possible
/// 3. Extracting top-level conjuncts
pub struct FormulaFlattener {
    /// Whether to break up quantifiers
    breakup_quantifiers: bool,
}

impl FormulaFlattener {
    /// Creates a new flattener
    pub fn new(breakup_quantifiers: bool) -> Self {
        Self {
            breakup_quantifiers,
        }
    }

    /// Flattens a formula and returns the list of top-level conjuncts
    pub fn flatten(&mut self, formula: &Formula) -> Vec<Formula> {
        // Visit the formula to flatten it
        let flattened = self.visit_formula(formula, false);

        // If it's a conjunction at the top level, extract conjuncts
        match &*flattened.inner() {
            FormulaInner::Nary { op: BinaryFormulaOp::And, formulas } => formulas.clone(),
            FormulaInner::Binary { op: BinaryFormulaOp::And, left, right } => {
                let mut result = Vec::new();
                self.extract_conjuncts(left.clone(), &mut result);
                self.extract_conjuncts(right.clone(), &mut result);
                result
            }
            _ => vec![flattened],
        }
    }

    /// Recursively extract conjuncts from a formula
    fn extract_conjuncts(&self, formula: Formula, result: &mut Vec<Formula>) {
        match &*formula.inner() {
            FormulaInner::Nary { op: BinaryFormulaOp::And, formulas } => {
                for f in formulas {
                    self.extract_conjuncts(f.clone(), result);
                }
            }
            FormulaInner::Binary { op: BinaryFormulaOp::And, left, right } => {
                self.extract_conjuncts(left.clone(), result);
                self.extract_conjuncts(right.clone(), result);
            }
            _ => result.push(formula),
        }
    }

    /// Visit a formula and return its flattened form
    fn visit_formula(&mut self, formula: &Formula, negated: bool) -> Formula {
        match &*formula.inner() {
            FormulaInner::Constant(b) => {
                // Negating a constant flips it
                Formula::constant(if negated { !b } else { *b })
            }

            FormulaInner::Not(inner) => {
                // Double negation cancels out
                self.visit_formula(inner, !negated)
            }

            FormulaInner::Binary { op, left, right } => {
                self.visit_binary(*op, left, right, negated)
            }

            FormulaInner::Nary { op, formulas } => {
                self.visit_nary(*op, formulas, negated)
            }

            FormulaInner::Quantified { quantifier, declarations, body } => {
                self.visit_quantified(*quantifier, declarations, body, negated)
            }

            // For other formulas (comparisons, multiplicity, etc.),
            // just wrap in NOT if negated
            _ => {
                if negated {
                    formula.clone().not()
                } else {
                    formula.clone()
                }
            }
        }
    }

    /// Visit a binary formula
    fn visit_binary(&mut self, op: BinaryFormulaOp, left: &Formula, right: &Formula, negated: bool) -> Formula {
        match op {
            BinaryFormulaOp::And => {
                if negated {
                    // ¬(A ∧ B) = ¬A ∨ ¬B (De Morgan's law)
                    self.visit_formula(left, true).or(self.visit_formula(right, true))
                } else {
                    self.visit_formula(left, false).and(self.visit_formula(right, false))
                }
            }

            BinaryFormulaOp::Or => {
                if negated {
                    // ¬(A ∨ B) = ¬A ∧ ¬B (De Morgan's law)
                    self.visit_formula(left, true).and(self.visit_formula(right, true))
                } else {
                    self.visit_formula(left, false).or(self.visit_formula(right, false))
                }
            }

            BinaryFormulaOp::Implies => {
                if negated {
                    // ¬(A → B) = A ∧ ¬B
                    self.visit_formula(left, false).and(self.visit_formula(right, true))
                } else {
                    // A → B = ¬A ∨ B
                    self.visit_formula(left, true).or(self.visit_formula(right, false))
                }
            }

            BinaryFormulaOp::Iff => {
                if negated {
                    // ¬(A ↔ B) = (A ∧ ¬B) ∨ (¬A ∧ B)
                    let a = self.visit_formula(left, false);
                    let not_a = self.visit_formula(left, true);
                    let b = self.visit_formula(right, false);
                    let not_b = self.visit_formula(right, true);

                    a.and(not_b).or(not_a.and(b))
                } else {
                    // A ↔ B = (A ∧ B) ∨ (¬A ∧ ¬B)
                    let a = self.visit_formula(left, false);
                    let not_a = self.visit_formula(left, true);
                    let b = self.visit_formula(right, false);
                    let not_b = self.visit_formula(right, true);

                    a.and(b).or(not_a.and(not_b))
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
                    Formula::or_all(formulas.iter().map(|f| self.visit_formula(f, true)).collect())
                } else {
                    Formula::and_all(formulas.iter().map(|f| self.visit_formula(f, false)).collect())
                }
            }

            BinaryFormulaOp::Or => {
                if negated {
                    // ¬(A ∨ B ∨ C) = ¬A ∧ ¬B ∧ ¬C
                    Formula::and_all(formulas.iter().map(|f| self.visit_formula(f, true)).collect())
                } else {
                    Formula::or_all(formulas.iter().map(|f| self.visit_formula(f, false)).collect())
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

            match new_quantifier {
                Quantifier::All => Formula::forall(declarations.clone(), self.visit_formula(body, true)),
                Quantifier::Some => Formula::exists(declarations.clone(), self.visit_formula(body, true)),
            }
        } else if self.breakup_quantifiers && quantifier == Quantifier::All {
            // Try to break up universal quantifiers if enabled
            // ∀x.(P ∧ Q) = (∀x.P) ∧ (∀x.Q) if x is not free in one of them
            // This is a simplified version - full implementation would need free variable analysis
            match &*body.inner() {
                FormulaInner::Binary { op: BinaryFormulaOp::And, .. } => {
                    // For now, just flatten the body without breaking up
                    // Full implementation would check free variables
                    Formula::forall(declarations.clone(), self.visit_formula(body, false))
                }
                _ => {
                    Formula::forall(declarations.clone(), self.visit_formula(body, false))
                }
            }
        } else {
            match quantifier {
                Quantifier::All => Formula::forall(declarations.clone(), self.visit_formula(body, false)),
                Quantifier::Some => Formula::exists(declarations.clone(), self.visit_formula(body, false)),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_double_negation() {
        let mut flattener = FormulaFlattener::new(false);

        // ¬¬A = A
        let a = Formula::TRUE;
        let not_not_a = a.clone().not().not();
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
        let not_and = a.clone().and(b.clone()).not();
        let result = flattener.flatten(&not_and);

        assert_eq!(result.len(), 1);
        match &*result[0].inner() {
            FormulaInner::Binary { op: BinaryFormulaOp::Or, left, right } => {
                assert_eq!(*left, Formula::constant(false)); // ¬TRUE
                assert_eq!(*right, Formula::constant(true));  // ¬FALSE
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
        let not_or = a.clone().or(b.clone()).not();
        let result = flattener.flatten(&not_or);

        assert_eq!(result.len(), 2); // Top-level AND gets flattened
        assert_eq!(result[0], Formula::constant(false)); // ¬TRUE
        assert_eq!(result[1], Formula::constant(true));  // ¬FALSE
    }

    #[test]
    fn test_implies_to_or() {
        let mut flattener = FormulaFlattener::new(false);

        // A → B = ¬A ∨ B
        let a = Formula::TRUE;
        let b = Formula::FALSE;
        let implies = a.clone().implies(b.clone());
        let result = flattener.flatten(&implies);

        assert_eq!(result.len(), 1);
        match &*result[0].inner() {
            FormulaInner::Binary { op: BinaryFormulaOp::Or, left, right } => {
                assert_eq!(*left, Formula::constant(false)); // ¬TRUE
                assert_eq!(*right, Formula::FALSE);
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

        let and1 = a.clone().and(b.clone());
        let and2 = c.clone().and(d.clone());
        let top = and1.and(and2);

        let result = flattener.flatten(&top);
        assert_eq!(result.len(), 4);
    }
}
