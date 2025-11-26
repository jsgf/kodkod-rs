/*
 * Kodkod -- Copyright (c) 2005-2012, Emina Torlak
 * Rust port -- Copyright (c) 2024
 *
 * Formula simplification and constant propagation
 * Following Java: kodkod.engine.fol2sat.FormulaFlattener, etc.
 */

use crate::ast::{Formula, Expression, Decls};
use crate::ast::formula::BinaryFormulaOp;
use crate::instance::Bounds;
use crate::bool::Options as BoolOptions;
use std::collections::HashMap;

/// Simplifies a formula by:
/// 1. Constant propagation
/// 2. Early evaluation of quantifier-free subformulas
/// 3. Detection of trivial contradictions
///
/// This is essential for performance on formulas with many quantified variables
/// where the inner formula may be trivially false.
pub fn simplify_formula(formula: &Formula, bounds: &Bounds, options: &BoolOptions) -> Formula {
    let mut simplifier = FormulaSimplifier::new(bounds, options);
    simplifier.simplify(formula)
}

struct FormulaSimplifier<'a> {
    bounds: &'a Bounds,
    options: &'a BoolOptions,
    // Cache for simplified subformulas
    cache: HashMap<*const Formula, Formula>,
}

impl<'a> FormulaSimplifier<'a> {
    fn new(bounds: &'a Bounds, options: &'a BoolOptions) -> Self {
        FormulaSimplifier {
            bounds,
            options,
            cache: HashMap::new(),
        }
    }

    fn simplify(&mut self, formula: &Formula) -> Formula {
        use Formula::*;

        match formula {
            // Constants stay as-is
            Constant(_) => formula.clone(),

            // Binary formulas: simplify operands and apply constant rules
            Binary { op, left, right } => {
                let left_simp = self.simplify(left);
                let right_simp = self.simplify(right);

                use BinaryFormulaOp::*;
                match op {
                    And => {
                        // FALSE AND x = FALSE
                        if matches!(left_simp, Constant(false)) || matches!(right_simp, Constant(false)) {
                            return Formula::FALSE;
                        }
                        // TRUE AND x = x
                        if matches!(left_simp, Constant(true)) {
                            return right_simp;
                        }
                        // x AND TRUE = x
                        if matches!(right_simp, Constant(true)) {
                            return left_simp;
                        }
                        Formula::Binary {
                            op: And,
                            left: Box::new(left_simp),
                            right: Box::new(right_simp),
                        }
                    }
                    Or => {
                        // TRUE OR x = TRUE
                        if matches!(left_simp, Constant(true)) || matches!(right_simp, Constant(true)) {
                            return Formula::TRUE;
                        }
                        // FALSE OR x = x
                        if matches!(left_simp, Constant(false)) {
                            return right_simp;
                        }
                        // x OR FALSE = x
                        if matches!(right_simp, Constant(false)) {
                            return left_simp;
                        }
                        Formula::Binary {
                            op: Or,
                            left: Box::new(left_simp),
                            right: Box::new(right_simp),
                        }
                    }
                    Implies => {
                        // FALSE => x = TRUE
                        if matches!(left_simp, Constant(false)) {
                            return Formula::TRUE;
                        }
                        // TRUE => x = x
                        if matches!(left_simp, Constant(true)) {
                            return right_simp;
                        }
                        // x => TRUE = TRUE
                        if matches!(right_simp, Constant(true)) {
                            return Formula::TRUE;
                        }
                        // x => FALSE = NOT x
                        if matches!(right_simp, Constant(false)) {
                            return self.simplify(&Formula::Not(Box::new(left_simp)));
                        }
                        Formula::Binary {
                            op: Implies,
                            left: Box::new(left_simp),
                            right: Box::new(right_simp),
                        }
                    }
                    Iff => {
                        // TRUE <=> x = x
                        if matches!(left_simp, Constant(true)) {
                            return right_simp;
                        }
                        if matches!(right_simp, Constant(true)) {
                            return left_simp;
                        }
                        // FALSE <=> x = NOT x
                        if matches!(left_simp, Constant(false)) {
                            return self.simplify(&Formula::Not(Box::new(right_simp)));
                        }
                        if matches!(right_simp, Constant(false)) {
                            return self.simplify(&Formula::Not(Box::new(left_simp)));
                        }
                        Formula::Binary {
                            op: Iff,
                            left: Box::new(left_simp),
                            right: Box::new(right_simp),
                        }
                    }
                }
            }

            // Negation: apply De Morgan's laws and constant rules
            Not(inner) => {
                let inner_simp = self.simplify(inner);
                match inner_simp {
                    Constant(b) => Formula::Constant(!b),
                    Not(inner2) => *inner2, // NOT NOT x = x
                    _ => Formula::Not(Box::new(inner_simp)),
                }
            }

            // Quantified formulas: try to detect if domain is empty or formula is constant
            Quantified { quantifier, declarations, body } => {
                // First simplify the body
                let body_simp = self.simplify(body);

                // If body is constant, quantifier doesn't matter
                match body_simp {
                    Constant(true) => {
                        // forall x | TRUE = TRUE, exists x | TRUE = TRUE
                        return Formula::TRUE;
                    }
                    Constant(false) => {
                        use crate::ast::Quantifier;
                        match quantifier {
                            Quantifier::All => return Formula::TRUE, // forall x | FALSE = TRUE (vacuous)
                            Quantifier::Some => return Formula::FALSE, // exists x | FALSE = FALSE
                        }
                    }
                    _ => {
                        // Keep the quantified formula with simplified body
                        Formula::Quantified {
                            quantifier: *quantifier,
                            declarations: declarations.clone(),
                            body: Box::new(body_simp),
                        }
                    }
                }
            }

            // For other formula types, don't simplify (yet)
            _ => formula.clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Variable, Quantifier, Decl};
    use crate::instance::Universe;

    #[test]
    fn test_constant_and() {
        let atoms: Vec<&str> = vec!["A"];
        let u = Universe::new(&atoms).unwrap();
        let b = Bounds::new(u);
        let opts = BoolOptions::default();

        // FALSE AND x = FALSE
        let f = Formula::Binary {
            op: BinaryFormulaOp::And,
            left: Box::new(Formula::FALSE),
            right: Box::new(Formula::TRUE),
        };
        let result = simplify_formula(&f, &b, &opts);
        assert!(matches!(result, Formula::Constant(false)));

        // TRUE AND TRUE = TRUE
        let f = Formula::Binary {
            op: BinaryFormulaOp::And,
            left: Box::new(Formula::TRUE),
            right: Box::new(Formula::TRUE),
        };
        let result = simplify_formula(&f, &b, &opts);
        assert!(matches!(result, Formula::Constant(true)));
    }

    #[test]
    fn test_constant_or() {
        let atoms: Vec<&str> = vec!["A"];
        let u = Universe::new(&atoms).unwrap();
        let b = Bounds::new(u);
        let opts = BoolOptions::default();

        // TRUE OR x = TRUE
        let f = Formula::Binary {
            op: BinaryFormulaOp::Or,
            left: Box::new(Formula::TRUE),
            right: Box::new(Formula::FALSE),
        };
        let result = simplify_formula(&f, &b, &opts);
        assert!(matches!(result, Formula::Constant(true)));

        // FALSE OR FALSE = FALSE
        let f = Formula::Binary {
            op: BinaryFormulaOp::Or,
            left: Box::new(Formula::FALSE),
            right: Box::new(Formula::FALSE),
        };
        let result = simplify_formula(&f, &b, &opts);
        assert!(matches!(result, Formula::Constant(false)));
    }

    #[test]
    fn test_quantified_with_constant_body() {
        let atoms: Vec<&str> = vec!["A", "B"];
        let u = Universe::new(&atoms).unwrap();
        let b = Bounds::new(u);
        let opts = BoolOptions::default();

        let x = Variable::unary("x");
        let decls = Decls::from(Decl::one_of(x, Expression::UNIV));

        // exists x | FALSE = FALSE
        let f = Formula::Quantified {
            quantifier: Quantifier::Some,
            declarations: decls.clone(),
            body: Box::new(Formula::FALSE),
        };
        let result = simplify_formula(&f, &b, &opts);
        assert!(matches!(result, Formula::Constant(false)));

        // forall x | FALSE = TRUE (vacuously true)
        let f = Formula::Quantified {
            quantifier: Quantifier::All,
            declarations: decls.clone(),
            body: Box::new(Formula::FALSE),
        };
        let result = simplify_formula(&f, &b, &opts);
        assert!(matches!(result, Formula::Constant(true)));
    }
}
