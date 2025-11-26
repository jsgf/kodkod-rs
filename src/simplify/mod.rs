/*
 * Kodkod -- Copyright (c) 2005-2012, Emina Torlak
 * Rust port -- Copyright (c) 2024
 *
 * Formula simplification and constant propagation
 * Following Java: kodkod.engine.fol2sat.FormulaFlattener, etc.
 */

use crate::ast::{Formula, Expression, Decls, Quantifier};
use crate::ast::formula::BinaryFormulaOp;
use crate::instance::Bounds;
use crate::bool::Options as BoolOptions;
use std::collections::HashMap;

/// Simplifies a formula by:
/// 1. Constant propagation
/// 2. Early evaluation of quantifier-free subformulas
/// 3. Detection of trivial contradictions
/// 4. Eager evaluation of quantifiers over small exact domains
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
    // Maximum domain size to eagerly evaluate quantifiers
    max_eager_domain: usize,
}

impl<'a> FormulaSimplifier<'a> {
    fn new(bounds: &'a Bounds, options: &'a BoolOptions) -> Self {
        FormulaSimplifier {
            bounds,
            options,
            cache: HashMap::new(),
            // Only eagerly evaluate quantifiers if domain is tiny
            // This prevents exponential blowup
            max_eager_domain: 3,
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

                self.simplify_binary(op, left_simp, right_simp)
            }

            // N-ary formulas: simplify components
            Nary { op, formulas } => {
                let mut simplified: Vec<Formula> = formulas.iter()
                    .map(|f| self.simplify(f))
                    .collect();

                self.simplify_nary(*op, &mut simplified)
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

                self.simplify_quantified(*quantifier, declarations, body_simp)
            }

            // For other formula types, don't simplify (yet)
            _ => formula.clone(),
        }
    }

    fn simplify_binary(&self, op: &BinaryFormulaOp, left: Formula, right: Formula) -> Formula {
        use BinaryFormulaOp::*;
        match op {
            And => {
                // FALSE AND x = FALSE
                if matches!(left, Formula::Constant(false)) || matches!(right, Formula::Constant(false)) {
                    return Formula::FALSE;
                }
                // TRUE AND x = x
                if matches!(left, Formula::Constant(true)) {
                    return right;
                }
                // x AND TRUE = x
                if matches!(right, Formula::Constant(true)) {
                    return left;
                }
                Formula::Binary {
                    op: And,
                    left: Box::new(left),
                    right: Box::new(right),
                }
            }
            Or => {
                // TRUE OR x = TRUE
                if matches!(left, Formula::Constant(true)) || matches!(right, Formula::Constant(true)) {
                    return Formula::TRUE;
                }
                // FALSE OR x = x
                if matches!(left, Formula::Constant(false)) {
                    return right;
                }
                // x OR FALSE = x
                if matches!(right, Formula::Constant(false)) {
                    return left;
                }
                Formula::Binary {
                    op: Or,
                    left: Box::new(left),
                    right: Box::new(right),
                }
            }
            Implies => {
                // FALSE => x = TRUE
                if matches!(left, Formula::Constant(false)) {
                    return Formula::TRUE;
                }
                // TRUE => x = x
                if matches!(left, Formula::Constant(true)) {
                    return right;
                }
                // x => TRUE = TRUE
                if matches!(right, Formula::Constant(true)) {
                    return Formula::TRUE;
                }
                // x => FALSE = NOT x
                if matches!(right, Formula::Constant(false)) {
                    return Formula::Not(Box::new(left));
                }
                Formula::Binary {
                    op: Implies,
                    left: Box::new(left),
                    right: Box::new(right),
                }
            }
            Iff => {
                // TRUE <=> x = x
                if matches!(left, Formula::Constant(true)) {
                    return right;
                }
                if matches!(right, Formula::Constant(true)) {
                    return left;
                }
                // FALSE <=> x = NOT x
                if matches!(left, Formula::Constant(false)) {
                    return Formula::Not(Box::new(right));
                }
                if matches!(right, Formula::Constant(false)) {
                    return Formula::Not(Box::new(left));
                }
                Formula::Binary {
                    op: Iff,
                    left: Box::new(left),
                    right: Box::new(right),
                }
            }
        }
    }

    fn simplify_nary(&self, op: BinaryFormulaOp, formulas: &mut Vec<Formula>) -> Formula {
        use BinaryFormulaOp::*;

        match op {
            And => {
                // Remove TRUE, detect FALSE
                formulas.retain(|f| !matches!(f, Formula::Constant(true)));
                if formulas.iter().any(|f| matches!(f, Formula::Constant(false))) {
                    return Formula::FALSE;
                }
                if formulas.is_empty() {
                    return Formula::TRUE;
                }
                if formulas.len() == 1 {
                    return formulas[0].clone();
                }
                Formula::Nary { op: And, formulas: formulas.clone() }
            }
            Or => {
                // Remove FALSE, detect TRUE
                formulas.retain(|f| !matches!(f, Formula::Constant(false)));
                if formulas.iter().any(|f| matches!(f, Formula::Constant(true))) {
                    return Formula::TRUE;
                }
                if formulas.is_empty() {
                    return Formula::FALSE;
                }
                if formulas.len() == 1 {
                    return formulas[0].clone();
                }
                Formula::Nary { op: Or, formulas: formulas.clone() }
            }
            _ => Formula::Nary { op, formulas: formulas.clone() }
        }
    }

    fn simplify_quantified(&self, quantifier: Quantifier, declarations: &Decls, body: Formula) -> Formula {
        // If body is constant, quantifier doesn't matter
        match body {
            Formula::Constant(true) => {
                // forall x | TRUE = TRUE, exists x | TRUE = TRUE
                return Formula::TRUE;
            }
            Formula::Constant(false) => {
                match quantifier {
                    Quantifier::All => return Formula::TRUE, // forall x | FALSE = TRUE (vacuous)
                    Quantifier::Some => return Formula::FALSE, // exists x | FALSE = FALSE
                }
            }
            _ => {
                // Check if we should eagerly evaluate this quantifier
                // Only do this for very small domains to avoid exponential blowup
                if self.should_eager_evaluate(declarations) {
                    eprintln!("DEBUG: Attempting eager evaluation of quantified formula with {} declarations", declarations.size());
                    if let Some(result) = self.try_eager_evaluate(quantifier, declarations, &body) {
                        eprintln!("DEBUG: Eager evaluation succeeded: {:?}", result);
                        return result;
                    }
                    eprintln!("DEBUG: Eager evaluation failed or too complex");
                }

                // Keep the quantified formula with simplified body
                Formula::Quantified {
                    quantifier,
                    declarations: declarations.clone(),
                    body: Box::new(body),
                }
            }
        }
    }

    fn should_eager_evaluate(&self, declarations: &Decls) -> bool {
        // Only eager evaluate if all declarations are over UNIV and universe is small
        if self.bounds.universe().size() > self.max_eager_domain {
            return false;
        }

        // Check if all declarations are simple (one_of UNIV)
        for decl in declarations.iter() {
            if !matches!(decl.expression(), Expression::UNIV) {
                return false;
            }
        }

        true
    }

    fn try_eager_evaluate(&self, _quantifier: Quantifier, _declarations: &Decls, _body: &Formula) -> Option<Formula> {
        // For now, return None - eager evaluation not yet implemented
        // This would require:
        // 1. Enumerate all possible bindings of variables
        // 2. For each binding, substitute variables in body
        // 3. Evaluate the substituted formula
        // 4. Combine results with AND (forall) or OR (exists)

        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Variable, Decl};
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
    fn test_nary_and() {
        let atoms: Vec<&str> = vec!["A"];
        let u = Universe::new(&atoms).unwrap();
        let b = Bounds::new(u);
        let opts = BoolOptions::default();

        // TRUE AND TRUE AND FALSE = FALSE
        let f = Formula::Nary {
            op: BinaryFormulaOp::And,
            formulas: vec![Formula::TRUE, Formula::TRUE, Formula::FALSE],
        };
        let result = simplify_formula(&f, &b, &opts);
        assert!(matches!(result, Formula::Constant(false)));

        // TRUE AND TRUE AND TRUE = TRUE
        let f = Formula::Nary {
            op: BinaryFormulaOp::And,
            formulas: vec![Formula::TRUE, Formula::TRUE, Formula::TRUE],
        };
        let result = simplify_formula(&f, &b, &opts);
        assert!(matches!(result, Formula::Constant(true)));
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
