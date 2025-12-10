/*
 * Kodkod -- Copyright (c) 2005-2012, Emina Torlak
 * Rust port -- Copyright (c) 2024
 *
 * Formula simplification and constant propagation
 * Following Java: kodkod.engine.fol2sat.FormulaFlattener, etc.
 */

pub mod flattener;
pub mod skolemizer;

pub use flattener::FormulaFlattener;
pub use skolemizer::Skolemizer;

use crate::ast::{Formula, FormulaInner, Decls, Quantifier};
use crate::ast::formula::BinaryFormulaOp;
use crate::instance::Bounds;

/// Simplifies a formula by:
/// 1. Constant propagation
/// 2. Early evaluation of quantifier-free subformulas
/// 3. Detection of trivial contradictions
/// 4. Eager evaluation of quantifiers over small exact domains
///
/// This is essential for performance on formulas with many quantified variables
/// where the inner formula may be trivially false.
pub fn simplify_formula(formula: &Formula, bounds: &Bounds) -> Formula {
    let mut simplifier = FormulaSimplifier::new(bounds);
    simplifier.simplify(formula)
}

struct FormulaSimplifier<'a> {
    bounds: &'a Bounds,
    // Maximum domain size to eagerly evaluate quantifiers
    max_eager_domain: usize,
}

impl<'a> FormulaSimplifier<'a> {
    fn new(bounds: &'a Bounds) -> Self {
        FormulaSimplifier {
            bounds,
            // Only eagerly evaluate quantifiers if domain is tiny
            // This prevents exponential blowup
            max_eager_domain: 3,
        }
    }

    fn simplify(&mut self, formula: &Formula) -> Formula {
        use FormulaInner::*;

        match &*formula.inner() {
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
                match &*inner_simp.inner() {
                    Constant(b) => Formula::constant(!b),
                    Not(inner2) => inner2.clone(),
                    _ => inner_simp.not(),
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

        // Helper to check if formula is constant
        let is_true = |f: &Formula| matches!(&*f.inner(), FormulaInner::Constant(true));
        let is_false = |f: &Formula| matches!(&*f.inner(), FormulaInner::Constant(false));

        match op {
            // AND simplifications
            And if is_false(&left) || is_false(&right) => Formula::FALSE,
            And if is_true(&left) => right,
            And if is_true(&right) => left,
            And if left == right => left, // x AND x = x

            // OR simplifications
            Or if is_true(&left) || is_true(&right) => Formula::TRUE,
            Or if is_false(&left) => right,
            Or if is_false(&right) => left,
            Or if left == right => left, // x OR x = x

            // IMPLIES simplifications
            Implies if is_false(&left) || is_true(&right) => Formula::TRUE,
            Implies if is_true(&left) => right,
            Implies if is_false(&right) => left.not(),
            Implies if left == right => Formula::TRUE, // x => x = TRUE

            // IFF simplifications
            Iff if is_true(&left) => right,
            Iff if is_true(&right) => left,
            Iff if is_false(&left) => right.not(),
            Iff if is_false(&right) => left.not(),
            Iff if left == right => Formula::TRUE, // x <=> x = TRUE

            // Default: keep the formula
            And => left.and(right),
            Or => left.or(right),
            Implies => left.implies(right),
            Iff => left.iff(right),
        }
    }

    fn simplify_nary(&self, op: BinaryFormulaOp, formulas: &mut Vec<Formula>) -> Formula {
        use BinaryFormulaOp::*;

        let is_true = |f: &Formula| matches!(&*f.inner(), FormulaInner::Constant(true));
        let is_false = |f: &Formula| matches!(&*f.inner(), FormulaInner::Constant(false));

        match op {
            And => {
                // Remove TRUE, detect FALSE
                formulas.retain(|f| !is_true(f));
                if formulas.iter().any(&is_false) {
                    return Formula::FALSE;
                }
                if formulas.is_empty() {
                    return Formula::TRUE;
                }
                if formulas.len() == 1 {
                    return formulas[0].clone();
                }
                Formula::and_all(formulas.clone())
            }
            Or => {
                // Remove FALSE, detect TRUE
                formulas.retain(|f| !is_false(f));
                if formulas.iter().any(is_true) {
                    return Formula::TRUE;
                }
                if formulas.is_empty() {
                    return Formula::FALSE;
                }
                if formulas.len() == 1 {
                    return formulas[0].clone();
                }
                Formula::or_all(formulas.clone())
            }
            _ => Formula::and_all(formulas.clone()) // Fallback, shouldn't happen
        }
    }

    fn simplify_quantified(&self, quantifier: Quantifier, declarations: &Decls, body: Formula) -> Formula {
        // If body is constant, quantifier doesn't matter
        match &*body.inner() {
            FormulaInner::Constant(true) => {
                // forall x | TRUE = TRUE, exists x | TRUE = TRUE
                Formula::TRUE
            }
            FormulaInner::Constant(false) => {
                match quantifier {
                    Quantifier::All => Formula::TRUE, // forall x | FALSE = TRUE (vacuous)
                    Quantifier::Some => Formula::FALSE, // exists x | FALSE = FALSE
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
                match quantifier {
                    Quantifier::All => Formula::forall(declarations.clone(), body),
                    Quantifier::Some => Formula::exists(declarations.clone(), body),
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
            // Check if expression is UNIV (the universe)
            if !matches!(&*decl.expression().inner(), crate::ast::ExpressionInner::Constant(crate::ast::ConstantExpr::Univ)) {
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
    use crate::ast::{Variable, Decl, Expression};
    use crate::instance::Universe;

    #[test]
    fn test_constant_and() {
        let atoms: Vec<&str> = vec!["A"];
        let u = Universe::new(&atoms).unwrap();
        let b = Bounds::new(u);

        // FALSE AND x = FALSE
        let f = Formula::FALSE.and(Formula::TRUE);
        let result = simplify_formula(&f, &b);
        assert!(matches!(&*result.inner(), FormulaInner::Constant(false)));

        // TRUE AND TRUE = TRUE
        let f = Formula::TRUE.and(Formula::TRUE);
        let result = simplify_formula(&f, &b);
        assert!(matches!(&*result.inner(), FormulaInner::Constant(true)));
    }

    #[test]
    fn test_nary_and() {
        let atoms: Vec<&str> = vec!["A"];
        let u = Universe::new(&atoms).unwrap();
        let b = Bounds::new(u);

        // TRUE AND TRUE AND FALSE = FALSE
        let f = Formula::and_all(vec![Formula::TRUE, Formula::TRUE, Formula::FALSE]);
        let result = simplify_formula(&f, &b);
        assert!(matches!(&*result.inner(), FormulaInner::Constant(false)));

        // TRUE AND TRUE AND TRUE = TRUE
        let f = Formula::and_all(vec![Formula::TRUE, Formula::TRUE, Formula::TRUE]);
        let result = simplify_formula(&f, &b);
        assert!(matches!(&*result.inner(), FormulaInner::Constant(true)));
    }

    #[test]
    fn test_constant_detection() {
        let atoms: Vec<&str> = vec!["A"];
        let u = Universe::new(&atoms).unwrap();
        let b = Bounds::new(u);

        // Test that TRUE is recognized as constant
        let result = simplify_formula(&Formula::TRUE, &b);
        assert!(matches!(&*result.inner(), FormulaInner::Constant(true)));

        // Test that FALSE is recognized as constant
        let result = simplify_formula(&Formula::FALSE, &b);
        assert!(matches!(&*result.inner(), FormulaInner::Constant(false)));

        // Test TRUE AND FALSE = FALSE
        let f = Formula::TRUE.and(Formula::FALSE);
        let result = simplify_formula(&f, &b);
        assert!(matches!(&*result.inner(), FormulaInner::Constant(false)));

        // Test TRUE OR FALSE = TRUE
        let f = Formula::TRUE.or(Formula::FALSE);
        let result = simplify_formula(&f, &b);
        assert!(matches!(&*result.inner(), FormulaInner::Constant(true)));

        // Test FALSE OR FALSE = FALSE
        let f = Formula::FALSE.or(Formula::FALSE);
        let result = simplify_formula(&f, &b);
        assert!(matches!(&*result.inner(), FormulaInner::Constant(false)));

        // Test TRUE AND TRUE = TRUE
        let f = Formula::TRUE.and(Formula::TRUE);
        let result = simplify_formula(&f, &b);
        assert!(matches!(&*result.inner(), FormulaInner::Constant(true)));

        // Test NOT TRUE = FALSE
        let f = Formula::TRUE.not();
        let result = simplify_formula(&f, &b);
        assert!(matches!(&*result.inner(), FormulaInner::Constant(false)));

        // Test NOT FALSE = TRUE
        let f = Formula::FALSE.not();
        let result = simplify_formula(&f, &b);
        assert!(matches!(&*result.inner(), FormulaInner::Constant(true)));
    }

    #[test]
    fn test_idempotence_rules() {
        let atoms: Vec<&str> = vec!["A"];
        let u = Universe::new(&atoms).unwrap();
        let b = Bounds::new(u);

        // Create a simple relation for testing
        let r = crate::ast::Relation::unary("r");

        // x AND x = x
        let x = crate::ast::Expression::from(r).some();
        let f = x.clone().and(x.clone());
        let result = simplify_formula(&f, &b);
        assert_eq!(result, x);

        // x OR x = x
        let f = x.clone().or(x.clone());
        let result = simplify_formula(&f, &b);
        assert_eq!(result, x);

        // x => x = TRUE
        let f = x.clone().implies(x.clone());
        let result = simplify_formula(&f, &b);
        assert!(matches!(&*result.inner(), FormulaInner::Constant(true)));

        // x <=> x = TRUE
        let f = x.clone().iff(x.clone());
        let result = simplify_formula(&f, &b);
        assert!(matches!(&*result.inner(), FormulaInner::Constant(true)));
    }

    #[test]
    fn test_quantified_with_constant_body() {
        let atoms: Vec<&str> = vec!["A", "B"];
        let u = Universe::new(&atoms).unwrap();
        let b = Bounds::new(u);

        let x = Variable::unary("x");
        let decls = Decls::from(Decl::one_of(x, Expression::UNIV));

        // exists x | FALSE = FALSE
        let f = Formula::exists(decls.clone(), Formula::FALSE);
        let result = simplify_formula(&f, &b);
        assert!(matches!(&*result.inner(), FormulaInner::Constant(false)));

        // forall x | FALSE = TRUE (vacuously true)
        let f = Formula::forall(decls.clone(), Formula::FALSE);
        let result = simplify_formula(&f, &b);
        assert!(matches!(&*result.inner(), FormulaInner::Constant(true)));
    }
}
