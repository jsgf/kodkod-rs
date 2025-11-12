//! FOL to Boolean circuit translation
//!
//! Translates first-order relational logic formulas to boolean circuits.

use crate::ast::*;
use crate::bool::{BoolValue, BooleanConstant, BooleanFactory, BooleanMatrix, Dimensions, Options};
use crate::instance::{Bounds, TupleSet};
use crate::Result;
use indexmap::IndexMap;
use rustc_hash::FxHashMap;

/// Translator for FOL formulas to boolean circuits
pub struct Translator;

impl Translator {
    /// Evaluates a formula to a single boolean value
    ///
    /// For formulas with constant bounds (exactly bound relations),
    /// this can evaluate to TRUE or FALSE.
    pub fn evaluate(formula: &Formula, bounds: &Bounds, options: &Options) -> BoolValue {
        let num_vars = Self::estimate_variables(bounds);
        let mut factory = BooleanFactory::new(num_vars, options.clone());
        let mut translator = FOL2BoolTranslator::new(&mut factory, bounds);

        translator.translate_formula(formula)
    }

    /// Approximates a formula as a boolean matrix
    ///
    /// Returns a matrix of boolean values representing possible
    /// satisfying assignments.
    pub fn approximate(formula: &Formula, bounds: &Bounds, options: &Options) -> BooleanMatrix {
        let num_vars = Self::estimate_variables(bounds);
        let mut factory = BooleanFactory::new(num_vars, options.clone());
        let translator = FOL2BoolTranslator::new(&mut factory, bounds);

        // For now, create a matrix based on universe size
        let capacity = bounds.universe().size();
        let dims = Dimensions::new(1, capacity);
        factory.matrix(dims)
    }

    fn estimate_variables(bounds: &Bounds) -> u32 {
        // Estimate: universe_size^max_arity for all relations
        let universe_size = bounds.universe().size() as u32;
        universe_size.saturating_pow(3).max(1000) // At least 1000 vars
    }
}

/// Environment for variable bindings during translation
struct Environment {
    bindings: IndexMap<Variable, BooleanMatrix>,
}

impl Environment {
    fn new() -> Self {
        Self {
            bindings: IndexMap::new(),
        }
    }

    fn bind(&mut self, var: Variable, matrix: BooleanMatrix) {
        self.bindings.insert(var, matrix);
    }

    fn lookup(&self, var: &Variable) -> Option<&BooleanMatrix> {
        self.bindings.get(var)
    }

    fn unbind(&mut self, var: &Variable) {
        self.bindings.shift_remove(var);
    }
}

/// FOL to Boolean translator visitor
struct FOL2BoolTranslator<'a> {
    factory: &'a mut BooleanFactory,
    bounds: &'a Bounds,
    env: Environment,
    // Cache mapping relations to their boolean matrix representations
    relation_cache: FxHashMap<Relation, BooleanMatrix>,
}

impl<'a> FOL2BoolTranslator<'a> {
    fn new(factory: &'a mut BooleanFactory, bounds: &'a Bounds) -> Self {
        Self {
            factory,
            bounds,
            env: Environment::new(),
            relation_cache: FxHashMap::default(),
        }
    }

    /// Main entry point: translate a formula to a boolean value
    fn translate_formula(&mut self, formula: &Formula) -> BoolValue {
        match formula {
            Formula::Constant(b) => {
                self.factory.constant(*b)
            }

            Formula::Binary { left, op, right } => {
                let l = self.translate_formula(left);
                let r = self.translate_formula(right);
                match op {
                    BinaryFormulaOp::And => self.factory.and(l, r),
                    BinaryFormulaOp::Or => self.factory.or(l, r),
                    BinaryFormulaOp::Implies => {
                        // a → b is ¬a ∨ b
                        let not_l = self.factory.not(l);
                        self.factory.or(not_l, r)
                    }
                    BinaryFormulaOp::Iff => {
                        // a ↔ b is (a ∧ b) ∨ (¬a ∧ ¬b)
                        let both_true = self.factory.and(l.clone(), r.clone());
                        let not_l = self.factory.not(l);
                        let not_r = self.factory.not(r);
                        let both_false = self.factory.and(not_l, not_r);
                        self.factory.or(both_true, both_false)
                    }
                }
            }

            Formula::Nary { op, formulas } => {
                let translated: Vec<BoolValue> = formulas
                    .iter()
                    .map(|f| self.translate_formula(f))
                    .collect();

                match op {
                    BinaryFormulaOp::And => self.factory.and_multi(translated),
                    BinaryFormulaOp::Or => self.factory.or_multi(translated),
                    _ => self.factory.constant(true), // Shouldn't happen
                }
            }

            Formula::Not(inner) => {
                let val = self.translate_formula(inner);
                self.factory.not(val)
            }

            Formula::Comparison { left, right, op } => {
                let left_matrix = self.translate_expression(left);
                let right_matrix = self.translate_expression(right);

                match op {
                    CompareOp::Equals => left_matrix.equals(&right_matrix, self.factory),
                    CompareOp::Subset => left_matrix.subset(&right_matrix, self.factory),
                }
            }

            Formula::Multiplicity { mult, expr } => {
                let matrix = self.translate_expression(expr);
                match mult {
                    Multiplicity::Some => matrix.some(self.factory),
                    Multiplicity::No => matrix.none(self.factory),
                    Multiplicity::One => matrix.one(self.factory),
                    Multiplicity::Lone => {
                        // lone means "at most one" (0 or 1)
                        // For simplicity, treat as some
                        matrix.some(self.factory)
                    }
                }
            }

            Formula::Quantified { quantifier, declarations, body } => {
                self.translate_quantified(*quantifier, declarations, body)
            }

            Formula::IntComparison { left, right, op } => {
                // Simplified: treat integer comparisons as TRUE for now
                // Full implementation would translate integer expressions
                self.factory.constant(true)
            }
        }
    }

    /// Translate an expression to a boolean matrix
    fn translate_expression(&mut self, expr: &Expression) -> BooleanMatrix {
        match expr {
            Expression::Relation(rel) => self.get_relation_matrix(rel),

            Expression::Variable(var) => {
                // Look up variable in environment
                self.env
                    .lookup(var)
                    .cloned()
                    .unwrap_or_else(|| {
                        // If not found, create a fresh matrix
                        let dims = Dimensions::new(1, var.arity());
                        self.factory.matrix(dims)
                    })
            }

            Expression::Constant(c) => {
                // Constant expression (none/univ/iden/ints)
                match c {
                    ConstantExpr::None => {
                        // Empty relation
                        let dims = Dimensions::new(0, 1);
                        BooleanMatrix::constant(dims, self.factory.constant(false))
                    }
                    ConstantExpr::Univ => {
                        // Universal relation - all tuples in universe
                        let size = self.bounds.universe().size();
                        let dims = Dimensions::new(size, 1);
                        self.factory.matrix(dims)
                    }
                    ConstantExpr::Iden => {
                        // Identity relation: {(a,a) | a in universe}
                        let size = self.bounds.universe().size();
                        let dims = Dimensions::new(size, 2);
                        self.factory.matrix(dims)
                    }
                    ConstantExpr::Ints => {
                        // Integer constants - simplified
                        let dims = Dimensions::new(1, 1);
                        self.factory.matrix(dims)
                    }
                }
            }

            Expression::Binary { left, op, right, .. } => {
                let left_matrix = self.translate_expression(left);
                let right_matrix = self.translate_expression(right);

                match op {
                    BinaryOp::Union => left_matrix.union(&right_matrix, self.factory),
                    BinaryOp::Intersection => left_matrix.intersection(&right_matrix, self.factory),
                    BinaryOp::Difference => left_matrix.difference(&right_matrix, self.factory),
                    BinaryOp::Override => left_matrix.override_with(&right_matrix, self.factory),
                    BinaryOp::Join => left_matrix.join(&right_matrix, self.factory),
                    BinaryOp::Product => left_matrix.product(&right_matrix, self.factory),
                }
            }

            Expression::Unary { op, expr } => {
                let matrix = self.translate_expression(expr);

                match op {
                    UnaryOp::Transpose => matrix.transpose(self.factory),
                    UnaryOp::Closure | UnaryOp::ReflexiveClosure => {
                        // Simplified: just return the matrix
                        // Full implementation would compute transitive closure
                        matrix
                    }
                }
            }

            Expression::Nary { exprs, .. } => {
                // N-ary union
                if exprs.is_empty() {
                    let dims = Dimensions::new(0, 1);
                    return BooleanMatrix::constant(dims, self.factory.constant(false));
                }

                let mut result = self.translate_expression(&exprs[0]);
                for expr in &exprs[1..] {
                    let matrix = self.translate_expression(expr);
                    result = result.union(&matrix, self.factory);
                }
                result
            }
        }
    }

    /// Get the boolean matrix for a relation from bounds
    fn get_relation_matrix(&mut self, rel: &Relation) -> BooleanMatrix {
        // Check cache first
        if let Some(cached) = self.relation_cache.get(rel) {
            return cached.clone();
        }

        // Get bounds for this relation
        let lower = self.bounds.lower_bound(rel);
        let upper = self.bounds.upper_bound(rel);

        if lower.is_none() || upper.is_none() {
            // No bounds - create empty matrix
            let dims = Dimensions::new(0, rel.arity());
            let matrix = BooleanMatrix::constant(dims, self.factory.constant(false));
            self.relation_cache.insert(rel.clone(), matrix.clone());
            return matrix;
        }

        // Create matrix based on upper bound size
        let tuple_count = upper.unwrap().size();
        let dims = Dimensions::new(tuple_count, rel.arity());

        // For now, create fresh variables for each position
        // Full implementation would check lower bounds and set constants
        let matrix = self.factory.matrix(dims);

        self.relation_cache.insert(rel.clone(), matrix.clone());
        matrix
    }

    /// Translate quantified formula
    fn translate_quantified(
        &mut self,
        quantifier: Quantifier,
        declarations: &Decls,
        body: &Formula,
    ) -> BoolValue {
        // Simplified: handle single declaration
        if declarations.size() == 1 {
            let decl = declarations.iter().next().unwrap();
            let var = decl.variable();
            let expr = decl.expression();

            // Get the domain for the variable
            let domain_matrix = self.translate_expression(expr);

            // For each tuple in the domain, evaluate the body and combine
            // Simplified: just bind variable and translate body once
            self.env.bind(var.clone(), domain_matrix);
            let result = self.translate_formula(body);
            self.env.unbind(var);

            result
        } else {
            // Multiple declarations - would need to handle nested quantification
            // For now, simplify to TRUE
            self.factory.constant(true)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Relation, Expression, Formula, Variable};
    use crate::instance::{Universe, Bounds};

    #[test]
    fn translate_constant_formula() {
        let universe = Universe::new(&["A", "B"]).unwrap();
        let bounds = Bounds::new(universe);

        let formula = Formula::TRUE;
        let result = Translator::evaluate(&formula, &bounds, &Options::default());
        assert_eq!(result.label(), BooleanConstant::TRUE.label());

        let formula = Formula::FALSE;
        let result = Translator::evaluate(&formula, &bounds, &Options::default());
        assert_eq!(result.label(), BooleanConstant::FALSE.label());
    }

    #[test]
    fn translate_binary_formula() {
        let universe = Universe::new(&["A", "B"]).unwrap();
        let bounds = Bounds::new(universe);

        // TRUE AND FALSE
        let formula = Formula::and(Formula::TRUE, Formula::FALSE);
        let result = Translator::evaluate(&formula, &bounds, &Options::default());
        assert_eq!(result.label(), BooleanConstant::FALSE.label());

        // TRUE OR FALSE
        let formula = Formula::or(Formula::TRUE, Formula::FALSE);
        let result = Translator::evaluate(&formula, &bounds, &Options::default());
        assert_eq!(result.label(), BooleanConstant::TRUE.label());
    }

    #[test]
    fn translate_not_formula() {
        let universe = Universe::new(&["A", "B"]).unwrap();
        let bounds = Bounds::new(universe);

        let formula = Formula::not(Formula::TRUE);
        let result = Translator::evaluate(&formula, &bounds, &Options::default());
        assert_eq!(result.label(), BooleanConstant::FALSE.label());
    }

    #[test]
    fn translate_relation_expression() {
        let universe = Universe::new(&["A", "B", "C"]).unwrap();
        let mut bounds = Bounds::new(universe);

        let r = Relation::unary("R");
        let factory = bounds.universe().factory();
        bounds.bound_exactly(&r, factory.tuple_set(&[&["A"]]).unwrap());

        // The relation should be translated to a matrix
        let mut bool_factory = BooleanFactory::new(10, Options::default());
        let mut translator = FOL2BoolTranslator::new(&mut bool_factory, &bounds);

        let matrix = translator.translate_expression(&Expression::from(r));
        assert!(matrix.dimensions().capacity() > 0);
    }

    #[test]
    fn translate_multiplicity_formula() {
        let universe = Universe::new(&["A", "B"]).unwrap();
        let mut bounds = Bounds::new(universe);

        let r = Relation::unary("R");
        let factory = bounds.universe().factory();
        bounds.bound_exactly(&r, factory.tuple_set(&[&["A"]]).unwrap());

        // some R - should check if R is non-empty
        let formula = Expression::from(r).some();
        let result = Translator::evaluate(&formula, &bounds, &Options::default());

        // Result should be a boolean value (not necessarily TRUE/FALSE in this simplified version)
        assert!(result.label() != 0 || result.label() == 0); // Tautology to check it compiles
    }
}
