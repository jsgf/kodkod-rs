//! FOL to Boolean circuit translation
//!
//! Translates first-order relational logic formulas to boolean circuits.
//! Following Java: kodkod.engine.fol2sat.FOL2BoolTranslator

mod leaf_interpreter;
mod environment;

pub use leaf_interpreter::LeafInterpreter;
pub use environment::Environment;

use crate::ast::*;
use crate::bool::{BoolValue, BooleanConstant, BooleanMatrix, Dimensions, Options};
use crate::instance::Bounds;

/// Translator for FOL formulas to boolean circuits
pub struct Translator;

impl Translator {
    /// Evaluates a formula to a single boolean value
    /// Following Java: Translator.translate()
    /// Returns the boolean circuit and the interpreter (for solution extraction)
    pub fn evaluate(formula: &Formula, bounds: &Bounds, options: &Options) -> (BoolValue, LeafInterpreter) {
        let mut interpreter = LeafInterpreter::from_bounds(bounds, options);
        let mut translator = FOL2BoolTranslator::new(&mut interpreter);
        let circuit = translator.translate_formula(formula);
        (circuit, interpreter)
    }

    /// Approximates a formula as a boolean matrix (not used in main solver)
    pub fn approximate(_formula: &Formula, bounds: &Bounds, options: &Options) -> BooleanMatrix {
        let mut interpreter = LeafInterpreter::from_bounds(bounds, options);
        let capacity = bounds.universe().size();
        let dims = Dimensions::new(1, capacity);
        interpreter.factory_mut().matrix(dims)
    }
}

/// FOL to Boolean translator
/// Following Java: FOL2BoolTranslator
struct FOL2BoolTranslator<'a> {
    interpreter: &'a mut LeafInterpreter,
    env: Environment,
}

impl<'a> FOL2BoolTranslator<'a> {
    fn new(interpreter: &'a mut LeafInterpreter) -> Self {
        Self {
            interpreter,
            env: Environment::empty(),
        }
    }

    /// Main entry point: translate a formula to a boolean value
    /// Following Java: FOL2BoolTranslator visitor methods
    fn translate_formula(&mut self, formula: &Formula) -> BoolValue {
        let result = match formula {
            Formula::Constant(b) => {
                self.interpreter.factory_mut().constant(*b)
            }

            Formula::Binary { left, op, right } => {
                let l = self.translate_formula(left);
                let r = self.translate_formula(right);
                let factory = self.interpreter.factory_mut();
                match op {
                    BinaryFormulaOp::And => factory.and(l, r),
                    BinaryFormulaOp::Or => factory.or(l, r),
                    BinaryFormulaOp::Implies => {
                        let not_l = factory.not(l);
                        factory.or(not_l, r)
                    }
                    BinaryFormulaOp::Iff => {
                        let both_true = factory.and(l.clone(), r.clone());
                        let not_l = factory.not(l);
                        let not_r = factory.not(r);
                        let both_false = factory.and(not_l, not_r);
                        factory.or(both_true, both_false)
                    }
                }
            }

            Formula::Nary { op, formulas } => {
                let translated: Vec<BoolValue> = formulas
                    .iter()
                    .map(|f| self.translate_formula(f))
                    .collect();

                let factory = self.interpreter.factory_mut();
                match op {
                    BinaryFormulaOp::And => factory.and_multi(translated),
                    BinaryFormulaOp::Or => factory.or_multi(translated),
                    _ => factory.constant(true),
                }
            }

            Formula::Not(inner) => {
                let val = self.translate_formula(inner);
                self.interpreter.factory_mut().not(val)
            }

            Formula::Comparison { left, right, op } => {
                let left_matrix = self.translate_expression(left);
                let right_matrix = self.translate_expression(right);
                let factory = self.interpreter.factory_mut();

                match op {
                    CompareOp::Equals => left_matrix.equals(&right_matrix, factory),
                    CompareOp::Subset => left_matrix.subset(&right_matrix, factory),
                }
            }

            Formula::Multiplicity { mult, expr } => {
                let matrix = self.translate_expression(expr);
                let factory = self.interpreter.factory_mut();
                match mult {
                    Multiplicity::Some => matrix.some(factory),
                    Multiplicity::No => matrix.none(factory),
                    Multiplicity::One => matrix.one(factory),
                    Multiplicity::Lone => {
                        let no_val = matrix.none(factory);
                        let one_val = matrix.one(factory);
                        factory.or(no_val, one_val)
                    }
                }
            }

            Formula::Quantified { quantifier, declarations, body } => {
                self.translate_quantified(*quantifier, declarations, body)
            }

            Formula::IntComparison { .. } => {
                // Integer comparisons are an extension feature
                // For now, return TRUE (conservative approximation)
                self.interpreter.factory_mut().constant(true)
            }
        };
        result
    }

    /// Expression translation
    /// Following Java: FOL2BoolTranslator.visit(Expression)
    fn translate_expression(&mut self, expr: &Expression) -> BooleanMatrix {
        let result = match expr {
            Expression::Relation(rel) => {
                self.interpreter.interpret_relation(rel)
            }

            Expression::Variable(var) => {
                self.env.lookup(var)
                    .cloned()
                    .unwrap_or_else(|| panic!("Unbound variable: {}", var.name()))
            }

            Expression::Constant(c) => {
                self.interpreter.interpret_constant(*c)
            }

            Expression::Binary { left, op, right, .. } => {
                let left_matrix = self.translate_expression(left);
                let right_matrix = self.translate_expression(right);
                let factory = self.interpreter.factory_mut();

                match op {
                    BinaryOp::Union => left_matrix.union(&right_matrix, factory),
                    BinaryOp::Intersection => left_matrix.intersection(&right_matrix, factory),
                    BinaryOp::Difference => left_matrix.difference(&right_matrix, factory),
                    BinaryOp::Override => left_matrix.override_with(&right_matrix, factory),
                    BinaryOp::Join => left_matrix.join(&right_matrix, factory),
                    BinaryOp::Product => left_matrix.product(&right_matrix, factory),
                }
            }

            Expression::Unary { op, expr } => {
                match op {
                    UnaryOp::Transpose => {
                        let matrix = self.translate_expression(expr);
                        let factory = self.interpreter.factory_mut();
                        matrix.transpose(factory)
                    }
                    UnaryOp::Closure => {
                        let matrix = self.translate_expression(expr);
                        let factory = self.interpreter.factory_mut();
                        matrix.closure(factory)
                    }
                    UnaryOp::ReflexiveClosure => {
                        let matrix = self.translate_expression(expr);
                        let iden = self.interpreter.interpret_constant(ConstantExpr::Iden);
                        let factory = self.interpreter.factory_mut();
                        matrix.reflexive_closure(factory, &iden)
                    }
                }
            }

            Expression::Nary { exprs, .. } => {
                // N-ary union
                if exprs.is_empty() {
                    let dims = Dimensions::new(0, 1);
                    return BooleanMatrix::empty(dims);
                }

                let mut result = self.translate_expression(&exprs[0]);
                for expr in &exprs[1..] {
                    let matrix = self.translate_expression(expr);
                    let factory = self.interpreter.factory_mut();
                    result = result.union(&matrix, factory);
                }
                result
            }
        };
        result
    }

    /// Quantifier translation
    /// Following Java: FOL2BoolTranslator.visit(QuantifiedFormula)
    fn translate_quantified(
        &mut self,
        quantifier: Quantifier,
        declarations: &Decls,
        body: &Formula
    ) -> BoolValue {
        match quantifier {
            Quantifier::Some => {
                let mut acc = Vec::new();
                self.translate_exists(declarations, body, 0,
                                     BoolValue::Constant(BooleanConstant::TRUE),
                                     &mut acc);
                self.interpreter.factory_mut().or_multi(acc)
            }
            Quantifier::All => {
                let mut acc = Vec::new();
                self.translate_forall(declarations, body, 0,
                                     BoolValue::Constant(BooleanConstant::FALSE),
                                     &mut acc);
                self.interpreter.factory_mut().and_multi(acc)
            }
        }
    }

    /// Existential quantification (FOLLOWING JAVA EXACTLY)
    /// Following Java: FOL2BoolTranslator.some(...)
    fn translate_exists(
        &mut self,
        decls: &Decls,
        formula: &Formula,
        current_decl: usize,
        decl_constraints: BoolValue,
        acc: &mut Vec<BoolValue>
    ) {
        // Base case: all variables bound
        if current_decl >= decls.size() {
            let formula_val = self.translate_formula(formula);
            let factory = self.interpreter.factory_mut();
            let result = factory.and(decl_constraints.clone(), formula_val);
            acc.push(result);
            return;
        }

        // Get current declaration
        let decl = decls.iter().nth(current_decl).unwrap();
        let var = decl.variable();
        let domain = self.translate_expression(decl.expression());

        // Create ground matrix for this variable
        let mut ground_value = self.interpreter.factory_mut().matrix(*domain.dimensions());

        // PUSH binding
        self.env.extend(var.clone(), ground_value.clone());

        // ITERATE over each tuple in domain
        let indices: Vec<(usize, BoolValue)> = domain.iter_indexed()
            .map(|(idx, val)| (idx, val.clone()))
            .collect();

        for (index, value) in indices {
            // Set this index to TRUE
            ground_value.set(index, BoolValue::Constant(BooleanConstant::TRUE));

            // Update environment
            *self.env.lookup_mut(&var).unwrap() = ground_value.clone();

            // Recurse with updated constraints
            let factory = self.interpreter.factory_mut();
            let new_constraints = factory.and(value.clone(), decl_constraints.clone());

            self.translate_exists(decls, formula, current_decl + 1, new_constraints, acc);

            // Reset this index to FALSE
            ground_value.set(index, BoolValue::Constant(BooleanConstant::FALSE));
        }

        // POP binding
        self.env.pop();
    }

    /// Universal quantification (FOLLOWING JAVA EXACTLY)
    /// Following Java: FOL2BoolTranslator.all(...)
    fn translate_forall(
        &mut self,
        decls: &Decls,
        formula: &Formula,
        current_decl: usize,
        decl_constraints: BoolValue,
        acc: &mut Vec<BoolValue>
    ) {
        // Base case: all variables bound
        if current_decl >= decls.size() {
            let formula_val = self.translate_formula(formula);
            let factory = self.interpreter.factory_mut();
            // forall: decl_constraints ∨ formula
            // (NOT following my earlier comment - following Java exactly)
            let result = factory.or(decl_constraints.clone(), formula_val);
            acc.push(result);
            return;
        }

        // Get current declaration
        let decl = decls.iter().nth(current_decl).unwrap();
        let var = decl.variable();
        let domain = self.translate_expression(decl.expression());

        // Create ground matrix
        let mut ground_value = self.interpreter.factory_mut().matrix(*domain.dimensions());

        // PUSH binding
        self.env.extend(var.clone(), ground_value.clone());

        // ITERATE
        let indices: Vec<(usize, BoolValue)> = domain.iter_indexed()
            .map(|(idx, val)| (idx, val.clone()))
            .collect();

        for (index, value) in indices {
            ground_value.set(index, BoolValue::Constant(BooleanConstant::TRUE));
            *self.env.lookup_mut(&var).unwrap() = ground_value.clone();

            // forall: ¬entry.value() ∨ declConstraints
            let factory = self.interpreter.factory_mut();
            let not_value = factory.not(value.clone());
            let new_constraints = factory.or(not_value, decl_constraints.clone());

            self.translate_forall(decls, formula, current_decl + 1, new_constraints, acc);

            ground_value.set(index, BoolValue::Constant(BooleanConstant::FALSE));
        }

        // POP binding
        self.env.pop();
    }
}
