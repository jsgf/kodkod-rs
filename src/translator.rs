//! FOL to Boolean circuit translation
//!
//! Translates first-order relational logic formulas to boolean circuits.
//! Following Java: kodkod.engine.fol2sat.FOL2BoolTranslator

mod leaf_interpreter;
mod environment;

pub use leaf_interpreter::LeafInterpreter;
pub use environment::Environment;

use crate::ast::*;
use crate::bool::{BoolValue, BooleanConstant, BooleanMatrix, Dimensions, Int, Options};
use crate::instance::Bounds;
use std::cell::RefCell;

/// Result of translating a formula to a boolean circuit
///
/// Wraps both the interpreter and the resulting value together to maintain the invariant
/// that BoolValue must always be associated with its corresponding interpreter/arena.
pub struct TranslationResult {
    interpreter: LeafInterpreter,
    value: BoolValue<'static>,
}

impl TranslationResult {
    /// Returns a reference to the interpreter (for solution extraction)
    pub fn interpreter(&self) -> &LeafInterpreter {
        &self.interpreter
    }

    /// Returns a reference to the boolean circuit value
    /// The lifetime is tied to the result, ensuring the value cannot be separated from the interpreter
    pub fn value(&self) -> &BoolValue<'_> {
        &self.value
    }
}

/// Result of approximating a formula as a boolean matrix
///
/// Wraps both the interpreter and the resulting matrix together to maintain the invariant
/// that BooleanMatrix must always be associated with its corresponding interpreter/arena.
pub struct ApproximationResult {
    interpreter: LeafInterpreter,
    matrix: BooleanMatrix<'static>,
}

impl ApproximationResult {
    /// Returns a reference to the interpreter
    pub fn interpreter(&self) -> &LeafInterpreter {
        &self.interpreter
    }

    /// Returns a reference to the boolean matrix
    /// The lifetime is tied to the result, ensuring the matrix cannot be separated from the interpreter
    pub fn matrix(&self) -> &BooleanMatrix<'_> {
        &self.matrix
    }
}

/// Translator for FOL formulas to boolean circuits
pub struct Translator;

impl Translator {
    /// Evaluates a formula to a boolean circuit with its interpreter
    /// Following Java: Translator.translate()
    ///
    /// Returns a TranslationResult that wraps both the interpreter and circuit together,
    /// ensuring their lifetimes are tied and cannot be separated.
    pub fn evaluate(formula: &Formula, bounds: &Bounds, options: &Options) -> TranslationResult {
        let interpreter = LeafInterpreter::from_bounds(bounds, options);

        let value = {
            let translator = FOL2BoolTranslator::new(&interpreter);
            translator.translate_formula(formula)
        };

        // SAFETY: The value contains no borrows - all BoolValue variants are either Constants,
        // Variables, or Formulas with handles to arena data. The arena is owned by the factory
        // which is owned by the interpreter in the result. We transmute to 'static since the
        // data will outlive any intermediate borrows.
        let value_static = unsafe {
            std::mem::transmute::<BoolValue, BoolValue<'static>>(value)
        };

        TranslationResult {
            interpreter,
            value: value_static,
        }
    }

    /// Approximates a formula as a boolean matrix (not used in main solver)
    pub fn approximate(_formula: &Formula, bounds: &Bounds, options: &Options) -> ApproximationResult {
        let interpreter = LeafInterpreter::from_bounds(bounds, options);
        let capacity = bounds.universe().size();
        let dims = Dimensions::new(1, capacity);

        let matrix = {
            let factory = interpreter.factory();
            factory.matrix(dims)
        };

        // SAFETY: Same as evaluate() - matrix contains no direct borrows, only handles to arena data
        let matrix_static = unsafe {
            std::mem::transmute::<BooleanMatrix, BooleanMatrix<'static>>(matrix)
        };

        ApproximationResult {
            interpreter,
            matrix: matrix_static,
        }
    }
}

/// FOL to Boolean translator
/// Following Java: FOL2BoolTranslator
struct FOL2BoolTranslator<'a> {
    interpreter: &'a LeafInterpreter,
    env: RefCell<Environment<'a>>,
}

impl<'a> FOL2BoolTranslator<'a> {
    fn new(interpreter: &'a LeafInterpreter) -> Self {
        Self {
            interpreter,
            env: RefCell::new(Environment::empty()),
        }
    }

    /// Main entry point: translate a formula to a boolean value
    /// Following Java: FOL2BoolTranslator visitor methods
    fn translate_formula(&self, formula: &Formula) -> BoolValue<'a> {
        match formula {
            Formula::Constant(b) => {
                self.interpreter.factory().constant(*b)
            }

            Formula::Binary { left, op, right } => {
                let l = self.translate_formula(left);
                let r = self.translate_formula(right);
                let factory = self.interpreter.factory();
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

                let factory = self.interpreter.factory();
                match op {
                    BinaryFormulaOp::And => factory.and_multi(translated),
                    BinaryFormulaOp::Or => factory.or_multi(translated),
                    _ => factory.constant(true),
                }
            }

            Formula::Not(inner) => {
                let val = self.translate_formula(inner);
                self.interpreter.factory().not(val)
            }

            Formula::Comparison { left, right, op } => {
                let (left_matrix, right_matrix) = {
                    (self.translate_expression(left), self.translate_expression(right))
                };
                let factory = self.interpreter.factory();

                match op {
                    CompareOp::Equals => left_matrix.equals(&right_matrix, factory),
                    CompareOp::Subset => left_matrix.subset(&right_matrix, factory),
                }
            }

            Formula::Multiplicity { mult, expr } => {
                let matrix = self.translate_expression(expr);
                let factory = self.interpreter.factory();
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

            Formula::IntComparison { left, op, right } => {
                let (left_int, right_int) = {
                    (self.translate_int_expr(left), self.translate_int_expr(right))
                };
                let factory = self.interpreter.factory();

                match op {
                    IntCompareOp::Eq => left_int.eq(&right_int, factory),
                    IntCompareOp::Lt => left_int.lt(&right_int, factory),
                    IntCompareOp::Lte => left_int.lte(&right_int, factory),
                    IntCompareOp::Gt => right_int.lt(&left_int, factory),
                    IntCompareOp::Gte => right_int.lte(&left_int, factory),
                }
            }
        }
    }

    /// Expression translation
    /// Following Java: FOL2BoolTranslator.visit(Expression)
    fn translate_expression(&self, expr: &Expression) -> BooleanMatrix<'a> {
        match expr {
            Expression::Relation(rel) => {
                self.interpreter.interpret_relation(rel)
            }

            Expression::Variable(var) => {
                self.env.borrow().lookup(var)
                    .cloned()
                    .unwrap_or_else(|| panic!("Unbound variable: {}", var.name()))
            }

            Expression::Constant(c) => {
                self.interpreter.interpret_constant(*c)
            }

            Expression::Binary { left, op, right, .. } => {
                let (left_matrix, right_matrix) = {
                    (self.translate_expression(left), self.translate_expression(right))
                };
                let factory = self.interpreter.factory();

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
                let factory = self.interpreter.factory();
                match op {
                    UnaryOp::Transpose => {
                        let matrix = self.translate_expression(expr);
                        matrix.transpose(factory)
                    }
                    UnaryOp::Closure => {
                        let matrix = self.translate_expression(expr);
                        matrix.closure(factory)
                    }
                    UnaryOp::ReflexiveClosure => {
                        let matrix = self.translate_expression(expr);
                        let iden = self.interpreter.interpret_constant(ConstantExpr::Iden);
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
                    let factory = self.interpreter.factory();
                    result = result.union(&matrix, factory);
                }
                result
            }
        }
    }

    /// Quantifier translation
    /// Following Java: FOL2BoolTranslator.visit(QuantifiedFormula)
    fn translate_quantified(
        &self,
        quantifier: Quantifier,
        declarations: &Decls,
        body: &Formula
    ) -> BoolValue<'a> {
        match quantifier {
            Quantifier::Some => {
                let mut acc = Vec::new();
                self.translate_exists(declarations, body, 0,
                                     BoolValue::Constant(BooleanConstant::TRUE),
                                     &mut acc);
                self.interpreter.factory().or_multi(acc)
            }
            Quantifier::All => {
                let mut acc = Vec::new();
                self.translate_forall(declarations, body, 0,
                                     BoolValue::Constant(BooleanConstant::FALSE),
                                     &mut acc);
                self.interpreter.factory().and_multi(acc)
            }
        }
    }

    /// Existential quantification (FOLLOWING JAVA EXACTLY)
    /// Following Java: FOL2BoolTranslator.some(...)
    fn translate_exists(
        &self,
        decls: &Decls,
        formula: &Formula,
        current_decl: usize,
        decl_constraints: BoolValue<'a>,
        acc: &mut Vec<BoolValue<'a>>
    ) {
        // Base case: all variables bound
        if current_decl >= decls.size() {
            let formula_val = self.translate_formula(formula);
            let factory = self.interpreter.factory();
            let result = factory.and(decl_constraints.clone(), formula_val);
            acc.push(result);
            return;
        }

        // Get current declaration
        let decl = decls.iter().nth(current_decl).unwrap();
        let var = decl.variable();
        let domain = self.translate_expression(decl.expression());

        // Create ground matrix for this variable
        let mut ground_value = self.interpreter.factory().matrix(*domain.dimensions());

        // PUSH binding
        self.env.borrow_mut().extend(var.clone(), ground_value.clone());

        // ITERATE over each tuple in domain
        let indices: Vec<(usize, BoolValue)> = domain.iter_indexed()
            .map(|(idx, val)| (idx, val.clone()))
            .collect();

        for (index, value) in indices {
            // Set this index to TRUE
            ground_value.set(index, BoolValue::Constant(BooleanConstant::TRUE));

            // Update environment
            *self.env.borrow_mut().lookup_mut(&var).unwrap() = ground_value.clone();

            // Recurse with updated constraints
            let factory = self.interpreter.factory();
            let new_constraints = factory.and(value.clone(), decl_constraints.clone());

            self.translate_exists(decls, formula, current_decl + 1, new_constraints, acc);

            // Reset this index to FALSE
            ground_value.set(index, BoolValue::Constant(BooleanConstant::FALSE));
        }

        // POP binding
        self.env.borrow_mut().pop();
    }

    /// Universal quantification (FOLLOWING JAVA EXACTLY)
    /// Following Java: FOL2BoolTranslator.all(...)
    fn translate_forall(
        &self,
        decls: &Decls,
        formula: &Formula,
        current_decl: usize,
        decl_constraints: BoolValue<'a>,
        acc: &mut Vec<BoolValue<'a>>
    ) {
        // Base case: all variables bound
        if current_decl >= decls.size() {
            let formula_val = self.translate_formula(formula);
            let factory = self.interpreter.factory();
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
        let mut ground_value = self.interpreter.factory().matrix(*domain.dimensions());

        // PUSH binding
        self.env.borrow_mut().extend(var.clone(), ground_value.clone());

        // ITERATE
        let indices: Vec<(usize, BoolValue)> = domain.iter_indexed()
            .map(|(idx, val)| (idx, val.clone()))
            .collect();

        for (index, value) in indices {
            ground_value.set(index, BoolValue::Constant(BooleanConstant::TRUE));
            *self.env.borrow_mut().lookup_mut(&var).unwrap() = ground_value.clone();

            // forall: ¬entry.value() ∨ declConstraints
            let factory = self.interpreter.factory();
            let not_value = factory.not(value.clone());
            let new_constraints = factory.or(not_value, decl_constraints.clone());

            self.translate_forall(decls, formula, current_decl + 1, new_constraints, acc);

            ground_value.set(index, BoolValue::Constant(BooleanConstant::FALSE));
        }

        // POP binding
        self.env.borrow_mut().pop();
    }

    /// Integer expression translation
    /// Following Java: FOL2BoolTranslator integer expression handling
    fn translate_int_expr(&self, expr: &IntExpression) -> Int<'a> {
        match expr {
            IntExpression::Constant(c) => {
                let factory = self.interpreter.factory();
                let one_bit = BoolValue::Constant(BooleanConstant::TRUE);
                Int::constant(*c, factory.bitwidth(), one_bit)
            }

            IntExpression::Cardinality(set_expr) => {
                // Count the number of tuples in the set expression using a popcount circuit
                let matrix = self.translate_expression(set_expr);
                let factory = self.interpreter.factory();
                matrix.popcount(factory)
            }

            IntExpression::Binary { left, op, right } => {
                let left_int = self.translate_int_expr(left);
                let right_int = self.translate_int_expr(right);
                let factory = self.interpreter.factory();

                match op {
                    IntBinaryOp::Plus => left_int.plus(&right_int, factory),
                    IntBinaryOp::Minus => left_int.minus(&right_int, factory),
                    IntBinaryOp::And => left_int.and(&right_int, factory),
                    IntBinaryOp::Or => left_int.or(&right_int, factory),
                    IntBinaryOp::Xor => left_int.xor(&right_int, factory),
                    IntBinaryOp::Shl => {
                        // Shift left by constant amount
                        if let IntExpression::Constant(shift_amt) = &**right {
                            if *shift_amt >= 0 {
                                left_int.shift_left(*shift_amt as usize)
                            } else {
                                left_int // Invalid shift amount
                            }
                        } else {
                            // Dynamic shift not yet supported
                            left_int
                        }
                    }
                    IntBinaryOp::Shr => {
                        // Arithmetic right shift by constant
                        if let IntExpression::Constant(shift_amt) = &**right {
                            if *shift_amt >= 0 {
                                left_int.shift_right_arithmetic(*shift_amt as usize)
                            } else {
                                left_int
                            }
                        } else {
                            left_int
                        }
                    }
                    IntBinaryOp::Sha => {
                        // Logical right shift by constant
                        if let IntExpression::Constant(shift_amt) = &**right {
                            if *shift_amt >= 0 {
                                left_int.shift_right(*shift_amt as usize)
                            } else {
                                left_int
                            }
                        } else {
                            left_int
                        }
                    }
                    IntBinaryOp::Multiply => {
                        // Multiplication not yet fully implemented in Int
                        // For now, fallback to constant evaluation if possible
                        if let (Some(lv), Some(rv)) = (left_int.value(), right_int.value()) {
                            let product = lv.wrapping_mul(rv);
                            let one_bit = BoolValue::Constant(BooleanConstant::TRUE);
                            Int::constant(product, factory.bitwidth(), one_bit)
                        } else {
                            left_int // Unsupported
                        }
                    }
                    IntBinaryOp::Divide | IntBinaryOp::Modulo => {
                        // Division/modulo not implemented
                        if let (Some(lv), Some(rv)) = (left_int.value(), right_int.value()) {
                            let result = match op {
                                IntBinaryOp::Divide if rv != 0 => lv / rv,
                                IntBinaryOp::Modulo if rv != 0 => lv % rv,
                                _ => 0,
                            };
                            let one_bit = BoolValue::Constant(BooleanConstant::TRUE);
                            Int::constant(result, factory.bitwidth(), one_bit)
                        } else {
                            left_int
                        }
                    }
                }
            }

            IntExpression::Unary { op, expr } => {
                let int_val = self.translate_int_expr(expr);
                let factory = self.interpreter.factory();

                match op {
                    IntUnaryOp::Negate => int_val.negate(factory),
                    IntUnaryOp::Not => int_val.not(factory),
                    IntUnaryOp::Abs => int_val.abs(factory),
                    IntUnaryOp::Sgn => int_val.sign(factory),
                }
            }

            IntExpression::If { condition, then_expr, else_expr } => {
                let cond_val = self.translate_formula(condition);
                let then_int = self.translate_int_expr(then_expr);
                let else_int = self.translate_int_expr(else_expr);
                let factory = self.interpreter.factory();

                // Build result bit-by-bit using ite
                let mut result_bits = Vec::new();
                for i in 0..then_int.width().max(else_int.width()) {
                    let then_bit = then_int.bit(i);
                    let else_bit = else_int.bit(i);
                    let result_bit = factory.ite(cond_val.clone(), then_bit, else_bit);
                    result_bits.push(result_bit);
                }
                Int::new(result_bits)
            }

            IntExpression::Nary { exprs } => {
                // N-ary sum
                if exprs.is_empty() {
                    let factory = self.interpreter.factory();
                    let one_bit = BoolValue::Constant(BooleanConstant::TRUE);
                    return Int::constant(0, factory.bitwidth(), one_bit);
                }

                let mut result = self.translate_int_expr(&exprs[0]);
                for expr in &exprs[1..] {
                    let int_val = self.translate_int_expr(expr);
                    let factory = self.interpreter.factory();
                    result = result.plus(&int_val, factory);
                }
                result
            }

            IntExpression::Sum { .. } => {
                // Sum over declarations not yet supported
                let factory = self.interpreter.factory();
                let one_bit = BoolValue::Constant(BooleanConstant::TRUE);
                Int::constant(0, factory.bitwidth(), one_bit)
            }

            IntExpression::ExprCast(_) => {
                // Cast expression not yet supported
                let factory = self.interpreter.factory();
                let one_bit = BoolValue::Constant(BooleanConstant::TRUE);
                Int::constant(0, factory.bitwidth(), one_bit)
            }
        }
    }
}
