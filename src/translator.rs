//! FOL to Boolean circuit translation
//!
//! Translates first-order relational logic formulas to boolean circuits.
//! Following Java: kodkod.engine.fol2sat.FOL2BoolTranslator

mod leaf_interpreter;
mod environment;
mod cache;

pub use leaf_interpreter::LeafInterpreter;
pub use environment::Environment;

use cache::TranslationCache;
use crate::ast::*;
use crate::bool::{BoolValue, BooleanConstant, BooleanMatrix, Dimensions, Int, Options};
use crate::instance::{Bounds, Instance};
use rustc_hash::FxHashMap;
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
    pub fn evaluate(
        formula: &Formula,
        bounds: &Bounds,
        options: &Options,
        symmetry_breaking: i32,
    ) -> TranslationResult {
        let interpreter = LeafInterpreter::from_bounds(bounds, options);

        // Build translation cache with shared node detection and free variable analysis
        // Following Java: FOL2BoolCache built from AnnotatedNode
        let cache = TranslationCache::new(formula);

        let value = {
            let translator = FOL2BoolTranslator::with_cache(&interpreter, cache);
            let mut circuit = translator.translate_formula(formula);

            // Generate and conjoin symmetry breaking predicate if enabled
            if symmetry_breaking > 0 {
                let mut breaker = crate::engine::SymmetryBreaker::new(bounds.clone());
                let sbp = breaker.generate_sbp(&interpreter, symmetry_breaking);
                let factory = interpreter.factory();
                circuit = factory.and(circuit, sbp);
            }

            circuit
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

    /// Approximates an expression as a boolean matrix
    /// This is used for computing upper bounds for Skolem relations
    /// Following Java: FOL2BoolTranslator.approximate()
    pub fn approximate_expression(
        expr: &Expression,
        bounds: &Bounds,
        options: &Options,
    ) -> Vec<usize> {
        Self::approximate_expression_with_env(expr, bounds, options, None)
    }

    /// Approximates an expression with an optional environment for variable bindings
    /// Following Java: FOL2BoolTranslator.approximate(Expression, LeafInterpreter, Environment)
    pub fn approximate_expression_with_env(
        expr: &Expression,
        bounds: &Bounds,
        options: &Options,
        env: Option<&BooleanMatrix<'_>>,
    ) -> Vec<usize> {
        let interpreter = LeafInterpreter::from_bounds(bounds, options);
        let translator = FOL2BoolTranslator::new(&interpreter);

        // If an environment is provided, we need to use it
        // For now, if env is provided but we can't use it, return empty (conservative)
        if env.is_some() {
            // TODO: Implement environment parameter passing
            // For now, return empty to trigger conservative bounds
            return Vec::new();
        }

        let matrix = translator.translate_expression(expr);
        matrix.dense_indices()
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

    /// Evaluates a formula against an instance
    /// Following Java: Translator.evaluate(Formula, Instance, Options)
    ///
    /// Returns the boolean value of the formula with respect to the instance.
    pub fn evaluate_formula(formula: &Formula, instance: &Instance, options: &Options) -> bool {
        let interpreter = LeafInterpreter::from_instance(instance, options);
        let translator = FOL2BoolTranslator::new(&interpreter);
        let value = translator.translate_formula(formula);

        // For evaluation against an instance, all values should reduce to constants
        // since there are no variables
        match value {
            BoolValue::Constant(c) => c.boolean_value(),
            _ => panic!("Expected constant value when evaluating against instance"),
        }
    }

    /// Evaluates an expression against an instance
    /// Following Java: Translator.evaluate(Expression, Instance, Options)
    ///
    /// Returns the tuple indices (as a vector) that the expression evaluates to.
    /// The caller should convert these to a TupleSet using TupleFactory.setOf()
    pub fn evaluate_expression(expr: &Expression, instance: &Instance, options: &Options) -> Vec<usize> {
        let interpreter = LeafInterpreter::from_instance(instance, options);
        let translator = FOL2BoolTranslator::new(&interpreter);
        let matrix = translator.translate_expression(expr);
        matrix.dense_indices()
    }

    /// Evaluates an integer expression against an instance
    /// Following Java: Translator.evaluate(IntExpression, Instance, Options)
    ///
    /// Returns the integer value that the expression evaluates to with respect to the instance.
    pub fn evaluate_int_expression(expr: &IntExpression, instance: &Instance, options: &Options) -> i32 {
        let interpreter = LeafInterpreter::from_instance(instance, options);
        let translator = FOL2BoolTranslator::new(&interpreter);
        let int_value = translator.translate_int_expr(expr);
        int_value
            .value()
            .expect("IntExpression should evaluate to a constant when evaluated against an instance")
    }
}

/// FOL to Boolean translator
/// Following Java: FOL2BoolTranslator
struct FOL2BoolTranslator<'a> {
    interpreter: &'a LeafInterpreter,
    env: RefCell<Environment<'a>>,
    // Leaf caching: cache relation and constant interpretations
    relation_cache: RefCell<FxHashMap<Relation, BooleanMatrix<'a>>>,
    constant_cache: RefCell<FxHashMap<ConstantExpr, BooleanMatrix<'a>>>,
    // Full translation cache with free variable tracking
    // Following Java: FOL2BoolCache with NoVarRecord/MultiVarRecord
    cache: RefCell<TranslationCache<'a>>,
}

impl<'a> FOL2BoolTranslator<'a> {
    fn new(interpreter: &'a LeafInterpreter) -> Self {
        Self {
            interpreter,
            env: RefCell::new(Environment::empty()),
            relation_cache: RefCell::new(FxHashMap::default()),
            constant_cache: RefCell::new(FxHashMap::default()),
            cache: RefCell::new(TranslationCache::empty()),
        }
    }

    fn with_cache(interpreter: &'a LeafInterpreter, cache: TranslationCache<'a>) -> Self {
        Self {
            interpreter,
            env: RefCell::new(Environment::empty()),
            relation_cache: RefCell::new(FxHashMap::default()),
            constant_cache: RefCell::new(FxHashMap::default()),
            cache: RefCell::new(cache),
        }
    }

    /// Main entry point: translate a formula to a boolean value
    /// Following Java: FOL2BoolTranslator visitor methods
    fn translate_formula(&self, formula: &Formula) -> BoolValue<'a> {
        // Check translation cache (handles both shared nodes and free variables)
        // Following Java: FOL2BoolCache.lookup()
        {
            let env = self.env.borrow();
            if let Some(cached) = self.cache.borrow().lookup_formula(formula, &env) {
                return cached;
            }
        }

        let result = self.translate_formula_inner(formula);

        // Cache the result
        {
            let env = self.env.borrow();
            self.cache.borrow_mut().cache_formula(formula, result.clone(), &env);
        }

        result
    }

    /// Inner formula translation (no caching)
    fn translate_formula_inner(&self, formula: &Formula) -> BoolValue<'a> {
        match &*formula.inner() {
            FormulaInner::Constant(b) => {
                self.interpreter.factory().constant(*b)
            }

            FormulaInner::Binary { left, op, right } => {
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

            FormulaInner::Nary { op, formulas } => {
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

            FormulaInner::Not(inner) => {
                let val = self.translate_formula(inner);
                self.interpreter.factory().not(val)
            }

            FormulaInner::Comparison { left, right, op } => {
                let (left_matrix, right_matrix) = {
                    (self.translate_expression(left), self.translate_expression(right))
                };
                let factory = self.interpreter.factory();

                match op {
                    CompareOp::Equals => left_matrix.equals(&right_matrix, factory),
                    CompareOp::Subset => left_matrix.subset(&right_matrix, factory),
                }
            }

            FormulaInner::Multiplicity { mult, expr } => {
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
                    Multiplicity::Set => {
                        // Set multiplicity as a formula constraint would mean the expression
                        // can be any subset, which is always true
                        factory.constant(true)
                    }
                }
            }

            FormulaInner::Quantified { quantifier, declarations, body } => {
                self.translate_quantified(*quantifier, declarations, body)
            }

            FormulaInner::IntComparison { left, op, right } => {
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

            FormulaInner::RelationPredicate(pred) => {
                // Convert predicate to explicit constraints and translate
                let constraints = pred.to_constraints();
                self.translate_formula(&constraints)
            }
        }
    }

    /// Expression translation
    /// Following Java: FOL2BoolTranslator.visit(Expression)
    fn translate_expression(&self, expr: &Expression) -> BooleanMatrix<'a> {
        // Check translation cache (handles both shared nodes and free variables)
        // Following Java: FOL2BoolCache.lookup()
        {
            let env = self.env.borrow();
            if let Some(cached) = self.cache.borrow().lookup_expr(expr, &env) {
                return cached;
            }
        }

        let result = self.translate_expression_inner(expr);

        // Cache the result
        {
            let env = self.env.borrow();
            self.cache.borrow_mut().cache_expr(expr, result.clone(), &env);
        }

        result
    }

    /// Inner expression translation (no caching)
    fn translate_expression_inner(&self, expr: &Expression) -> BooleanMatrix<'a> {
        match &*expr.inner() {
            ExpressionInner::Relation(rel) => {
                // Check cache first
                if let Some(cached) = self.relation_cache.borrow().get(rel) {
                    return cached.clone();
                }

                // Interpret and cache
                let matrix = self.interpreter.interpret_relation(rel);
                self.relation_cache.borrow_mut().insert(rel.clone(), matrix.clone());
                matrix
            }

            ExpressionInner::Variable(var) => {
                self.env.borrow().lookup(var)
                    .cloned()
                    .unwrap_or_else(|| panic!("Unbound variable: {}", var.name()))
            }

            ExpressionInner::Constant(c) => {
                // Check cache first
                if let Some(cached) = self.constant_cache.borrow().get(c) {
                    return cached.clone();
                }

                // Interpret and cache
                let matrix = self.interpreter.interpret_constant(*c);
                self.constant_cache.borrow_mut().insert(*c, matrix.clone());
                matrix
            }

            ExpressionInner::Binary { left, op, right, .. } => {
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

            ExpressionInner::Unary { op, expr } => {
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

            ExpressionInner::Nary { exprs, .. } => {
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

            ExpressionInner::Comprehension { declarations, formula } => {
                // { decls | formula }
                let usize = self.interpreter.universe().size();
                let dims = Dimensions::square(usize, declarations.size());
                let mut result = self.interpreter.factory().matrix(dims);
                self.translate_comprehension(declarations, formula,0,
                    BoolValue::Constant(BooleanConstant::TRUE), 0, &mut result);
                result
            }
            ExpressionInner::IntToExprCast { int_expr, op } => {
                // Convert integer expression to relational expression
                use crate::ast::IntCastOp;
                let int_value = self.translate_int_expr(int_expr);
                match op {
                    IntCastOp::IntCast => {
                        // Singleton set containing the atom for this integer
                        self.interpret_int_value_as_set(int_value)
                    }
                    IntCastOp::BitsetCast => {
                        // Set of powers of 2 (bits) in this integer
                        self.interpret_int_value_as_bitset(int_value)
                    }
                }
            }
            ExpressionInner::If { condition, then_expr, else_expr, .. } => {
                // If-then-else expression
                // Following Java: FOL2BoolTranslator.visit(IfExpression)
                let condition_val = self.translate_formula(condition);
                let then_matrix = self.translate_expression(then_expr);
                let else_matrix = self.translate_expression(else_expr);
                then_matrix.choice(condition_val, &else_matrix, self.interpreter.factory())
            }
        }
    }

    /// Convert an integer value to a set containing the atom for that integer
    /// Following Java: FOL2BoolTranslator.visit(IntToExprCast) with INTCAST operator
    fn interpret_int_value_as_set(&self, int_value: Int<'a>) -> BooleanMatrix<'a> {
        let factory = self.interpreter.factory();
        let usize = self.interpreter.universe().size();
        let dims = Dimensions::square(usize, 1);
        let mut ret = factory.matrix(dims);

        // For each integer atom i in the universe, set result[interpret(i)] = (int_value == i)
        for i in self.interpreter.ints() {
            let atom_index = self.interpreter.interpret(i);
            let i_const = factory.integer(i);
            let is_equal = int_value.eq(&i_const, factory);
            // ret[atom_index] = ret[atom_index] || (int_value == i)
            let current = ret.get(atom_index);
            ret.set(atom_index, factory.or(current, is_equal));
        }

        ret
    }

    /// Convert an integer value to a set of power-of-2 atoms (bitset representation)
    /// Following Java: FOL2BoolTranslator.visit(IntToExprCast) with BITSETCAST operator
    fn interpret_int_value_as_bitset(&self, int_value: Int<'a>) -> BooleanMatrix<'a> {
        let factory = self.interpreter.factory();
        let usize = self.interpreter.universe().size();
        let dims = Dimensions::square(usize, 1);
        let mut ret = factory.matrix(dims);

        let twos_complement = int_value.twos_complement_bits();
        let msb = twos_complement.len() - 1;

        // Handle all bits but the sign bit
        for i in 0..msb {
            let pow2 = 1 << i;
            // Check if this power of 2 is in the integer atoms
            if self.interpreter.ints().any(|x| x == pow2) {
                let atom_index = self.interpreter.interpret(pow2);
                ret.set(atom_index, twos_complement[i].clone());
            }
        }

        // Handle the sign bit
        let sign_bit_value = -(1 << msb);
        if self.interpreter.ints().any(|x| x == sign_bit_value) {
            let atom_index = self.interpreter.interpret(sign_bit_value);
            ret.set(atom_index, twos_complement[msb].clone());
        }

        ret
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
                let mut acc = None;
                self.translate_exists(declarations, body, 0,
                                     BoolValue::Constant(BooleanConstant::TRUE),
                                     &mut acc);
                acc.unwrap_or(BoolValue::Constant(BooleanConstant::FALSE))
            }
            Quantifier::All => {
                let mut acc = None;
                self.translate_forall(declarations, body, 0,
                                     BoolValue::Constant(BooleanConstant::FALSE),
                                     &mut acc);
                acc.unwrap_or(BoolValue::Constant(BooleanConstant::TRUE))
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
        acc: &mut Option<BoolValue<'a>>
    ) {
        // Short-circuit: if we've already found TRUE, stop
        if let Some(BoolValue::Constant(BooleanConstant::TRUE)) = acc {
            return;
        }

        // Base case: all variables bound
        if current_decl >= decls.size() {
            let formula_val = self.translate_formula(formula);
            let factory = self.interpreter.factory();
            let result = factory.and(decl_constraints.clone(), formula_val);

            // Accumulate with OR: acc = acc OR result
            *acc = Some(match acc.take() {
                None => result,
                Some(prev) => factory.or(prev, result)
            });
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
            // Short-circuit check
            if let Some(BoolValue::Constant(BooleanConstant::TRUE)) = acc {
                break;
            }

            // Set this index to TRUE
            ground_value.set(index, BoolValue::Constant(BooleanConstant::TRUE));

            // Update environment
            *self.env.borrow_mut().lookup_mut(var).unwrap() = ground_value.clone();

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
        acc: &mut Option<BoolValue<'a>>
    ) {
        // Short-circuit: if we've already found FALSE, stop
        if let Some(BoolValue::Constant(BooleanConstant::FALSE)) = acc {
            return;
        }

        // Base case: all variables bound
        if current_decl >= decls.size() {
            let formula_val = self.translate_formula(formula);
            let factory = self.interpreter.factory();
            // forall: decl_constraints ∨ formula
            // (NOT following my earlier comment - following Java exactly)
            let result = factory.or(decl_constraints.clone(), formula_val);

            // Accumulate with AND: acc = acc AND result
            *acc = Some(match acc.take() {
                None => result,
                Some(prev) => factory.and(prev, result)
            });
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
            // Short-circuit check
            if let Some(BoolValue::Constant(BooleanConstant::FALSE)) = acc {
                break;
            }

            ground_value.set(index, BoolValue::Constant(BooleanConstant::TRUE));
            *self.env.borrow_mut().lookup_mut(var).unwrap() = ground_value.clone();

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

    /// Comprehension translation
    /// Following Java: FOL2BoolTranslator.comprehension(...)
    /// Translates { decls | formula } to a boolean matrix
    fn translate_comprehension(
        &self,
        decls: &Decls,
        formula: &Formula,
        current_decl: usize,
        decl_constraints: BoolValue<'a>,
        partial_index: usize,
        matrix: &mut BooleanMatrix<'a>
    ) {
        let factory = self.interpreter.factory();

        // Base case: all variables bound, evaluate formula and set matrix cell
        if current_decl >= decls.size() {
            let formula_val = self.translate_formula(formula);
            let result = factory.and(decl_constraints.clone(), formula_val);
            matrix.set(partial_index, result);
            return;
        }

        // Get current declaration
        let decl = decls.iter().nth(current_decl).unwrap();
        let var = decl.variable();
        let domain = self.translate_expression(decl.expression());

        // Calculate position multiplier for this level
        let usize = self.interpreter.universe().size();
        let position = usize.pow((decls.size() - current_decl - 1) as u32);

        // Create ground matrix for this variable
        let mut ground_value = factory.matrix(*domain.dimensions());

        // PUSH binding
        self.env.borrow_mut().extend(var.clone(), ground_value.clone());

        // ITERATE over domain
        let indices: Vec<(usize, BoolValue)> = domain.iter_indexed()
            .map(|(idx, val)| (idx, val.clone()))
            .collect();

        for (index, value) in indices {
            // Set this index to TRUE
            ground_value.set(index, BoolValue::Constant(BooleanConstant::TRUE));

            // Update environment
            *self.env.borrow_mut().lookup_mut(var).unwrap() = ground_value.clone();

            // Recurse with updated constraints and partial index
            let new_constraints = factory.and(value.clone(), decl_constraints.clone());
            self.translate_comprehension(decls, formula, current_decl + 1,
                new_constraints, partial_index + index * position, matrix);

            // Reset this index to FALSE
            ground_value.set(index, BoolValue::Constant(BooleanConstant::FALSE));
        }

        // POP binding
        self.env.borrow_mut().pop();
    }

    /// Integer expression translation
    /// Following Java: FOL2BoolTranslator integer expression handling
    fn translate_int_expr(&self, expr: &IntExpression) -> Int<'a> {
        match expr.inner() {
            IntExpressionInner::Constant(c) => {
                let factory = self.interpreter.factory();
                let one_bit = BoolValue::Constant(BooleanConstant::TRUE);
                Int::constant(*c, factory.bitwidth(), one_bit)
            }

            IntExpressionInner::Cardinality(set_expr) => {
                // Count the number of tuples in the set expression using a popcount circuit
                let matrix = self.translate_expression(set_expr);
                let factory = self.interpreter.factory();
                matrix.popcount(factory)
            }

            IntExpressionInner::Binary { left, op, right } => {
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
                        if let IntExpressionInner::Constant(shift_amt) = right.inner() {
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
                        if let IntExpressionInner::Constant(shift_amt) = right.inner() {
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
                        if let IntExpressionInner::Constant(shift_amt) = right.inner() {
                            if *shift_amt >= 0 {
                                left_int.shift_right(*shift_amt as usize)
                            } else {
                                left_int
                            }
                        } else {
                            left_int
                        }
                    }
                    IntBinaryOp::Multiply => left_int.multiply(&right_int, factory),
                    IntBinaryOp::Divide => left_int.divide(&right_int, factory),
                    IntBinaryOp::Modulo => left_int.modulo(&right_int, factory),
                }
            }

            IntExpressionInner::Unary { op, expr } => {
                let int_val = self.translate_int_expr(expr);
                let factory = self.interpreter.factory();

                match op {
                    IntUnaryOp::Negate => int_val.negate(factory),
                    IntUnaryOp::Not => int_val.not(factory),
                    IntUnaryOp::Abs => int_val.abs(factory),
                    IntUnaryOp::Sgn => int_val.sign(factory),
                }
            }

            IntExpressionInner::If { condition, then_expr, else_expr } => {
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

            IntExpressionInner::Nary { exprs } => {
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

            IntExpressionInner::Sum { .. } => {
                // Sum over declarations not yet supported
                let factory = self.interpreter.factory();
                let one_bit = BoolValue::Constant(BooleanConstant::TRUE);
                Int::constant(0, factory.bitwidth(), one_bit)
            }

            IntExpressionInner::ExprCast(expr) => {
                // Following Java: FOL2BoolTranslator.visit(ExprToIntCast) for SUM operator
                // Translates expression and sums the integer values of its atoms
                let matrix = self.translate_expression(expr);
                let factory = self.interpreter.factory();

                // Collect all integers with bounds
                let ints: Vec<i32> = self.interpreter.ints().collect();

                if ints.is_empty() {
                    // No integers, return 0
                    return Int::constant(0, factory.bitwidth(), BoolValue::Constant(BooleanConstant::TRUE));
                }

                // Build sum recursively like Java implementation
                self.sum_helper(&matrix, &ints, 0, ints.len() - 1)
            }
        }
    }

    /// Helper method for computing sum of integer atoms in an expression
    /// Following Java: FOL2BoolTranslator.sum(BooleanMatrix, IntIterator, int, int)
    fn sum_helper(
        &self,
        matrix: &BooleanMatrix<'a>,
        ints: &[i32],
        low: usize,
        high: usize,
    ) -> Int<'a> {
        let factory = self.interpreter.factory();

        if low > high {
            // Empty range
            Int::constant(0, factory.bitwidth(), BoolValue::Constant(BooleanConstant::TRUE))
        } else if low == high {
            // Single integer
            let i = ints[low];
            let atom_index = self.interpreter.interpret(i);
            let condition = matrix.get(atom_index);
            // Create integer that equals i when condition is true, 0 otherwise
            Int::constant(i, factory.bitwidth(), condition)
        } else {
            // Recursively split and sum
            let mid = (low + high) / 2;
            let lsum = self.sum_helper(matrix, ints, low, mid);
            let hsum = self.sum_helper(matrix, ints, mid + 1, high);
            lsum.plus(&hsum, factory)
        }
    }
}
