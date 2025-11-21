//! Boolean factory with gate caching
//!
//! The factory creates boolean values and formulas, with automatic deduplication.
//! Uses interior mutability (Cell/RefCell) to avoid &mut self everywhere.

use super::{BoolValue, BooleanConstant, BooleanFormula, BooleanMatrix, BooleanVariable, Dimensions, FormulaKind, MatrixArena};
use rustc_hash::FxHashMap;
use std::cell::{Cell, RefCell};
use std::mem;

/// Options for boolean factory
#[derive(Debug, Clone)]
pub struct Options {
    /// Enable sharing of boolean formulas (default: true)
    pub sharing: bool,
    /// Bitwidth for integer encoding (default: 32)
    pub bitwidth: usize,
}

impl Default for Options {
    fn default() -> Self {
        Self {
            sharing: true,
            bitwidth: 32,
        }
    }
}

/// Boolean circuit factory with caching
///
/// Creates boolean values and formulas, with automatic deduplication of gates.
/// Uses interior mutability to allow creating gates through `&self`.
pub struct BooleanFactory {
    num_variables: u32,
    next_label: Cell<u32>,
    options: Options,
    // Cache for gate deduplication
    // Key: (kind, input labels) -> cached formula
    cache: RefCell<FxHashMap<CacheKey, BooleanFormula<'static>>>,
    bitwidth: usize,
    // Arena for allocating BoolValue handles
    arena: MatrixArena,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum CacheKey {
    And(Box<[i32]>),
    Or(Box<[i32]>),
    Not(i32),
    Ite(i32, i32, i32),
}

impl BooleanFactory {
    /// Creates a new boolean factory
    ///
    /// # Arguments
    /// * `num_variables` - Initial number of variables to allocate
    /// * `options` - Factory options
    pub fn new(num_variables: u32, options: Options) -> Self {
        Self {
            num_variables,
            // Start labels after variables (variables are 1..=num_variables)
            next_label: Cell::new(num_variables + 1),
            bitwidth: options.bitwidth,
            options,
            cache: RefCell::new(FxHashMap::default()),
            arena: MatrixArena::new(),
        }
    }

    /// Returns the number of variables
    pub fn num_variables(&self) -> u32 {
        self.num_variables
    }

    /// Returns a reference to the arena
    pub fn arena(&self) -> &MatrixArena {
        &self.arena
    }

    /// Fetches a cached formula, transmuting from 'static to the arena's lifetime
    /// This is the ONLY place where lifetime transmutation happens
    #[inline]
    fn cache_get<'arena>(&'arena self, key: &CacheKey) -> Option<BooleanFormula<'arena>> {
        self.cache.borrow().get(key).map(|f| {
            unsafe { mem::transmute::<BooleanFormula<'static>, BooleanFormula<'arena>>(f.clone()) }
        })
    }

    /// Inserts a formula into the cache, transmuting from arena's lifetime to 'static
    /// This is the ONLY place where lifetime transmutation happens
    #[inline]
    fn cache_insert<'arena>(&'arena self, key: CacheKey, formula: BooleanFormula<'arena>) {
        let static_formula = unsafe { mem::transmute::<BooleanFormula<'arena>, BooleanFormula<'static>>(formula) };
        self.cache.borrow_mut().insert(key, static_formula);
    }

    /// Creates a boolean variable
    pub fn variable<'arena>(&'arena self, label: i32) -> BoolValue<'arena> {
        assert!(label > 0 && label <= self.num_variables as i32,
                "Variable label must be in range 1..={}", self.num_variables);
        BoolValue::Variable(BooleanVariable::new(label))
    }

    /// Creates a constant
    pub fn constant<'arena>(&'arena self, value: bool) -> BoolValue<'arena> {
        BoolValue::Constant(if value {
            BooleanConstant::TRUE
        } else {
            BooleanConstant::FALSE
        })
    }

    /// Creates an AND gate
    pub fn and<'arena>(&'arena self, left: BoolValue<'arena>, right: BoolValue<'arena>) -> BoolValue<'arena> {
        self.and_multi(vec![left, right])
    }

    /// Creates a multi-input AND gate
    pub fn and_multi<'arena>(&'arena self, mut inputs: Vec<BoolValue<'arena>>) -> BoolValue<'arena> {
        if inputs.is_empty() {
            return self.constant(true);
        }
        if inputs.len() == 1 {
            return inputs.into_iter().next().unwrap();
        }

        // Check for trivial cases
        if inputs.iter().any(|v| matches!(v, BoolValue::Constant(BooleanConstant::FALSE))) {
            return self.constant(false);
        }

        // Remove TRUE constants
        inputs.retain(|v| !matches!(v, BoolValue::Constant(BooleanConstant::TRUE)));

        if inputs.is_empty() {
            return self.constant(true);
        }
        if inputs.len() == 1 {
            return inputs.into_iter().next().unwrap();
        }

        // Check for contradictions (p AND !p = FALSE)
        for i in 0..inputs.len() {
            for j in (i+1)..inputs.len() {
                // Check if inputs[j] is NOT(inputs[i]) or vice versa
                if let BoolValue::Formula(f) = &inputs[j] {
                    if let FormulaKind::Not(h) = f.kind() {
                        if self.arena.resolve_handle(*h) == &inputs[i] {
                            return self.constant(false);
                        }
                    }
                }
                if let BoolValue::Formula(f) = &inputs[i] {
                    if let FormulaKind::Not(h) = f.kind() {
                        if self.arena.resolve_handle(*h) == &inputs[j] {
                            return self.constant(false);
                        }
                    }
                }
            }
        }

        // Remove duplicates (idempotency: p AND p = p)
        inputs.sort_by_key(|v| v.label());
        inputs.dedup();

        if inputs.len() == 1 {
            return inputs.into_iter().next().unwrap();
        }

        // Check cache
        if self.options.sharing {
            let labels: Vec<i32> = inputs.iter().map(|v| v.label()).collect();
            let key = CacheKey::And(labels.into_boxed_slice());

            if let Some(cached) = self.cache_get(&key) {
                return BoolValue::Formula(cached);
            }

            // Create new formula - allocate inputs slice in arena
            let label = self.allocate_label();
            let handle = self.arena.alloc_slice_handle(&inputs);
            let formula = BooleanFormula::new(label, FormulaKind::And(handle));
            self.cache_insert(key, formula.clone());
            BoolValue::Formula(formula)
        } else {
            let label = self.allocate_label();
            let handle = self.arena.alloc_slice_handle(&inputs);
            BoolValue::Formula(BooleanFormula::new(label, FormulaKind::And(handle)))
        }
    }

    /// Creates an OR gate
    pub fn or<'arena>(&'arena self, left: BoolValue<'arena>, right: BoolValue<'arena>) -> BoolValue<'arena> {
        self.or_multi(vec![left, right])
    }

    /// Creates a multi-input OR gate
    pub fn or_multi<'arena>(&'arena self, mut inputs: Vec<BoolValue<'arena>>) -> BoolValue<'arena> {
        if inputs.is_empty() {
            return self.constant(false);
        }
        if inputs.len() == 1 {
            return inputs.into_iter().next().unwrap();
        }

        // Check for trivial cases
        if inputs.iter().any(|v| matches!(v, BoolValue::Constant(BooleanConstant::TRUE))) {
            return self.constant(true);
        }

        // Remove FALSE constants
        inputs.retain(|v| !matches!(v, BoolValue::Constant(BooleanConstant::FALSE)));

        if inputs.is_empty() {
            return self.constant(false);
        }
        if inputs.len() == 1 {
            return inputs.into_iter().next().unwrap();
        }

        // Check for excluded middle (p OR !p = TRUE)
        for i in 0..inputs.len() {
            for j in (i+1)..inputs.len() {
                // Check if inputs[j] is NOT(inputs[i]) or vice versa
                if let BoolValue::Formula(f) = &inputs[j] {
                    if let FormulaKind::Not(h) = f.kind() {
                        if self.arena.resolve_handle(*h) == &inputs[i] {
                            return self.constant(true);
                        }
                    }
                }
                if let BoolValue::Formula(f) = &inputs[i] {
                    if let FormulaKind::Not(h) = f.kind() {
                        if self.arena.resolve_handle(*h) == &inputs[j] {
                            return self.constant(true);
                        }
                    }
                }
            }
        }

        // Remove duplicates (idempotency: p OR p = p)
        inputs.sort_by_key(|v| v.label());
        inputs.dedup();

        if inputs.len() == 1 {
            return inputs.into_iter().next().unwrap();
        }

        // Check cache
        if self.options.sharing {
            let labels: Vec<i32> = inputs.iter().map(|v| v.label()).collect();
            let key = CacheKey::Or(labels.into_boxed_slice());

            if let Some(cached) = self.cache_get(&key) {
                return BoolValue::Formula(cached);
            }

            // Create new formula - allocate inputs slice in arena
            let label = self.allocate_label();
            let handle = self.arena.alloc_slice_handle(&inputs);
            let formula = BooleanFormula::new(label, FormulaKind::Or(handle));
            self.cache_insert(key, formula.clone());
            BoolValue::Formula(formula)
        } else {
            let label = self.allocate_label();
            let handle = self.arena.alloc_slice_handle(&inputs);
            BoolValue::Formula(BooleanFormula::new(label, FormulaKind::Or(handle)))
        }
    }

    /// Creates a NOT gate
    pub fn not<'arena>(&'arena self, input: BoolValue<'arena>) -> BoolValue<'arena> {
        // Check for trivial cases
        if let BoolValue::Constant(c) = input {
            return self.constant(match c {
                BooleanConstant::TRUE => false,
                BooleanConstant::FALSE => true,
            });
        }

        // Check cache
        if self.options.sharing {
            let key = CacheKey::Not(input.label());

            if let Some(cached) = self.cache_get(&key) {
                return BoolValue::Formula(cached);
            }

            // Create new formula - allocate input handle in arena
            let label = self.allocate_label();
            let handle = self.arena.alloc_handle(input.clone());
            let formula = BooleanFormula::new(label, FormulaKind::Not(handle));
            self.cache_insert(key, formula.clone());
            BoolValue::Formula(formula)
        } else {
            let label = self.allocate_label();
            let handle = self.arena.alloc_handle(input);
            BoolValue::Formula(BooleanFormula::new(label, FormulaKind::Not(handle)))
        }
    }

    /// Creates an if-then-else gate
    pub fn ite<'arena>(&'arena self, condition: BoolValue<'arena>, then_val: BoolValue<'arena>, else_val: BoolValue<'arena>) -> BoolValue<'arena> {
        // Check for trivial cases
        if let BoolValue::Constant(c) = condition {
            return match c {
                BooleanConstant::TRUE => then_val,
                BooleanConstant::FALSE => else_val,
            };
        }

        // If then and else are the same, return that value
        if then_val == else_val {
            return then_val;
        }

        // Check cache
        if self.options.sharing {
            let key = CacheKey::Ite(condition.label(), then_val.label(), else_val.label());

            if let Some(cached) = self.cache_get(&key) {
                return BoolValue::Formula(cached);
            }

            // Create new formula - allocate value handles in arena
            let label = self.allocate_label();
            let condition_handle = self.arena.alloc_handle(condition.clone());
            let then_handle = self.arena.alloc_handle(then_val.clone());
            let else_handle = self.arena.alloc_handle(else_val.clone());
            let formula = BooleanFormula::new(
                label,
                FormulaKind::Ite {
                    condition: condition_handle,
                    then_val: then_handle,
                    else_val: else_handle,
                },
            );
            self.cache_insert(key, formula.clone());
            BoolValue::Formula(formula)
        } else {
            let label = self.allocate_label();
            let condition_handle = self.arena.alloc_handle(condition);
            let then_handle = self.arena.alloc_handle(then_val);
            let else_handle = self.arena.alloc_handle(else_val);
            BoolValue::Formula(BooleanFormula::new(
                label,
                FormulaKind::Ite {
                    condition: condition_handle,
                    then_val: then_handle,
                    else_val: else_handle,
                },
            ))
        }
    }

    /// Creates an empty boolean matrix with the given dimensions
    /// Following Java: used for quantifier translation
    pub fn matrix<'arena>(&'arena self, dimensions: Dimensions) -> BooleanMatrix<'arena> {
        BooleanMatrix::empty(dimensions)
    }

    /// Returns the bitwidth used for integer operations
    pub fn bitwidth(&self) -> usize {
        self.bitwidth
    }

    /// XOR operation: a XOR b = (a AND NOT b) OR (NOT a AND b)
    pub fn xor<'arena>(&'arena self, a: BoolValue<'arena>, b: BoolValue<'arena>) -> BoolValue<'arena> {
        let not_b = self.not(b.clone());
        let a_and_not_b = self.and(a.clone(), not_b);

        let not_a = self.not(a);
        let not_a_and_b = self.and(not_a, b);

        self.or(a_and_not_b, not_a_and_b)
    }

    /// IFF (if and only if): a IFF b = (a AND b) OR (NOT a AND NOT b)
    pub fn iff<'arena>(&'arena self, a: BoolValue<'arena>, b: BoolValue<'arena>) -> BoolValue<'arena> {
        let a_and_b = self.and(a.clone(), b.clone());
        let not_a = self.not(a);
        let not_b = self.not(b);
        let not_a_and_not_b = self.and(not_a, not_b);
        self.or(a_and_b, not_a_and_not_b)
    }

    /// IMPLIES: a IMPLIES b = NOT a OR b
    pub fn implies<'arena>(&'arena self, a: BoolValue<'arena>, b: BoolValue<'arena>) -> BoolValue<'arena> {
        let not_a = self.not(a);
        self.or(not_a, b)
    }

    /// Full adder sum: a XOR b XOR cin
    /// Returns the sum bit (without carry)
    pub fn sum<'arena>(&'arena self, a: BoolValue<'arena>, b: BoolValue<'arena>, cin: BoolValue<'arena>) -> BoolValue<'arena> {
        let ab_xor = self.xor(a, b);
        self.xor(ab_xor, cin)
    }

    /// Full adder carry out: (a AND b) OR (cin AND (a XOR b))
    pub fn carry<'arena>(&'arena self, a: BoolValue<'arena>, b: BoolValue<'arena>, cin: BoolValue<'arena>) -> BoolValue<'arena> {
        let a_and_b = self.and(a.clone(), b.clone());
        let ab_xor = self.xor(a, b);
        let cin_and_xor = self.and(cin, ab_xor);
        self.or(a_and_b, cin_and_xor)
    }

    /// Creates an Int representing the given constant integer value
    /// Following Java: BooleanFactory.integer(int)
    pub fn integer<'arena>(&'arena self, value: i32) -> crate::bool::Int<'arena> {
        crate::bool::Int::constant(value, self.options.bitwidth, BoolValue::Constant(BooleanConstant::TRUE))
    }

    fn allocate_label(&self) -> i32 {
        let label = self.next_label.get();
        self.next_label.set(label + 1);
        label as i32
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn factory_creates_variables() {
        let factory = BooleanFactory::new(10, Options::default());
        assert_eq!(factory.num_variables(), 10);
    }

    #[test]
    fn factory_variable_creation() {
        let factory = BooleanFactory::new(5, Options::default());
        let v1 = factory.variable(1);
        let v2 = factory.variable(2);

        assert_eq!(v1.label(), 1);
        assert_eq!(v2.label(), 2);
        assert_ne!(v1, v2);
    }

    #[test]
    fn gate_deduplication() {
        let factory = BooleanFactory::new(5, Options::default());
        let v1 = factory.variable(1);
        let v2 = factory.variable(2);

        let and1 = factory.and(v1.clone(), v2.clone());
        let and2 = factory.and(v1.clone(), v2.clone());

        // Same gate instance due to caching
        assert_eq!(and1.label(), and2.label());
    }

    #[test]
    fn boolean_matrix() {
        let factory = BooleanFactory::new(10, Options::default());
        // Ternary relation over universe of size 2: capacity=8 (2³), arity=3
        let dims = Dimensions::new(8, 3);

        let matrix = factory.matrix(dims);

        assert_eq!(matrix.dimensions().capacity(), 8);
        // Matrix starts empty (all FALSE)
        assert_eq!(matrix.density(), 0);
    }

    #[test]
    fn and_simplification() {
        let factory = BooleanFactory::new(5, Options::default());

        // AND with FALSE => FALSE
        let result = factory.and(factory.constant(true), factory.constant(false));
        assert_eq!(result.label(), -1); // FALSE

        // AND with TRUE => other value
        let v1 = factory.variable(1);
        let result = factory.and(factory.constant(true), v1.clone());
        assert_eq!(result.label(), 1); // v1
    }

    #[test]
    fn or_simplification() {
        let factory = BooleanFactory::new(5, Options::default());

        // OR with TRUE => TRUE
        let result = factory.or(factory.constant(true), factory.constant(false));
        assert_eq!(result.label(), 0); // TRUE

        // OR with FALSE => other value
        let v1 = factory.variable(1);
        let result = factory.or(factory.constant(false), v1.clone());
        assert_eq!(result.label(), 1); // v1
    }

    #[test]
    fn not_simplification() {
        let factory = BooleanFactory::new(5, Options::default());

        // NOT TRUE => FALSE
        let result = factory.not(factory.constant(true));
        assert_eq!(result.label(), -1); // FALSE

        // NOT FALSE => TRUE
        let result = factory.not(factory.constant(false));
        assert_eq!(result.label(), 0); // TRUE
    }

    #[test]
    fn ite_simplification() {
        let factory = BooleanFactory::new(5, Options::default());
        let v1 = factory.variable(1);
        let v2 = factory.variable(2);

        // ITE with TRUE condition => then branch
        let result = factory.ite(factory.constant(true), v1.clone(), v2.clone());
        assert_eq!(result.label(), 1); // v1

        // ITE with FALSE condition => else branch
        let result = factory.ite(factory.constant(false), v1.clone(), v2.clone());
        assert_eq!(result.label(), 2); // v2

        // ITE with same branches => that value
        let result = factory.ite(v1.clone(), v2.clone(), v2.clone());
        assert_eq!(result.label(), 2); // v2
    }

    #[test]
    fn integer_creation() {
        let factory = BooleanFactory::new(10, Options::default());

        // Create integer constant
        let int5 = factory.integer(5);
        assert_eq!(int5.width(), factory.options.bitwidth);

        // Verify it's constant
        assert!(int5.is_constant());
        assert_eq!(int5.value(), Some(5));

        // Test negative integer
        let int_neg = factory.integer(-3);
        assert!(int_neg.is_constant());
        assert_eq!(int_neg.value(), Some(-3));

        // Test zero
        let int_zero = factory.integer(0);
        assert!(int_zero.is_constant());
        assert_eq!(int_zero.value(), Some(0));
    }

    #[test]
    fn integer_bitwidth() {
        let options = Options {
            bitwidth: 8,
            ..Default::default()
        };
        let factory = BooleanFactory::new(10, options);

        let int_val = factory.integer(127);
        assert_eq!(int_val.width(), 8);

        let int_val2 = factory.integer(-128);
        assert_eq!(int_val2.width(), 8);
    }

    // Algebraic property tests following Java BooleanCircuitTest

    #[test]
    #[should_panic(expected = "Double negation elimination failed")]
    fn not_involution() {
        // Following Java: testNot() - involution: !!a = a
        // EXPECTED TO FAIL: Double negation elimination not implemented for formulas
        let factory = BooleanFactory::new(20, Options::default());

        // Constants
        assert_eq!(factory.not(factory.not(factory.constant(false))), factory.constant(false));
        assert_eq!(factory.not(factory.not(factory.constant(true))), factory.constant(true));

        // Variables
        for i in 1..=10 {
            let v = factory.variable(i);
            assert_eq!(factory.not(factory.not(v.clone())), v, "Double negation elimination failed for variable");
        }

        // Formulas
        let v1 = factory.variable(1);
        let v2 = factory.variable(2);
        let or12 = factory.or(v1.clone(), v2.clone());
        let and12 = factory.and(v1, v2);

        assert_eq!(factory.not(factory.not(or12.clone())), or12, "Double negation elimination failed for OR formula");
        assert_eq!(factory.not(factory.not(and12.clone())), and12, "Double negation elimination failed for AND formula");
    }

    #[test]
    fn and_identity_and_short_circuit() {
        // Following Java: testIdentityContradictionExcludedMiddle for AND
        let factory = BooleanFactory::new(10, Options::default());

        let v1 = factory.variable(1);
        let v2 = factory.variable(2);

        // Identity: p AND TRUE = p
        assert_eq!(factory.and(v1.clone(), factory.constant(true)), v1);
        assert_eq!(factory.and(factory.constant(true), v2.clone()), v2);

        // Short circuit: p AND FALSE = FALSE
        assert_eq!(factory.and(v1.clone(), factory.constant(false)), factory.constant(false));
        assert_eq!(factory.and(factory.constant(false), v1.clone()), factory.constant(false));

        // Contradiction: p AND !p = FALSE
        assert_eq!(factory.and(v1.clone(), factory.not(v1.clone())), factory.constant(false));
    }

    #[test]
    fn or_identity_and_short_circuit() {
        // Following Java: testIdentityContradictionExcludedMiddle for OR
        let factory = BooleanFactory::new(10, Options::default());

        let v1 = factory.variable(1);
        let v2 = factory.variable(2);

        // Identity: p OR FALSE = p
        assert_eq!(factory.or(v1.clone(), factory.constant(false)), v1);
        assert_eq!(factory.or(factory.constant(false), v2.clone()), v2);

        // Short circuit: p OR TRUE = TRUE
        assert_eq!(factory.or(v1.clone(), factory.constant(true)), factory.constant(true));
        assert_eq!(factory.or(factory.constant(true), v1.clone()), factory.constant(true));

        // Excluded middle: p OR !p = TRUE
        assert_eq!(factory.or(v1.clone(), factory.not(v1.clone())), factory.constant(true));
    }

    #[test]
    #[should_panic(expected = "Absorption law failed")]
    fn and_idempotency_and_absorption() {
        // Following Java: testIdempotencyAbsorptionContraction for AND
        // EXPECTED TO FAIL: Absorption law optimization not implemented
        let factory = BooleanFactory::new(10, Options::default());

        let v1 = factory.variable(1);
        let v2 = factory.variable(2);

        // Idempotency: p AND p = p
        assert_eq!(factory.and(v1.clone(), v1.clone()), v1);
        assert_eq!(factory.and(v2.clone(), v2.clone()), v2);

        // Absorption: p AND (p OR q) = p
        let v1_or_v2 = factory.or(v1.clone(), v2.clone());
        assert_eq!(factory.and(v1.clone(), v1_or_v2), v1, "Absorption law failed: p AND (p OR q) should equal p");

        // Contraction (complement of absorption): p OR (p AND q) = p
        let v1_and_v2 = factory.and(v1.clone(), v2.clone());
        assert_eq!(factory.or(v1.clone(), v1_and_v2), v1, "Absorption law failed: p OR (p AND q) should equal p");
    }

    #[test]
    #[should_panic(expected = "Absorption law failed")]
    fn or_idempotency_and_absorption() {
        // Following Java: testIdempotencyAbsorptionContraction for OR
        // EXPECTED TO FAIL: Absorption law optimization not implemented
        let factory = BooleanFactory::new(10, Options::default());

        let v1 = factory.variable(1);
        let v2 = factory.variable(2);

        // Idempotency: p OR p = p
        assert_eq!(factory.or(v1.clone(), v1.clone()), v1);
        assert_eq!(factory.or(v2.clone(), v2.clone()), v2);

        // Absorption: p OR (p AND q) = p
        let v1_and_v2 = factory.and(v1.clone(), v2.clone());
        assert_eq!(factory.or(v1.clone(), v1_and_v2), v1, "Absorption law failed: p OR (p AND q) should equal p");

        // Contraction (complement of absorption): p AND (p OR q) = p
        let v1_or_v2 = factory.or(v1.clone(), v2.clone());
        assert_eq!(factory.and(v1.clone(), v1_or_v2), v1, "Absorption law failed: p AND (p OR q) should equal p");
    }

    #[test]
    fn and_commutativity() {
        // Following Java: testCommutativityAndAssociativity for AND
        let factory = BooleanFactory::new(10, Options::default());

        let v1 = factory.variable(1);
        let v2 = factory.variable(2);
        let v3 = factory.variable(3);

        // Commutativity: p AND q = q AND p
        assert_eq!(
            factory.and(v1.clone(), v2.clone()),
            factory.and(v2.clone(), v1.clone())
        );

        // Multi-input commutativity
        assert_eq!(
            factory.and_multi(vec![v1.clone(), v2.clone(), v3.clone()]),
            factory.and_multi(vec![v2.clone(), v3.clone(), v1.clone()])
        );
        assert_eq!(
            factory.and_multi(vec![v1.clone(), v2.clone(), v3.clone()]),
            factory.and_multi(vec![v3.clone(), v1.clone(), v2.clone()])
        );
    }

    #[test]
    fn or_commutativity() {
        // Following Java: testCommutativityAndAssociativity for OR
        let factory = BooleanFactory::new(10, Options::default());

        let v1 = factory.variable(1);
        let v2 = factory.variable(2);
        let v3 = factory.variable(3);

        // Commutativity: p OR q = q OR p
        assert_eq!(
            factory.or(v1.clone(), v2.clone()),
            factory.or(v2.clone(), v1.clone())
        );

        // Multi-input commutativity
        assert_eq!(
            factory.or_multi(vec![v1.clone(), v2.clone(), v3.clone()]),
            factory.or_multi(vec![v2.clone(), v3.clone(), v1.clone()])
        );
        assert_eq!(
            factory.or_multi(vec![v1.clone(), v2.clone(), v3.clone()]),
            factory.or_multi(vec![v3.clone(), v1.clone(), v2.clone()])
        );
    }

    #[test]
    #[should_panic(expected = "Canonical form failed")]
    fn and_associativity() {
        // Following Java: testParenthesis for AND
        // EXPECTED TO FAIL: Canonical form generation not implemented
        let factory = BooleanFactory::new(10, Options::default());

        let v1 = factory.variable(1);
        let v2 = factory.variable(2);
        let v3 = factory.variable(3);
        let v4 = factory.variable(4);

        // Associativity: (p AND q) AND r = p AND (q AND r)
        assert_eq!(
            factory.and(factory.and(v1.clone(), v2.clone()), v3.clone()),
            factory.and(v1.clone(), factory.and(v2.clone(), v3.clone())),
            "Canonical form failed: (p AND q) AND r should equal p AND (q AND r)"
        );

        // Extended: ((p AND q) AND r) AND s = p AND (q AND (r AND s))
        let pq = factory.and(v1.clone(), v2.clone());
        let pqr = factory.and(pq.clone(), v3.clone());
        let pqrs = factory.and(pqr, v4.clone());

        let rs = factory.and(v3.clone(), v4.clone());
        let qrs = factory.and(v2.clone(), rs);
        let p_qrs = factory.and(v1.clone(), qrs);

        assert_eq!(pqrs, p_qrs, "Canonical form failed for nested AND");
    }

    #[test]
    #[should_panic(expected = "Canonical form failed")]
    fn or_associativity() {
        // Following Java: testParenthesis for OR
        // EXPECTED TO FAIL: Canonical form generation not implemented
        let factory = BooleanFactory::new(10, Options::default());

        let v1 = factory.variable(1);
        let v2 = factory.variable(2);
        let v3 = factory.variable(3);
        let v4 = factory.variable(4);

        // Associativity: (p OR q) OR r = p OR (q OR r)
        assert_eq!(
            factory.or(factory.or(v1.clone(), v2.clone()), v3.clone()),
            factory.or(v1.clone(), factory.or(v2.clone(), v3.clone())),
            "Canonical form failed: (p OR q) OR r should equal p OR (q OR r)"
        );

        // Extended: ((p OR q) OR r) OR s = p OR (q OR (r OR s))
        let pq = factory.or(v1.clone(), v2.clone());
        let pqr = factory.or(pq.clone(), v3.clone());
        let pqrs = factory.or(pqr, v4.clone());

        let rs = factory.or(v3.clone(), v4.clone());
        let qrs = factory.or(v2.clone(), rs);
        let p_qrs = factory.or(v1.clone(), qrs);

        assert_eq!(pqrs, p_qrs, "Canonical form failed for nested OR");
    }

    #[test]
    #[should_panic(expected = "ITE reduction failed")]
    fn ite_reductions() {
        // Following Java: testITE
        // EXPECTED TO FAIL: ITE to boolean operation conversion not implemented
        let factory = BooleanFactory::new(10, Options::default());

        let v1 = factory.variable(1);
        let v2 = factory.variable(2);
        let a12 = factory.and(v1.clone(), v2.clone());
        let na12 = factory.not(a12.clone());
        let v6 = factory.variable(6);
        let v7 = factory.variable(7);
        let o67 = factory.or(v6.clone(), v7.clone());
        let v8 = factory.variable(8);
        let v9 = factory.variable(9);
        let o89 = factory.or(v8.clone(), v9.clone());

        // ITE(cond, t, t) = t
        assert_eq!(factory.ite(a12.clone(), o67.clone(), o67.clone()), o67);

        // ITE(cond, TRUE, e) = cond OR e
        assert_eq!(
            factory.ite(a12.clone(), factory.constant(true), o89.clone()),
            factory.or(o89.clone(), a12.clone()),
            "ITE reduction failed: ITE(c, TRUE, e) should equal c OR e"
        );

        // ITE(cond, FALSE, e) = !cond AND e
        assert_eq!(
            factory.ite(a12.clone(), factory.constant(false), o89.clone()),
            factory.and(o89.clone(), na12.clone()),
            "ITE reduction failed: ITE(c, FALSE, e) should equal !c AND e"
        );
    }
}
