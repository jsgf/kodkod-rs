//! Boolean factory with gate caching
//!
//! The factory creates boolean values and formulas, with automatic deduplication.
//! Uses interior mutability (Cell/RefCell) to avoid &mut self everywhere.

use super::{BoolValue, BooleanConstant, BooleanFormula, BooleanMatrix, BooleanVariable, Dimensions, FormulaKind, MatrixArena};
use rustc_hash::FxHashMap;
use std::cell::{Cell, RefCell};

/// Options for boolean factory
#[derive(Debug, Clone)]
pub struct Options {
    /// Enable sharing of boolean formulas (default: true)
    pub sharing: bool,
}

impl Default for Options {
    fn default() -> Self {
        Self { sharing: true }
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
    cache: RefCell<FxHashMap<CacheKey, BooleanFormula>>,
    bitwidth: usize,
    // Arena for allocating BoolValue handles
    arena: MatrixArena,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum CacheKey {
    And(Vec<i32>),
    Or(Vec<i32>),
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
            options,
            cache: RefCell::new(FxHashMap::default()),
            bitwidth: 32, // Default bitwidth for integers
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

    /// Creates a boolean variable
    pub fn variable(&self, label: i32) -> BoolValue {
        assert!(label > 0 && label <= self.num_variables as i32,
                "Variable label must be in range 1..={}", self.num_variables);
        BoolValue::Variable(BooleanVariable::new(label))
    }

    /// Creates a constant
    pub fn constant(&self, value: bool) -> BoolValue {
        BoolValue::Constant(if value {
            BooleanConstant::TRUE
        } else {
            BooleanConstant::FALSE
        })
    }

    /// Creates an AND gate
    pub fn and(&self, left: BoolValue, right: BoolValue) -> BoolValue {
        self.and_multi(vec![left, right])
    }

    /// Creates a multi-input AND gate
    pub fn and_multi(&self, mut inputs: Vec<BoolValue>) -> BoolValue {
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

        // Check cache
        if self.options.sharing {
            let labels: Vec<i32> = inputs.iter().map(|v| v.label()).collect();
            let key = CacheKey::And(labels.clone());

            if let Some(cached) = self.cache.borrow().get(&key) {
                return BoolValue::Formula(cached.clone());
            }

            // Create new formula - allocate inputs slice in arena
            let label = self.allocate_label();
            let handle = self.arena.alloc_slice_handle(&inputs);
            let formula = BooleanFormula::new(label, FormulaKind::And(handle));
            self.cache.borrow_mut().insert(key, formula.clone());
            BoolValue::Formula(formula)
        } else {
            let label = self.allocate_label();
            let handle = self.arena.alloc_slice_handle(&inputs);
            BoolValue::Formula(BooleanFormula::new(label, FormulaKind::And(handle)))
        }
    }

    /// Creates an OR gate
    pub fn or(&self, left: BoolValue, right: BoolValue) -> BoolValue {
        self.or_multi(vec![left, right])
    }

    /// Creates a multi-input OR gate
    pub fn or_multi(&self, mut inputs: Vec<BoolValue>) -> BoolValue {
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

        // Check cache
        if self.options.sharing {
            let labels: Vec<i32> = inputs.iter().map(|v| v.label()).collect();
            let key = CacheKey::Or(labels.clone());

            if let Some(cached) = self.cache.borrow().get(&key) {
                return BoolValue::Formula(cached.clone());
            }

            // Create new formula - allocate inputs slice in arena
            let label = self.allocate_label();
            let handle = self.arena.alloc_slice_handle(&inputs);
            let formula = BooleanFormula::new(label, FormulaKind::Or(handle));
            self.cache.borrow_mut().insert(key, formula.clone());
            BoolValue::Formula(formula)
        } else {
            let label = self.allocate_label();
            let handle = self.arena.alloc_slice_handle(&inputs);
            BoolValue::Formula(BooleanFormula::new(label, FormulaKind::Or(handle)))
        }
    }

    /// Creates a NOT gate
    pub fn not(&self, input: BoolValue) -> BoolValue {
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

            if let Some(cached) = self.cache.borrow().get(&key) {
                return BoolValue::Formula(cached.clone());
            }

            // Create new formula - allocate input handle in arena
            let label = self.allocate_label();
            let handle = self.arena.alloc_handle(input.clone());
            let formula = BooleanFormula::new(label, FormulaKind::Not(handle));
            self.cache.borrow_mut().insert(key, formula.clone());
            BoolValue::Formula(formula)
        } else {
            let label = self.allocate_label();
            let handle = self.arena.alloc_handle(input);
            BoolValue::Formula(BooleanFormula::new(label, FormulaKind::Not(handle)))
        }
    }

    /// Creates an if-then-else gate
    pub fn ite(&self, condition: BoolValue, then_val: BoolValue, else_val: BoolValue) -> BoolValue {
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

            if let Some(cached) = self.cache.borrow().get(&key) {
                return BoolValue::Formula(cached.clone());
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
            self.cache.borrow_mut().insert(key, formula.clone());
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
    pub fn matrix(&self, dimensions: Dimensions) -> BooleanMatrix {
        BooleanMatrix::empty(dimensions)
    }

    /// Returns the bitwidth used for integer operations
    pub fn bitwidth(&self) -> usize {
        self.bitwidth
    }

    /// XOR operation: a XOR b = (a AND NOT b) OR (NOT a AND b)
    pub fn xor(&self, a: BoolValue, b: BoolValue) -> BoolValue {
        let not_b = self.not(b.clone());
        let a_and_not_b = self.and(a.clone(), not_b);

        let not_a = self.not(a);
        let not_a_and_b = self.and(not_a, b);

        self.or(a_and_not_b, not_a_and_b)
    }

    /// IFF (if and only if): a IFF b = (a AND b) OR (NOT a AND NOT b)
    pub fn iff(&self, a: BoolValue, b: BoolValue) -> BoolValue {
        let a_and_b = self.and(a.clone(), b.clone());
        let not_a = self.not(a);
        let not_b = self.not(b);
        let not_a_and_not_b = self.and(not_a, not_b);
        self.or(a_and_b, not_a_and_not_b)
    }

    /// IMPLIES: a IMPLIES b = NOT a OR b
    pub fn implies(&self, a: BoolValue, b: BoolValue) -> BoolValue {
        let not_a = self.not(a);
        self.or(not_a, b)
    }

    /// Full adder sum: a XOR b XOR cin
    /// Returns the sum bit (without carry)
    pub fn sum(&self, a: BoolValue, b: BoolValue, cin: BoolValue) -> BoolValue {
        let ab_xor = self.xor(a, b);
        self.xor(ab_xor, cin)
    }

    /// Full adder carry out: (a AND b) OR (cin AND (a XOR b))
    pub fn carry(&self, a: BoolValue, b: BoolValue, cin: BoolValue) -> BoolValue {
        let a_and_b = self.and(a.clone(), b.clone());
        let ab_xor = self.xor(a, b);
        let cin_and_xor = self.and(cin, ab_xor);
        self.or(a_and_b, cin_and_xor)
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
        let mut factory = BooleanFactory::new(5, Options::default());
        let v1 = factory.variable(1);
        let v2 = factory.variable(2);

        let and1 = factory.and(v1.clone(), v2.clone());
        let and2 = factory.and(v1.clone(), v2.clone());

        // Same gate instance due to caching
        assert_eq!(and1.label(), and2.label());
    }

    #[test]
    fn boolean_matrix() {
        let mut factory = BooleanFactory::new(10, Options::default());
        // Ternary relation over universe of size 2: capacity=8 (2³), arity=3
        let dims = Dimensions::new(8, 3);

        let matrix = factory.matrix(dims);

        assert_eq!(matrix.dimensions().capacity(), 8);
        // Matrix starts empty (all FALSE)
        assert_eq!(matrix.density(), 0);
    }

    #[test]
    fn and_simplification() {
        let mut factory = BooleanFactory::new(5, Options::default());

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
        let mut factory = BooleanFactory::new(5, Options::default());

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
        let mut factory = BooleanFactory::new(5, Options::default());

        // NOT TRUE => FALSE
        let result = factory.not(factory.constant(true));
        assert_eq!(result.label(), -1); // FALSE

        // NOT FALSE => TRUE
        let result = factory.not(factory.constant(false));
        assert_eq!(result.label(), 0); // TRUE
    }

    #[test]
    fn ite_simplification() {
        let mut factory = BooleanFactory::new(5, Options::default());
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
}
