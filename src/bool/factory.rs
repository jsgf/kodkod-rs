//! Boolean factory with gate caching
//!
//! The factory creates boolean values and formulas, with automatic deduplication.
//! Uses interior mutability (Cell/RefCell) to avoid &mut self everywhere.

use super::{BoolValue, BooleanConstant, BooleanFormula, BooleanMatrix, BooleanVariable, Dimensions, FormulaKind};
use rustc_hash::{FxHashMap, FxHashSet};
use std::cell::{Cell, RefCell};
use std::collections::HashSet;
use std::rc::Rc;

/// Options for boolean factory
#[derive(Debug, Clone)]
pub struct Options {
    /// Enable sharing of boolean formulas (default: true)
    pub sharing: bool,
    /// Bitwidth for integer encoding (default: 32)
    pub bitwidth: usize,
    /// Skolemization depth (default: 0, negative means disabled)
    pub skolem_depth: Option<usize>,
}

impl Default for Options {
    fn default() -> Self {
        Self {
            sharing: true,
            bitwidth: 32,
            skolem_depth: Some(0),
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
    cache: RefCell<FxHashMap<CacheKey, BooleanFormula>>,
    bitwidth: usize,
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
        }
    }

    /// Returns the number of variables
    pub fn num_variables(&self) -> u32 {
        self.num_variables
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

        // Apply subsumption law (JoJ) BEFORE flattening: (a & b) & (a & b & c) = (a & b & c)
        // If one AND gate's inputs are a subset of another's, keep the superset
        // This must happen before flattening or the gates will be expanded
        if inputs.len() > 1 {
            // Collect flattened labels for all AND gates (without modifying inputs)
            let flattened: Vec<Option<FxHashSet<i32>>> = inputs
                .iter()
                .map(|input| self.get_flattened_labels(input, true))
                .collect();

            let mut subsume_remove = Vec::new();
            for i in 0..inputs.len() {
                if subsume_remove.contains(&i) {
                    continue;
                }
                if let Some(ref set_i) = flattened[i] {
                    for j in (i + 1)..inputs.len() {
                        if subsume_remove.contains(&j) {
                            continue;
                        }
                        if let Some(ref set_j) = flattened[j] {
                            // For AND: if set_i ⊂ set_j, remove i (keep j, the superset)
                            // For AND: if set_j ⊂ set_i, remove j (keep i, the superset)
                            if set_i.len() < set_j.len() && set_i.iter().all(|x| set_j.contains(x)) {
                                subsume_remove.push(i);
                                break; // i is removed, no need to check more
                            } else if set_j.len() < set_i.len() && set_j.iter().all(|x| set_i.contains(x)) {
                                subsume_remove.push(j);
                            } else if set_i.len() == set_j.len() && set_i == set_j {
                                // Same flattened inputs - remove one (keep earlier, remove later)
                                subsume_remove.push(j);
                            }
                        }
                    }
                }
            }

            // Sort and deduplicate removal indices
            subsume_remove.sort_unstable();
            subsume_remove.dedup();
            // Remove in reverse order
            for &i in subsume_remove.iter().rev() {
                inputs.remove(i);
            }

            if inputs.is_empty() {
                return self.constant(true);
            }
            if inputs.len() == 1 {
                return inputs.into_iter().next().unwrap();
            }
        }

        // Flatten nested AND gates into a single multi-input AND
        let mut flattened = Vec::new();
        for input in inputs {
            match input {
                BoolValue::Formula(BooleanFormula { kind: FormulaKind::And(inner_inputs), .. }) => {
                    // Flatten nested AND by extracting its inputs
                    let inner = inner_inputs.as_ref();
                    flattened.extend_from_slice(inner);
                }
                other => flattened.push(other),
            }
        }
        inputs = flattened;

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
        // Use a HashSet for O(n) checking instead of O(n²) nested loops
        let mut seen_labels: HashSet<i32> = HashSet::new();
        for input in &inputs {
            let label = input.label();
            // Check if we've seen the negation of this label
            if seen_labels.contains(&-label) {
                return self.constant(false);
            }
            // For NOT gates, also check if we've seen the inner formula
            if let BoolValue::Formula(f) = input
                && let FormulaKind::Not(h) = f.kind() {
                    let inner_label = h.label();
                    if seen_labels.contains(&inner_label) {
                        return self.constant(false);
                    }
                }
            seen_labels.insert(label);
        }

        // Remove duplicates (idempotency: p AND p = p)
        inputs.sort_by_key(|v| v.label());
        inputs.dedup();

        if inputs.len() == 1 {
            return inputs.into_iter().next().unwrap();
        }

        // Apply absorption law: p AND (p OR q) = p
        // Remove any OR formula that contains another input
        // Build a set of input labels for O(1) lookups
        let input_labels: HashSet<i32> = inputs.iter().map(|v| v.label()).collect();
        let mut to_remove = Vec::new();
        for (i, input) in inputs.iter().enumerate() {
            if let BoolValue::Formula(f) = input
                && let FormulaKind::Or(or_inputs_handle) = f.kind() {
                    let or_inputs = &**or_inputs_handle;
                    // Check if any other input appears in this OR
                    // Now O(m) where m = or_inputs.len(), not O(n)
                    if or_inputs.iter().any(|v| {
                        let label = v.label();
                        label != input.label() && input_labels.contains(&label)
                    }) {
                        to_remove.push(i);
                    }
                }
        }

        // Remove in reverse order to maintain indices
        for &i in to_remove.iter().rev() {
            inputs.remove(i);
        }

        if inputs.len() == 1 {
            return inputs.into_iter().next().unwrap();
        }

        // Check cache
        if self.options.sharing {
            let labels: Vec<i32> = inputs.iter().map(|v| v.label()).collect();
            let key = CacheKey::And(labels.into_boxed_slice());

            if let Some(cached) = self.cache.borrow().get(&key).cloned() {
                return BoolValue::Formula(cached);
            }

            // Create new formula - allocate inputs slice in arena
            let label = self.allocate_label();
            let handle = Rc::from(inputs.as_slice());
            let formula = BooleanFormula::new(label, FormulaKind::And(handle));
            self.cache.borrow_mut().insert(key, formula.clone());
            BoolValue::Formula(formula)
        } else {
            let label = self.allocate_label();
            let handle = Rc::from(inputs.as_slice());
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

        // Apply subsumption law (JoJ) BEFORE flattening: (a | b) | (a | b | c) = (a | b | c)
        // If one OR gate's inputs are a subset of another's, keep the superset
        // This must happen before flattening or the gates will be expanded
        if inputs.len() > 1 {
            // Collect flattened labels for all OR gates (without modifying inputs)
            let flattened: Vec<Option<FxHashSet<i32>>> = inputs
                .iter()
                .map(|input| self.get_flattened_labels(input, false))
                .collect();

            let mut subsume_remove = Vec::new();
            for i in 0..inputs.len() {
                if subsume_remove.contains(&i) {
                    continue;
                }
                if let Some(ref set_i) = flattened[i] {
                    for j in (i + 1)..inputs.len() {
                        if subsume_remove.contains(&j) {
                            continue;
                        }
                        if let Some(ref set_j) = flattened[j] {
                            // For OR: if set_i ⊂ set_j, remove i (keep j, the superset)
                            // For OR: if set_j ⊂ set_i, remove j (keep i, the superset)
                            if set_i.len() < set_j.len() && set_i.iter().all(|x| set_j.contains(x)) {
                                subsume_remove.push(i);
                                break; // i is removed, no need to check more
                            } else if set_j.len() < set_i.len() && set_j.iter().all(|x| set_i.contains(x)) {
                                subsume_remove.push(j);
                            } else if set_i.len() == set_j.len() && set_i == set_j {
                                // Same flattened inputs - remove one (keep earlier, remove later)
                                subsume_remove.push(j);
                            }
                        }
                    }
                }
            }

            // Sort and deduplicate removal indices
            subsume_remove.sort_unstable();
            subsume_remove.dedup();
            // Remove in reverse order
            for &i in subsume_remove.iter().rev() {
                inputs.remove(i);
            }

            if inputs.is_empty() {
                return self.constant(false);
            }
            if inputs.len() == 1 {
                return inputs.into_iter().next().unwrap();
            }
        }

        // Flatten nested OR gates into a single multi-input OR
        let mut flattened = Vec::new();
        for input in inputs {
            match input {
                BoolValue::Formula(BooleanFormula { kind: FormulaKind::Or(inner_inputs), .. }) => {
                    // Flatten nested OR by extracting its inputs
                    let inner = inner_inputs.as_ref();
                    flattened.extend_from_slice(inner);
                }
                other => flattened.push(other),
            }
        }
        inputs = flattened;

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
        // Use a HashSet for O(n) checking instead of O(n²) nested loops
        let mut seen_labels: HashSet<i32> = HashSet::new();
        for input in &inputs {
            let label = input.label();
            // Check if we've seen the negation of this label
            if seen_labels.contains(&-label) {
                return self.constant(true);
            }
            // For NOT gates, also check if we've seen the inner formula
            if let BoolValue::Formula(f) = input
                && let FormulaKind::Not(h) = f.kind() {
                    let inner_label = h.label();
                    if seen_labels.contains(&inner_label) {
                        return self.constant(true);
                    }
                }
            seen_labels.insert(label);
        }

        // Remove duplicates (idempotency: p OR p = p)
        inputs.sort_by_key(|v| v.label());
        inputs.dedup();

        if inputs.len() == 1 {
            return inputs.into_iter().next().unwrap();
        }

        // Apply contraction (absorption) law: p OR (p AND q) = p
        // Remove any AND formula that contains another input
        // Build a set of input labels for O(1) lookups
        let input_labels: HashSet<i32> = inputs.iter().map(|v| v.label()).collect();
        let mut to_remove = Vec::new();
        for (i, input) in inputs.iter().enumerate() {
            if let BoolValue::Formula(f) = input
                && let FormulaKind::And(and_inputs_handle) = f.kind() {
                    let and_inputs = &**and_inputs_handle;
                    // Check if any other input appears in this AND
                    // Now O(m) where m = and_inputs.len(), not O(n)
                    if and_inputs.iter().any(|v| {
                        let label = v.label();
                        label != input.label() && input_labels.contains(&label)
                    }) {
                        to_remove.push(i);
                    }
                }
        }

        // Remove in reverse order to maintain indices
        for &i in to_remove.iter().rev() {
            inputs.remove(i);
        }

        if inputs.len() == 1 {
            return inputs.into_iter().next().unwrap();
        }

        // Check cache
        if self.options.sharing {
            let labels: Vec<i32> = inputs.iter().map(|v| v.label()).collect();
            let key = CacheKey::Or(labels.into_boxed_slice());

            if let Some(cached) = self.cache.borrow().get(&key).cloned() {
                return BoolValue::Formula(cached);
            }

            // Create new formula - allocate inputs slice in arena
            let label = self.allocate_label();
            let handle = Rc::from(inputs.as_slice());
            let formula = BooleanFormula::new(label, FormulaKind::Or(handle));
            self.cache.borrow_mut().insert(key, formula.clone());
            BoolValue::Formula(formula)
        } else {
            let label = self.allocate_label();
            let handle = Rc::from(inputs.as_slice());
            BoolValue::Formula(BooleanFormula::new(label, FormulaKind::Or(handle)))
        }
    }

    /// Creates a NOT gate
    pub fn not(&self, input: BoolValue) -> BoolValue {
        // Check for optimizations
        match &input {
            BoolValue::Constant(BooleanConstant::TRUE) => return self.constant(false),
            BoolValue::Constant(BooleanConstant::FALSE) => return self.constant(true),
            BoolValue::Formula(BooleanFormula { kind: FormulaKind::Not(inner), .. }) => {
                // Double negation: NOT(NOT(x)) = x
                return (**inner).clone();
            }
            _ => {}
        }

        // Check cache
        if self.options.sharing {
            let key = CacheKey::Not(input.label());

            if let Some(cached) = self.cache.borrow().get(&key).cloned() {
                return BoolValue::Formula(cached);
            }

            // Create new formula - allocate input handle in arena
            let label = self.allocate_label();
            let handle = Rc::new(input.clone());
            let formula = BooleanFormula::new(label, FormulaKind::Not(handle));
            self.cache.borrow_mut().insert(key, formula.clone());
            BoolValue::Formula(formula)
        } else {
            let label = self.allocate_label();
            let handle = Rc::new(input);
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

        // ITE reductions to simpler boolean operations
        match (&then_val, &else_val) {
            // ITE(cond, TRUE, else) = cond OR else
            (BoolValue::Constant(BooleanConstant::TRUE), _) => {
                return self.or(condition, else_val);
            }
            // ITE(cond, FALSE, else) = !cond AND else
            (BoolValue::Constant(BooleanConstant::FALSE), _) => {
                return self.and(self.not(condition), else_val);
            }
            // ITE(cond, then, TRUE) = !cond OR then
            (_, BoolValue::Constant(BooleanConstant::TRUE)) => {
                return self.or(self.not(condition), then_val);
            }
            // ITE(cond, then, FALSE) = cond AND then
            (_, BoolValue::Constant(BooleanConstant::FALSE)) => {
                return self.and(condition, then_val);
            }
            _ => {}
        }

        // Check cache
        if self.options.sharing {
            let key = CacheKey::Ite(condition.label(), then_val.label(), else_val.label());

            if let Some(cached) = self.cache.borrow().get(&key).cloned() {
                return BoolValue::Formula(cached);
            }

            // Create new formula - allocate value handles in arena
            let label = self.allocate_label();
            let condition_handle = Rc::new(condition.clone());
            let then_handle = Rc::new(then_val.clone());
            let else_handle = Rc::new(else_val.clone());
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
            let condition_handle = Rc::new(condition);
            let then_handle = Rc::new(then_val);
            let else_handle = Rc::new(else_val);
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

    /// Creates an Int representing the given constant integer value
    /// Following Java: BooleanFactory.integer(int)
    pub fn integer(&self, value: i32) -> crate::bool::Int {
        crate::bool::Int::constant(value, self.options.bitwidth, BoolValue::Constant(BooleanConstant::TRUE))
    }

    fn allocate_label(&self) -> i32 {
        let label = self.next_label.get();
        self.next_label.set(label + 1);
        label as i32
    }

    /// Flattens a gate's inputs by recursively extracting same-op children.
    /// Returns the set of leaf input labels (not including same-op child gates).
    /// This is used for subsumption checking.
    ///
    /// For example, flattening AND gate `(a & b) & c` where `(a & b)` is also an AND gate
    /// returns `{a, b, c}`.
    ///
    /// # Arguments
    /// * `value` - The value to flatten
    /// * `is_and` - If true, we're flattening AND gates; if false, flattening OR gates
    fn flatten_gate_inputs(&self, value: &BoolValue, is_and: bool) -> FxHashSet<i32> {
        let mut result = FxHashSet::default();
        match value {
            BoolValue::Formula(f) => {
                match f.kind() {
                    FormulaKind::And(handle) if is_and => {
                        // Recursively flatten AND children when we're in AND mode
                        let inputs = &**handle;
                        for input in inputs {
                            result.extend(self.flatten_gate_inputs(input, true));
                        }
                    }
                    FormulaKind::Or(handle) if !is_and => {
                        // Recursively flatten OR children when we're in OR mode
                        let inputs = &**handle;
                        for input in inputs {
                            result.extend(self.flatten_gate_inputs(input, false));
                        }
                    }
                    _ => {
                        // Any other value (variable, constant, wrong-op gate) - just use its label
                        result.insert(value.label());
                    }
                }
            }
            _ => {
                result.insert(value.label());
            }
        }
        result
    }

    /// Get the flattened labels of inputs if this is a same-op gate.
    /// Returns None if the value is not a formula or not the expected op.
    fn get_flattened_labels(&self, value: &BoolValue, is_and: bool) -> Option<FxHashSet<i32>> {
        match value {
            BoolValue::Formula(f) => {
                match f.kind() {
                    FormulaKind::And(handle) if is_and => {
                        let inputs = &**handle;
                        let mut result = FxHashSet::default();
                        for input in inputs {
                            result.extend(self.flatten_gate_inputs(input, true));
                        }
                        Some(result)
                    }
                    FormulaKind::Or(handle) if !is_and => {
                        let inputs = &**handle;
                        let mut result = FxHashSet::default();
                        for input in inputs {
                            result.extend(self.flatten_gate_inputs(input, false));
                        }
                        Some(result)
                    }
                    _ => None,
                }
            }
            _ => None,
        }
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
    fn not_involution() {
        // Following Java: testNot() - involution: !!a = a
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
    fn and_idempotency_and_absorption() {
        // Following Java: testIdempotencyAbsorptionContraction for AND
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
    fn or_idempotency_and_absorption() {
        // Following Java: testIdempotencyAbsorptionContraction for OR
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
    fn and_associativity() {
        // Following Java: testParenthesis for AND
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
    fn or_associativity() {
        // Following Java: testParenthesis for OR
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
    fn ite_reductions() {
        // Following Java: testITE
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
