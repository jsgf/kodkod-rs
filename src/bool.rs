//! Boolean circuit representation
//!
//! The boolean layer is the intermediate representation used when translating
//! first-order logic formulas to CNF for SAT solving.
//!
//! Key types:
//! - `BooleanValue`: Trait for all boolean values (constants, variables, formulas)
//! - `BooleanConstant`: TRUE (label 0) or FALSE (label -1)
//! - `BooleanVariable`: Variables with positive integer labels
//! - `BoolValue<'arena>`: Enum encompassing all boolean value types
//! - `BooleanFormula`: Boolean gates (AND, OR, NOT, ITE)
//! - `Operator`: Boolean operators
//! - `Dimensions`: Matrix dimensions for relation encoding
//! - `BooleanMatrix`: Matrix of boolean values
//! - `BooleanFactory`: Factory for creating and caching boolean circuits

mod factory;
pub mod var_allocator;
pub mod int;
pub mod arena;

pub use factory::{BooleanFactory, Options};
pub use var_allocator::VariableAllocator;
pub use int::Int;
pub use arena::MatrixArena;

use rustc_hash::FxHashMap;
use std::marker::PhantomData;

/// Index handle for a value stored in the arena
///
/// A lightweight copy-able reference to a value allocated in an arena.
/// The lifetime parameter `'arena` ties the handle to a specific arena instance,
/// preventing accidental mixing of handles from different arenas.
///
/// Handles are type-safe: `Handle<'a, X>` cannot be used where `Handle<'a, Y>` is expected.
/// Can point to either a single value `Handle<'arena, T>` or a slice `Handle<'arena, [T]>`.
#[derive(Eq, PartialEq, Hash)]
pub struct Handle<'arena, T: ?Sized> {
    ptr: *const T,
    _phantom: PhantomData<&'arena ()>,
}

impl<'arena, T: ?Sized + std::fmt::Debug> std::fmt::Debug for Handle<'arena, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // SAFETY: Handle is only created from valid arena allocations
        // NOTE: This can stack overflow if there are cycles in the data structure,
        // but BooleanFactory should only create DAGs (directed acyclic graphs)
        unsafe { (*self.ptr).fmt(f) }
    }
}

impl<'arena, T: ?Sized> Copy for Handle<'arena, T> {}

impl<'arena, T: ?Sized> Clone for Handle<'arena, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'arena, T: ?Sized> Handle<'arena, T> {
    /// Creates a new handle from a pointer.
    ///
    /// # Safety
    /// The pointer must point to a valid value that outlives the arena lifetime.
    pub(crate) unsafe fn new(ptr: *const T) -> Self {
        Self {
            ptr,
            _phantom: PhantomData,
        }
    }
}

/// Trait for all Boolean values
///
/// Each boolean value has an integer label used in CNF translation.
pub trait BooleanValue {
    /// Returns the label for this boolean value.
    /// - Constants: TRUE=0, FALSE=-1
    /// - Variables: positive integers
    /// - Formulas: assigned by factory during construction
    fn label(&self) -> i32;
}

/// Boolean constant (TRUE or FALSE)
///
/// Constants have special labels:
/// - TRUE has label 0
/// - FALSE has label -1
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BooleanConstant {
    /// TRUE constant (label 0)
    TRUE,
    /// FALSE constant (label -1)
    FALSE,
}

impl BooleanConstant {
    /// Returns the label for this constant
    pub fn label(&self) -> i32 {
        match self {
            BooleanConstant::TRUE => 0,
            BooleanConstant::FALSE => -1,
        }
    }

    /// Returns the boolean value of this constant
    /// Following Java: BooleanConstant.booleanValue()
    pub fn boolean_value(&self) -> bool {
        self.label() > 0 || *self == BooleanConstant::TRUE
    }
}

impl BooleanValue for BooleanConstant {
    fn label(&self) -> i32 {
        self.label()
    }
}

/// Boolean variable with a positive integer label
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BooleanVariable {
    label: i32,
}

impl BooleanVariable {
    /// Creates a new boolean variable with the given label.
    ///
    /// # Panics
    /// Panics if label is not positive (must be > 0).
    pub fn new(label: i32) -> Self {
        assert!(label > 0, "Variable labels must be positive");
        Self { label }
    }

    /// Returns the label for this variable
    pub fn label(&self) -> i32 {
        self.label
    }
}

impl BooleanValue for BooleanVariable {
    fn label(&self) -> i32 {
        self.label
    }
}

/// Boolean formula (gate)
///
/// Formulas have identity-based equality using their unique labels.
/// Small enough (40 bytes) to be Copy.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BooleanFormula<'arena> {
    label: i32,
    kind: FormulaKind<'arena>,
}

impl<'arena> BooleanFormula<'arena> {
    /// Creates a new formula with the given label and kind
    pub(crate) fn new(label: i32, kind: FormulaKind<'arena>) -> Self {
        Self { label, kind }
    }

    /// Returns the label for this formula
    pub fn label(&self) -> i32 {
        self.label
    }

    /// Returns the kind of this formula
    pub fn kind(&self) -> &FormulaKind<'arena> {
        &self.kind
    }
}

impl<'arena> BooleanValue for BooleanFormula<'arena> {
    fn label(&self) -> i32 {
        self.label
    }
}

/// Formula kind (gate type)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FormulaKind<'arena> {
    /// Multi-input AND gate - handle to slice of BoolValue<'arena>s in arena
    And(Handle<'arena, [BoolValue<'arena>]>),
    /// Multi-input OR gate - handle to slice of BoolValue<'arena>s in arena
    Or(Handle<'arena, [BoolValue<'arena>]>),
    /// NOT gate - handle to BoolValue<'arena> in arena
    Not(Handle<'arena, BoolValue<'arena>>),
    /// If-then-else gate - handles to BoolValue<'arena>s in arena
    Ite {
        /// Condition
        condition: Handle<'arena, BoolValue<'arena>>,
        /// Then branch
        then_val: Handle<'arena, BoolValue<'arena>>,
        /// Else branch
        else_val: Handle<'arena, BoolValue<'arena>>,
    },
}

/// Unified boolean value type
///
/// Encompasses constants, variables, and formulas.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BoolValue<'arena> {
    /// Constant (TRUE or FALSE)
    Constant(BooleanConstant),
    /// Variable
    Variable(BooleanVariable),
    /// Formula (gate)
    Formula(BooleanFormula<'arena>),
}

impl<'arena> BoolValue<'arena> {
    /// Returns the label for this value
    pub fn label(&self) -> i32 {
        match self {
            BoolValue::Constant(c) => c.label(),
            BoolValue::Variable(v) => v.label(),
            BoolValue::Formula(f) => f.label(),
        }
    }

    /// Returns true if this is a constant
    pub fn is_constant(&self) -> bool {
        matches!(self, BoolValue::Constant(_))
    }

    /// Returns true if this is a variable
    pub fn is_variable(&self) -> bool {
        matches!(self, BoolValue::Variable(_))
    }

    /// Returns true if this is a formula
    pub fn is_formula(&self) -> bool {
        matches!(self, BoolValue::Formula(_))
    }
}

impl<'arena> BooleanValue for BoolValue<'arena> {
    fn label(&self) -> i32 {
        self.label()
    }
}

impl<'arena> From<BooleanConstant> for BoolValue<'arena> {
    fn from(c: BooleanConstant) -> Self {
        BoolValue::Constant(c)
    }
}

impl<'arena> From<BooleanVariable> for BoolValue<'arena> {
    fn from(v: BooleanVariable) -> Self {
        BoolValue::Variable(v)
    }
}

impl<'arena> From<BooleanFormula<'arena>> for BoolValue<'arena> {
    fn from(f: BooleanFormula<'arena>) -> Self {
        BoolValue::Formula(f)
    }
}

/// Boolean operators for formulas
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Operator {
    /// Logical AND
    AND,
    /// Logical OR
    OR,
    /// Logical NOT
    NOT,
    /// If-Then-Else (ternary conditional)
    ITE,
}

/// Dimensions for boolean matrices
///
/// Boolean matrices are used to encode relations during translation.
/// Each matrix has a fixed size (rows × columns).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Dimensions {
    rows: usize,
    cols: usize,
}

impl Dimensions {
    /// Creates new dimensions
    pub fn new(rows: usize, cols: usize) -> Self {
        Self { rows, cols }
    }

    /// Creates square dimensions for a relation of given arity over a universe
    /// Following Java: Dimensions.square(universe_size, arity)
    /// Capacity = universe_size^arity
    pub fn square(universe_size: usize, arity: usize) -> Self {
        let capacity = universe_size.pow(arity as u32);
        Self {
            rows: capacity,
            cols: arity,
        }
    }

    /// Returns the number of rows
    pub fn rows(&self) -> usize {
        self.rows
    }

    /// Returns the number of columns
    pub fn cols(&self) -> usize {
        self.cols
    }

    /// Returns the total capacity (number of tuples in the relation)
    /// Note: In this implementation, rows stores the capacity, not rows*cols
    pub fn capacity(&self) -> usize {
        self.rows
    }

    /// Returns the arity (number of columns, i.e., dimensionality)
    pub fn arity(&self) -> usize {
        self.cols
    }

    /// Returns dimension(0) - the size of the first dimension
    /// For uniform relations over a universe of size u with arity n:
    /// capacity = u^n, so u = capacity^(1/n)
    ///
    /// This computes the integer nth root of capacity using binary search.
    pub fn dimension_0(&self) -> usize {
        if self.cols == 1 {
            return self.rows;
        }

        // Binary search for the nth root
        let n = self.cols as u32;
        let capacity = self.rows;

        // Start with reasonable bounds
        let mut low = 1;
        let mut high = capacity;

        while low < high {
            let mid = (low + high).div_ceil(2);
            let pow = mid.pow(n);

            if pow == capacity {
                return mid;
            } else if pow < capacity {
                low = mid;
            } else {
                high = mid - 1;
            }
        }

        low
    }
}

/// Matrix of boolean values
///
/// Used to encode relations during FOL→Boolean translation.
/// Implements sparse storage: only non-FALSE entries are stored.
#[derive(Debug, Clone)]
pub struct BooleanMatrix<'arena> {
    dimensions: Dimensions,
    /// Sparse storage: only non-FALSE entries (index → value)
    cells: FxHashMap<usize, BoolValue<'arena>>,
}

impl<'arena> BooleanMatrix<'arena> {
    /// Creates an empty matrix with the given dimensions (all FALSE)
    pub fn empty(dimensions: Dimensions) -> Self {
        Self {
            dimensions,
            cells: FxHashMap::default(),
        }
    }

    /// Creates a matrix with specific indices marked TRUE
    /// Following Java: BooleanMatrix(Dimensions, BooleanFactory, IntSet, IntSet)
    ///
    /// # Arguments
    /// * `dims` - Matrix dimensions
    /// * `all_indices` - Upper bound indices (domain of possible values)
    /// * `true_indices` - Lower bound indices (definitely TRUE)
    pub fn with_bounds(
        dims: Dimensions,
        _factory: &'arena BooleanFactory,
        all_indices: &[usize],
        true_indices: &[usize],
    ) -> Self {
        let mut cells = FxHashMap::default();

        // Mark lower bound indices as TRUE
        for &idx in true_indices {
            cells.insert(idx, BoolValue::Constant(BooleanConstant::TRUE));
        }

        // Note: all_indices defines the domain, but we don't store FALSE values
        // Variables will be assigned later in LeafInterpreter
        let _ = all_indices; // Suppress warning - used for validation in Java

        Self { dimensions: dims, cells }
    }

    /// Returns the dimensions of this matrix
    pub fn dimensions(&self) -> &Dimensions {
        &self.dimensions
    }

    /// Sets value at flat index
    /// Following Java: BooleanMatrix.set(int, BooleanValue)
    pub fn set(&mut self, index: usize, value: BoolValue<'arena>) {
        if value == BoolValue::Constant(BooleanConstant::FALSE) {
            // Sparse: don't store FALSE
            self.cells.remove(&index);
        } else {
            self.cells.insert(index, value);
        }
    }

    /// Gets value at flat index
    /// Following Java: BooleanMatrix.get(int)
    pub fn get(&self, index: usize) -> BoolValue<'arena> {
        self.cells
            .get(&index)
            .cloned()
            .unwrap_or(BoolValue::Constant(BooleanConstant::FALSE))
    }

    /// Iterates over (index, value) pairs - ONLY non-FALSE entries
    /// Following Java: BooleanMatrix.iterator()
    pub fn iter_indexed(&self) -> impl Iterator<Item = (usize, &BoolValue<'arena>)> + '_ {
        self.cells.iter().map(|(&idx, val)| (idx, val))
    }

    /// Returns the number of non-FALSE entries
    /// Following Java: BooleanMatrix.density()
    pub fn density(&self) -> usize {
        self.cells.len()
    }

    /// Returns the indices where the value is TRUE
    /// Following Java: BooleanMatrix.denseIndices()
    ///
    /// For evaluation results (all constants), this returns indices that are TRUE.
    /// Should only be called after evaluation against an instance where all values
    /// are constants (no variables).
    pub fn dense_indices(&self) -> Vec<usize> {
        self.cells
            .iter()
            .filter_map(|(&idx, val)| {
                if *val == BoolValue::Constant(BooleanConstant::TRUE) {
                    Some(idx)
                } else {
                    None
                }
            })
            .collect()
    }

    /// Gets the element at the given row and column
    pub fn get_at(&self, row: usize, col: usize) -> Option<BoolValue<'arena>> {
        if row < self.dimensions.rows && col < self.dimensions.cols {
            Some(self.get(row * self.dimensions.cols + col))
        } else {
            None
        }
    }

    /// Gets the element at the given row and column, returning FALSE if out of bounds
    pub fn get_row_col(&self, row: usize, col: usize) -> BoolValue<'arena> {
        self.get_at(row, col)
            .unwrap_or(BoolValue::Constant(BooleanConstant::FALSE))
    }

    /// Union (OR) of two matrices
    /// Following Java: BooleanMatrix.or(BooleanMatrix)
    pub fn union(&self, other: &BooleanMatrix<'arena>, factory: &'arena BooleanFactory) -> BooleanMatrix<'arena> {
        assert_eq!(self.dimensions, other.dimensions);
        let mut result = BooleanMatrix::empty(self.dimensions);

        // Add all entries from self
        for (&idx, val) in &self.cells {
            let other_val = other.get(idx);
            result.set(idx, factory.or(val.clone(), other_val));
        }

        // Add entries only in other
        for (&idx, val) in &other.cells {
            if !self.cells.contains_key(&idx) {
                result.set(idx, val.clone());
            }
        }

        result
    }

    /// Intersection (AND) of two matrices
    /// Following Java: BooleanMatrix.and(BooleanMatrix)
    pub fn intersection(&self, other: &BooleanMatrix<'arena>, factory: &'arena BooleanFactory) -> BooleanMatrix<'arena> {
        assert_eq!(self.dimensions, other.dimensions);
        let mut result = BooleanMatrix::empty(self.dimensions);

        // Only entries in BOTH can be non-FALSE
        for (&idx, val) in &self.cells {
            if let Some(other_val) = other.cells.get(&idx) {
                result.set(idx, factory.and(val.clone(), other_val.clone()));
            }
        }

        result
    }

    /// Difference (this AND NOT other)
    /// Following Java: BooleanMatrix.difference(BooleanMatrix)
    pub fn difference(&self, other: &BooleanMatrix<'arena>, factory: &'arena BooleanFactory) -> BooleanMatrix<'arena> {
        assert_eq!(self.dimensions, other.dimensions);
        if self.cells.is_empty() || other.cells.is_empty() {
            return self.clone();
        }

        let mut result = BooleanMatrix::empty(self.dimensions);
        for (&idx, val) in &self.cells {
            let other_val = other.get(idx);
            let not_other = factory.not(other_val);
            result.set(idx, factory.and(val.clone(), not_other));
        }

        result
    }

    /// Element-wise negation
    /// Following Java: BooleanMatrix.not()
    pub fn not(&self, factory: &'arena BooleanFactory) -> BooleanMatrix<'arena> {
        let mut result = BooleanMatrix::empty(self.dimensions);

        for i in 0..self.dimensions.capacity() {
            let v = self.get(i);
            if v == BoolValue::Constant(BooleanConstant::FALSE) {
                // null/absent cell becomes TRUE
                result.set(i, BoolValue::Constant(BooleanConstant::TRUE));
            } else if v != BoolValue::Constant(BooleanConstant::TRUE) {
                // Non-TRUE value gets negated
                result.set(i, factory.not(v));
            }
            // TRUE cells remain absent (FALSE) in result
        }

        result
    }

    /// Join/Dot Product of two matrices
    /// Following Java: BooleanMatrix.dot(BooleanMatrix)
    pub fn join(&self, other: &BooleanMatrix<'arena>, factory: &'arena BooleanFactory) -> BooleanMatrix<'arena> {
        // Result arity: self.arity + other.arity - 2
        // Following Java: Dimensions.dot()
        let result_arity = self.dimensions.arity() + other.dimensions.arity() - 2;

        // Java: b = other.dims.dimension(0)
        let b = other.dimensions.dimension_0();

        // Java: c = other.dims.capacity() / b
        let c = other.dimensions.capacity() / b;

        // Result capacity
        // Following Java: (capacity*dim.capacity) / (drop*drop) where drop = b
        let result_capacity = (self.dimensions.capacity() * other.dimensions.capacity()) / (b * b);

        let result_dims = Dimensions::new(result_capacity, result_arity);
        let mut result = BooleanMatrix::empty(result_dims);

        if self.cells.is_empty() || other.cells.is_empty() {
            return result;
        }

        // Use b and c already calculated above (don't recalculate!)
        for (&i, v0) in &self.cells {
            // For each entry in self at flat index i
            let row_head = (i % b) * c;
            let row_tail = row_head + c - 1;

            // Find matching entries in other
            for (&j, v1) in &other.cells {
                if j >= row_head && j <= row_tail {
                    let product = factory.and(v0.clone(), v1.clone());
                    if product != BoolValue::Constant(BooleanConstant::FALSE) {
                        let k = (i / b) * c + j % c;
                        // Accumulate OR
                        let existing = result.get(k);
                        let new_val = factory.or(existing.clone(), product.clone());
                        result.set(k, new_val);
                    }
                }
            }
        }

        result
    }

    /// Cross Product of two matrices
    /// Following Java: BooleanMatrix.cross(BooleanMatrix)
    pub fn product(&self, other: &BooleanMatrix<'arena>, factory: &'arena BooleanFactory) -> BooleanMatrix<'arena> {
        let result_dims = Dimensions::new(
            self.dimensions.capacity() * other.dimensions.capacity(),
            self.dimensions.cols() + other.dimensions.cols(),
        );
        let mut result = BooleanMatrix::empty(result_dims);

        if self.cells.is_empty() || other.cells.is_empty() {
            return result;
        }

        let other_cap = other.dimensions.capacity();
        for (&i, v0) in &self.cells {
            let base = other_cap * i;
            for (&j, v1) in &other.cells {
                let conjunction = factory.and(v0.clone(), v1.clone());
                result.set(base + j, conjunction);
            }
        }

        result
    }

    /// Transpose of this matrix
    /// Following Java: BooleanMatrix.transpose()
    pub fn transpose(&self, _factory: &'arena BooleanFactory) -> BooleanMatrix<'arena> {
        // For a binary relation, transpose only swaps the elements in each pair
        // The capacity (number of tuples) and arity (dimensionality) remain unchanged
        assert_eq!(self.dimensions.arity(), 2, "transpose only works on binary relations");

        // Compute universe size from capacity = u^2
        let u = self.dimensions.dimension_0();

        let mut result = BooleanMatrix::empty(self.dimensions);

        for (&idx, val) in &self.cells {
            // Convert flat index to (row, col) coordinates
            let row = idx / u;
            let col = idx % u;
            // Swap to (col, row) and convert back to flat index
            let transposed_idx = col * u + row;
            result.set(transposed_idx, val.clone());
        }

        result
    }

    /// Override: combine matrices with precedence
    /// Following Java: BooleanMatrix.override(BooleanMatrix)
    pub fn override_with(&self, other: &BooleanMatrix<'arena>, factory: &'arena BooleanFactory) -> BooleanMatrix<'arena> {
        assert_eq!(self.dimensions, other.dimensions);
        if other.cells.is_empty() {
            return self.clone();
        }

        let mut result = BooleanMatrix::empty(self.dimensions);
        // Start with other's entries
        for (&idx, val) in &other.cells {
            result.set(idx, val.clone());
        }

        let row_length = self.dimensions.capacity() / self.dimensions.dimension_0();
        let mut row = usize::MAX;
        let mut row_val = BoolValue::Constant(BooleanConstant::TRUE);

        for (&idx, val) in &self.cells {
            let e0row = idx / row_length;
            if row != e0row {
                row = e0row;
                // Compute nand of other's values in this row
                row_val = self.nand_row(other, row * row_length, (row + 1) * row_length, factory);
            }
            let current = result.get(idx);
            let conjunction = factory.and(val.clone(), row_val.clone());
            result.set(idx, factory.or(current, conjunction));
        }

        result
    }

    /// Helper: Returns conjunction of negated values in range [start, end)
    /// Following Java: BooleanMatrix.nand(int, int)
    fn nand_row(&self, matrix: &BooleanMatrix<'arena>, start: usize, end: usize, factory: &'arena BooleanFactory) -> BoolValue<'arena> {
        let mut acc = Vec::new();
        for idx in start..end {
            if let Some(val) = matrix.cells.get(&idx) {
                acc.push(factory.not(val.clone()));
            }
        }
        if acc.is_empty() {
            BoolValue::Constant(BooleanConstant::TRUE)
        } else {
            factory.and_multi(acc)
        }
    }

    /// If-then-else choice between matrices
    /// Following Java: BooleanMatrix.choice(BooleanValue, BooleanMatrix)
    /// Returns a matrix m such that m[i] = condition ? this[i] : other[i]
    pub fn choice(&self, condition: BoolValue<'arena>, other: &BooleanMatrix<'arena>, factory: &'arena BooleanFactory) -> BooleanMatrix<'arena> {
        assert_eq!(self.dimensions, other.dimensions);

        // Trivial cases
        if let BoolValue::Constant(c) = condition {
            return match c {
                BooleanConstant::TRUE => self.clone(),
                BooleanConstant::FALSE => other.clone(),
            };
        }

        let mut result = BooleanMatrix::empty(self.dimensions);

        // For each entry in this matrix
        for (&idx, val) in &self.cells {
            if let Some(other_val) = other.cells.get(&idx) {
                // Both have values: use ite
                result.set(idx, factory.ite(condition.clone(), val.clone(), other_val.clone()));
            } else {
                // Only this has value: condition AND val
                result.set(idx, factory.and(condition.clone(), val.clone()));
            }
        }

        // For entries only in other matrix
        for (&idx, val) in &other.cells {
            if !self.cells.contains_key(&idx) {
                // condition ? FALSE : val = NOT(condition) AND val
                result.set(idx, factory.and(factory.not(condition.clone()), val.clone()));
            }
        }

        result
    }

    /// Check equality: all corresponding entries must be equal
    /// Following Java: BooleanMatrix.eq(BooleanMatrix)
    pub fn equals(&self, other: &BooleanMatrix<'arena>, factory: &'arena BooleanFactory) -> BoolValue<'arena> {
        let subset1 = self.subset(other, factory);
        let subset2 = other.subset(self, factory);
        factory.and(subset1, subset2)
    }

    /// Check subset: all entries in self imply corresponding entries in other
    /// Following Java: BooleanMatrix.subset(BooleanMatrix)
    pub fn subset(&self, other: &BooleanMatrix<'arena>, factory: &'arena BooleanFactory) -> BoolValue<'arena> {
        assert_eq!(self.dimensions, other.dimensions);
        let mut acc = Vec::new();

        for (&idx, val) in &self.cells {
            let other_val = other.get(idx);
            let not_val = factory.not(val.clone());
            // self[i] => other[i]  ≡  !self[i] || other[i]
            let implication = factory.or(not_val, other_val);
            acc.push(implication);
        }

        if acc.is_empty() {
            BoolValue::Constant(BooleanConstant::TRUE)
        } else {
            factory.and_multi(acc)
        }
    }

    /// Multiplicity: some (at least one entry is TRUE)
    /// Following Java: BooleanMatrix.some()
    pub fn some(&self, factory: &'arena BooleanFactory) -> BoolValue<'arena> {
        if self.cells.is_empty() {
            return BoolValue::Constant(BooleanConstant::FALSE);
        }

        let values: Vec<BoolValue<'arena>> = self.cells.values().cloned().collect();
        let result = factory.or_multi(values);
        result
    }

    /// Multiplicity: none (all entries are FALSE)
    /// Following Java: BooleanMatrix.none()
    pub fn none(&self, factory: &'arena BooleanFactory) -> BoolValue<'arena> {
        let some_val = self.some(factory);
        let result = factory.not(some_val);
        result
    }

    /// Multiplicity: one (exactly one entry is TRUE)
    /// Following Java: BooleanMatrix.one()
    pub fn one(&self, factory: &'arena BooleanFactory) -> BoolValue<'arena> {
        if self.cells.is_empty() {
            return BoolValue::Constant(BooleanConstant::FALSE);
        }

        let mut constraints = Vec::new();
        let mut partial = BoolValue::Constant(BooleanConstant::FALSE);

        for val in self.cells.values() {
            // Each value implies no previous values were true
            // val => !partial  ≡  !val || !partial
            let not_val = factory.not(val.clone());
            let not_partial = factory.not(partial.clone());
            let constraint = factory.or(not_val, not_partial);
            constraints.push(constraint);
            partial = factory.or(partial, val.clone());
        }

        // At least one must be true
        constraints.push(partial);
        factory.and_multi(constraints)
    }

    /// Transitive closure of a binary relation
    /// Following Java: BooleanMatrix.closure()
    /// Computes R^+ = R ∪ (R.R) ∪ (R.R.R) ∪ ... using iterative squaring
    pub fn closure(&self, factory: &'arena BooleanFactory) -> BooleanMatrix<'arena> {
        assert_eq!(self.dimensions.cols(), 2, "closure requires binary relation");

        if self.cells.is_empty() {
            return self.clone();
        }

        let mut ret = self.clone();

        // Compute the number of rows in the matrix
        let row_factor = self.dimensions.cols();
        let mut seen_rows = std::collections::HashSet::new();

        for &idx in self.cells.keys() {
            let row = idx / row_factor;
            seen_rows.insert(row);
        }
        let row_num = seen_rows.len();

        // Compute closure using iterative squaring: ret = ret OR (ret . ret)
        let mut i = 1;
        while i < row_num {
            let dot_result = ret.join(&ret, factory);
            ret = ret.union(&dot_result, factory);
            i *= 2;
        }

        ret
    }

    /// Reflexive transitive closure
    /// Following Java: R* = IDEN ∪ R^+
    pub fn reflexive_closure(&self, factory: &'arena BooleanFactory, iden: &BooleanMatrix<'arena>) -> BooleanMatrix<'arena> {
        let closure = self.closure(factory);
        closure.union(iden, factory)
    }

    /// Count the number of TRUE entries in this matrix as a boolean circuit
    /// Returns an Int representing the count via popcount circuit
    pub fn popcount(&self, factory: &'arena BooleanFactory) -> Int<'arena> {
        if self.cells.is_empty() {
            let one_bit = BoolValue::Constant(BooleanConstant::TRUE);
            return Int::constant(0, factory.bitwidth(), one_bit);
        }

        // Collect all values from the matrix (only non-FALSE entries)
        let values: Vec<BoolValue<'arena>> = self.cells.values().cloned().collect();

        if values.is_empty() {
            let one_bit = BoolValue::Constant(BooleanConstant::TRUE);
            return Int::constant(0, factory.bitwidth(), one_bit);
        }

        // Use cascaded full adders to sum the values
        // Start with the first value in bit 0
        let mut result_bits: Vec<BoolValue<'arena>> = vec![values[0].clone()];

        // Add remaining values
        for val in &values[1..] {
            // Add current value to the accumulated result
            let mut new_bits = Vec::new();
            let mut carry = BoolValue::Constant(BooleanConstant::FALSE);

            // For each bit position, perform full addition
            for res_bit in result_bits.iter() {
                // sum = res_bit XOR val XOR carry
                let sum = factory.sum(res_bit.clone(), val.clone(), carry.clone());
                new_bits.push(sum);

                // carry = (res_bit AND val) OR (carry AND (res_bit XOR val))
                carry = factory.carry(res_bit.clone(), val.clone(), carry);
            }

            // Add final carry as a new bit if non-zero
            if carry != BoolValue::Constant(BooleanConstant::FALSE) {
                new_bits.push(carry.clone());
            }

            result_bits = new_bits;
        }

        // Pad to factory bitwidth
        while result_bits.len() < factory.bitwidth() {
            result_bits.push(BoolValue::Constant(BooleanConstant::FALSE));
        }

        Int::new(result_bits)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn boolean_constants() {
        assert_eq!(BooleanConstant::TRUE.label(), 0);
        assert_eq!(BooleanConstant::FALSE.label(), -1);
        assert_ne!(BooleanConstant::TRUE, BooleanConstant::FALSE);
    }

    #[test]
    fn boolean_variables() {
        let v1 = BooleanVariable::new(1);
        let v2 = BooleanVariable::new(2);

        assert_eq!(v1.label(), 1);
        assert_ne!(v1, v2);
    }

    #[test]
    #[should_panic(expected = "Variable labels must be positive")]
    fn boolean_variable_must_be_positive() {
        BooleanVariable::new(0);
    }

    #[test]
    #[should_panic(expected = "Variable labels must be positive")]
    fn boolean_variable_cannot_be_negative() {
        BooleanVariable::new(-1);
    }

    #[test]
    fn boolean_formula() {
        let arena = MatrixArena::new();
        let v1 = BoolValue::Variable(BooleanVariable::new(1));
        let v2 = BoolValue::Variable(BooleanVariable::new(2));

        let handle = arena.alloc_slice_handle(&[v1, v2]);
        let formula = BooleanFormula::new(10, FormulaKind::And(handle));
        assert_eq!(formula.label(), 10);
    }

    #[test]
    fn boolean_value_conversions() {
        let c = BoolValue::from(BooleanConstant::TRUE);
        assert!(c.is_constant());
        assert_eq!(c.label(), 0);

        let v = BoolValue::from(BooleanVariable::new(5));
        assert!(v.is_variable());
        assert_eq!(v.label(), 5);
    }

    #[test]
    fn dimensions() {
        // Dimensions::new(capacity, arity)
        // For a binary relation over universe of size 2: capacity=4, arity=2
        let dims = Dimensions::new(4, 2);
        assert_eq!(dims.rows(), 4); // capacity
        assert_eq!(dims.cols(), 2); // arity
        assert_eq!(dims.capacity(), 4);
        assert_eq!(dims.arity(), 2);
    }

    #[test]
    fn boolean_matrix() {
        // Binary relation over universe of size 2: capacity=4 (2²), arity=2
        let dims = Dimensions::new(4, 2);
        let mut matrix = BooleanMatrix::empty(dims);

        // Set some values
        matrix.set(0, BoolValue::Constant(BooleanConstant::TRUE));
        matrix.set(1, BoolValue::Constant(BooleanConstant::FALSE)); // Won't be stored
        matrix.set(2, BoolValue::Variable(BooleanVariable::new(1)));
        matrix.set(3, BoolValue::Variable(BooleanVariable::new(2)));

        assert_eq!(matrix.dimensions().capacity(), 4);
        assert_eq!(matrix.get(0).label(), 0); // TRUE
        assert_eq!(matrix.get(1).label(), -1); // FALSE (not stored)
        assert_eq!(matrix.get(2).label(), 1); // var 1
        assert_eq!(matrix.get(3).label(), 2); // var 2
        assert_eq!(matrix.density(), 3); // Only 3 non-FALSE entries stored
    }

    #[test]
    fn operator_variants() {
        // Just ensure all operators exist
        let _ = [Operator::AND, Operator::OR, Operator::NOT, Operator::ITE];
    }

    #[test]
    fn matrix_choice_trivial_true() {
        // Following Java: BooleanMatrix.choice with TRUE condition
        use crate::bool::factory::{BooleanFactory, Options};

        let factory = BooleanFactory::new(10, Options::default());
        let dims = Dimensions::new(2, 1);

        let mut m1 = BooleanMatrix::empty(dims);
        let mut m2 = BooleanMatrix::empty(dims);

        m1.set(0, factory.variable(1));
        m1.set(1, factory.variable(2));

        m2.set(0, factory.variable(3));
        m2.set(1, factory.variable(4));

        // TRUE ? m1 : m2 = m1
        let result = m1.choice(factory.constant(true), &m2, &factory);

        assert_eq!(result.get(0).label(), 1);
        assert_eq!(result.get(1).label(), 2);
    }

    #[test]
    fn matrix_choice_trivial_false() {
        // Following Java: BooleanMatrix.choice with FALSE condition
        use crate::bool::factory::{BooleanFactory, Options};

        let factory = BooleanFactory::new(10, Options::default());
        let dims = Dimensions::new(2, 1);

        let mut m1 = BooleanMatrix::empty(dims);
        let mut m2 = BooleanMatrix::empty(dims);

        m1.set(0, factory.variable(1));
        m1.set(1, factory.variable(2));

        m2.set(0, factory.variable(3));
        m2.set(1, factory.variable(4));

        // FALSE ? m1 : m2 = m2
        let result = m1.choice(factory.constant(false), &m2, &factory);

        assert_eq!(result.get(0).label(), 3);
        assert_eq!(result.get(1).label(), 4);
    }

    #[test]
    fn matrix_choice_conditional() {
        // Following Java: BooleanMatrix.choice with variable condition
        use crate::bool::factory::{BooleanFactory, Options};

        let factory = BooleanFactory::new(10, Options::default());
        let dims = Dimensions::new(3, 1);

        let mut m1 = BooleanMatrix::empty(dims);
        let mut m2 = BooleanMatrix::empty(dims);

        // m1 has values at indices 0 and 1
        m1.set(0, factory.variable(1));
        m1.set(1, factory.variable(2));

        // m2 has values at indices 1 and 2
        m2.set(1, factory.variable(3));
        m2.set(2, factory.variable(4));

        let cond = factory.variable(5);

        // result = cond ? m1 : m2
        let result = m1.choice(cond.clone(), &m2, &factory);

        // Index 0: only in m1, result should be cond AND v1
        let r0 = result.get(0);
        assert!(r0.is_formula());

        // Index 1: in both, result should be ITE(cond, v1, v3)
        let r1 = result.get(1);
        assert!(r1.is_formula());

        // Index 2: only in m2, result should be NOT(cond) AND v4
        let r2 = result.get(2);
        assert!(r2.is_formula());
    }

    #[test]
    fn matrix_choice_sparse() {
        // Test choice with sparse matrices
        use crate::bool::factory::{BooleanFactory, Options};

        let factory = BooleanFactory::new(10, Options::default());
        let dims = Dimensions::new(10, 1); // Large sparse matrix

        let mut m1 = BooleanMatrix::empty(dims);
        let mut m2 = BooleanMatrix::empty(dims);

        // Only a few entries
        m1.set(0, factory.variable(1));
        m1.set(5, factory.variable(2));

        m2.set(5, factory.variable(3));
        m2.set(9, factory.variable(4));

        let cond = factory.variable(5);
        let result = m1.choice(cond, &m2, &factory);

        // Should only have entries where either m1 or m2 had entries
        assert!(result.density() <= 4);
        assert!(result.get(0).is_formula()); // From m1 only
        assert!(result.get(5).is_formula()); // From both
        assert!(result.get(9).is_formula()); // From m2 only
        assert_eq!(result.get(3).label(), -1); // FALSE (neither had entry)
    }

    #[test]
    fn boolean_constant_boolean_value() {
        assert!(BooleanConstant::TRUE.boolean_value());
        assert!(!BooleanConstant::FALSE.boolean_value());
    }

    #[test]
    fn matrix_dense_indices_all_true() {
        let dims = Dimensions::new(5, 1);

        let mut matrix = BooleanMatrix::empty(dims);
        matrix.set(0, BoolValue::Constant(BooleanConstant::TRUE));
        matrix.set(2, BoolValue::Constant(BooleanConstant::TRUE));
        matrix.set(4, BoolValue::Constant(BooleanConstant::TRUE));

        let indices = matrix.dense_indices();
        assert_eq!(indices.len(), 3);
        assert!(indices.contains(&0));
        assert!(indices.contains(&2));
        assert!(indices.contains(&4));
    }

    #[test]
    fn matrix_dense_indices_mixed() {
        use crate::bool::factory::{BooleanFactory, Options};

        let factory = BooleanFactory::new(5, Options::default());
        let dims = Dimensions::new(5, 1);

        let mut matrix = BooleanMatrix::empty(dims);
        matrix.set(0, BoolValue::Constant(BooleanConstant::TRUE));
        matrix.set(1, factory.variable(1)); // Variable, not TRUE
        matrix.set(2, BoolValue::Constant(BooleanConstant::TRUE));
        matrix.set(3, BoolValue::Constant(BooleanConstant::FALSE));

        let indices = matrix.dense_indices();
        // Should only include indices with TRUE constants
        assert_eq!(indices.len(), 2);
        assert!(indices.contains(&0));
        assert!(indices.contains(&2));
        assert!(!indices.contains(&1)); // Variable, not included
        assert!(!indices.contains(&3)); // FALSE, not included
    }

    #[test]
    fn matrix_dense_indices_empty() {
        let dims = Dimensions::new(5, 1);
        let matrix = BooleanMatrix::<'_>::empty(dims);

        let indices = matrix.dense_indices();
        assert_eq!(indices.len(), 0);
    }
}
