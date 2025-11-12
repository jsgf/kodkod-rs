//! Boolean circuit representation
//!
//! The boolean layer is the intermediate representation used when translating
//! first-order logic formulas to CNF for SAT solving.
//!
//! Key types:
//! - `BooleanValue`: Trait for all boolean values (constants, variables, formulas)
//! - `BooleanConstant`: TRUE (label 0) or FALSE (label -1)
//! - `BooleanVariable`: Variables with positive integer labels
//! - `BoolValue`: Enum encompassing all boolean value types
//! - `BooleanFormula`: Boolean gates (AND, OR, NOT, ITE)
//! - `Operator`: Boolean operators
//! - `Dimensions`: Matrix dimensions for relation encoding
//! - `BooleanMatrix`: Matrix of boolean values
//! - `BooleanFactory`: Factory for creating and caching boolean circuits

mod factory;
mod matrix_ops;

pub use factory::{BooleanFactory, Options};

use std::sync::Arc;

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
}

impl BooleanValue for BooleanConstant {
    fn label(&self) -> i32 {
        self.label()
    }
}

/// Boolean variable with a positive integer label
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
/// Formulas are reference-counted for identity-based equality and caching.
#[derive(Debug, Clone)]
pub struct BooleanFormula {
    inner: Arc<BooleanFormulaInner>,
}

impl BooleanFormula {
    /// Creates a new formula with the given label and kind
    pub(crate) fn new(label: i32, kind: FormulaKind) -> Self {
        Self {
            inner: Arc::new(BooleanFormulaInner { label, kind }),
        }
    }

    /// Returns the label for this formula
    pub fn label(&self) -> i32 {
        self.inner.label
    }

    /// Returns the kind of this formula
    pub fn kind(&self) -> &FormulaKind {
        &self.inner.kind
    }
}

impl PartialEq for BooleanFormula {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.inner, &other.inner)
    }
}

impl Eq for BooleanFormula {}

impl std::hash::Hash for BooleanFormula {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        Arc::as_ptr(&self.inner).hash(state);
    }
}

impl BooleanValue for BooleanFormula {
    fn label(&self) -> i32 {
        self.inner.label
    }
}

#[derive(Debug)]
struct BooleanFormulaInner {
    label: i32,
    kind: FormulaKind,
}

/// Formula kind (gate type)
#[derive(Debug, Clone)]
pub enum FormulaKind {
    /// Multi-input AND gate
    And(Vec<BoolValue>),
    /// Multi-input OR gate
    Or(Vec<BoolValue>),
    /// NOT gate
    Not(Box<BoolValue>),
    /// If-then-else gate
    Ite {
        /// Condition
        condition: Box<BoolValue>,
        /// Then branch
        then_val: Box<BoolValue>,
        /// Else branch
        else_val: Box<BoolValue>,
    },
}

/// Unified boolean value type
///
/// Encompasses constants, variables, and formulas.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BoolValue {
    /// Constant (TRUE or FALSE)
    Constant(BooleanConstant),
    /// Variable
    Variable(BooleanVariable),
    /// Formula (gate)
    Formula(BooleanFormula),
}

impl BoolValue {
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

impl BooleanValue for BoolValue {
    fn label(&self) -> i32 {
        self.label()
    }
}

impl From<BooleanConstant> for BoolValue {
    fn from(c: BooleanConstant) -> Self {
        BoolValue::Constant(c)
    }
}

impl From<BooleanVariable> for BoolValue {
    fn from(v: BooleanVariable) -> Self {
        BoolValue::Variable(v)
    }
}

impl From<BooleanFormula> for BoolValue {
    fn from(f: BooleanFormula) -> Self {
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

    /// Returns the number of rows
    pub fn rows(&self) -> usize {
        self.rows
    }

    /// Returns the number of columns
    pub fn cols(&self) -> usize {
        self.cols
    }

    /// Returns the total capacity (rows × cols)
    pub fn capacity(&self) -> usize {
        self.rows * self.cols
    }
}

/// Matrix of boolean values
///
/// Used to encode relations during FOL→Boolean translation.
#[derive(Debug, Clone)]
pub struct BooleanMatrix {
    dimensions: Dimensions,
    elements: Vec<BoolValue>,
}

impl BooleanMatrix {
    /// Creates a new boolean matrix with the given dimensions and elements
    pub fn new(dimensions: Dimensions, elements: Vec<BoolValue>) -> Self {
        assert_eq!(
            dimensions.capacity(),
            elements.len(),
            "Element count must match matrix capacity"
        );
        Self {
            dimensions,
            elements,
        }
    }

    /// Returns the dimensions of this matrix
    pub fn dimensions(&self) -> &Dimensions {
        &self.dimensions
    }

    /// Returns the elements of this matrix
    pub fn elements(&self) -> &[BoolValue] {
        &self.elements
    }

    /// Gets the element at the given row and column
    pub fn get(&self, row: usize, col: usize) -> Option<&BoolValue> {
        if row < self.dimensions.rows && col < self.dimensions.cols {
            self.elements.get(row * self.dimensions.cols + col)
        } else {
            None
        }
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
        let v1 = BoolValue::Variable(BooleanVariable::new(1));
        let v2 = BoolValue::Variable(BooleanVariable::new(2));

        let formula = BooleanFormula::new(10, FormulaKind::And(vec![v1, v2]));
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
        let dims = Dimensions::new(2, 3);
        assert_eq!(dims.rows(), 2);
        assert_eq!(dims.cols(), 3);
        assert_eq!(dims.capacity(), 6);
    }

    #[test]
    fn boolean_matrix() {
        let dims = Dimensions::new(2, 2);
        let elements = vec![
            BoolValue::Constant(BooleanConstant::TRUE),
            BoolValue::Constant(BooleanConstant::FALSE),
            BoolValue::Variable(BooleanVariable::new(1)),
            BoolValue::Variable(BooleanVariable::new(2)),
        ];

        let matrix = BooleanMatrix::new(dims, elements);
        assert_eq!(matrix.dimensions().capacity(), 4);
        assert_eq!(matrix.get(0, 0).unwrap().label(), 0); // TRUE
        assert_eq!(matrix.get(0, 1).unwrap().label(), -1); // FALSE
        assert_eq!(matrix.get(1, 0).unwrap().label(), 1); // var 1
        assert_eq!(matrix.get(1, 1).unwrap().label(), 2); // var 2
    }

    #[test]
    fn operator_variants() {
        // Just ensure all operators exist
        let _ops = vec![Operator::AND, Operator::OR, Operator::NOT, Operator::ITE];
    }
}
