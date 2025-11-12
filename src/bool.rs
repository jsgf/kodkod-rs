//! Boolean circuit representation
//!
//! The boolean layer is the intermediate representation used when translating
//! first-order logic formulas to CNF for SAT solving.
//!
//! Key types:
//! - `BooleanValue`: Trait for all boolean values (constants, variables, formulas)
//! - `BooleanConstant`: TRUE (label 0) or FALSE (label -1)
//! - `BooleanVariable`: Variables with positive integer labels
//! - `Operator`: Boolean operators (AND, OR, NOT, ITE)
//! - `Dimensions`: Matrix dimensions for relation encoding

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
    fn dimensions() {
        let dims = Dimensions::new(2, 3);
        assert_eq!(dims.rows(), 2);
        assert_eq!(dims.cols(), 3);
        assert_eq!(dims.capacity(), 6);
    }

    #[test]
    fn operator_variants() {
        // Just ensure all operators exist
        let _ops = vec![Operator::AND, Operator::OR, Operator::NOT, Operator::ITE];
    }
}
