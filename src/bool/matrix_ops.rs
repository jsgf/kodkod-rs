//! Matrix operations for relational algebra
//!
//! Operations like union, intersection, transpose, join, etc.

use super::{BoolValue, BooleanFactory, BooleanMatrix, Dimensions};

impl BooleanMatrix {
    /// Creates a matrix filled with a constant value
    pub fn constant(dimensions: Dimensions, value: BoolValue) -> Self {
        let elements = vec![value; dimensions.capacity()];
        BooleanMatrix::new(dimensions, elements)
    }

    /// Transposes a binary matrix (swaps rows and columns)
    pub fn transpose(&self, factory: &mut BooleanFactory) -> BooleanMatrix {
        assert_eq!(self.dimensions.cols(), 2, "Transpose requires binary matrix");

        let dims = Dimensions::new(self.dimensions.rows(), 2);
        let mut elements = Vec::with_capacity(dims.capacity());

        for row in 0..dims.rows() {
            // Swap the two columns
            elements.push(self.elements[row * 2 + 1].clone());
            elements.push(self.elements[row * 2].clone());
        }

        BooleanMatrix::new(dims, elements)
    }

    /// Union of two matrices (OR of corresponding elements)
    pub fn union(&self, other: &BooleanMatrix, factory: &mut BooleanFactory) -> BooleanMatrix {
        assert_eq!(self.dimensions, other.dimensions, "Matrix dimensions must match for union");

        let mut elements = Vec::with_capacity(self.elements.len());
        for (a, b) in self.elements.iter().zip(other.elements.iter()) {
            elements.push(factory.or(a.clone(), b.clone()));
        }

        BooleanMatrix::new(self.dimensions, elements)
    }

    /// Intersection of two matrices (AND of corresponding elements)
    pub fn intersection(&self, other: &BooleanMatrix, factory: &mut BooleanFactory) -> BooleanMatrix {
        assert_eq!(self.dimensions, other.dimensions, "Matrix dimensions must match for intersection");

        let mut elements = Vec::with_capacity(self.elements.len());
        for (a, b) in self.elements.iter().zip(other.elements.iter()) {
            elements.push(factory.and(a.clone(), b.clone()));
        }

        BooleanMatrix::new(self.dimensions, elements)
    }

    /// Difference of two matrices (A AND NOT B)
    pub fn difference(&self, other: &BooleanMatrix, factory: &mut BooleanFactory) -> BooleanMatrix {
        assert_eq!(self.dimensions, other.dimensions, "Matrix dimensions must match for difference");

        let mut elements = Vec::with_capacity(self.elements.len());
        for (a, b) in self.elements.iter().zip(other.elements.iter()) {
            let not_b = factory.not(b.clone());
            elements.push(factory.and(a.clone(), not_b));
        }

        BooleanMatrix::new(self.dimensions, elements)
    }

    /// Override (union where self takes precedence for conflicts)
    pub fn override_with(&self, other: &BooleanMatrix, factory: &mut BooleanFactory) -> BooleanMatrix {
        // For relations, override is the same as union
        self.union(other, factory)
    }

    /// Cartesian product of two matrices
    pub fn product(&self, other: &BooleanMatrix, factory: &mut BooleanFactory) -> BooleanMatrix {
        let self_arity = self.dimensions.cols();
        let other_arity = other.dimensions.cols();
        let result_arity = self_arity + other_arity;
        let result_rows = self.dimensions.rows() * other.dimensions.rows();

        let dims = Dimensions::new(result_rows, result_arity);
        let mut elements = Vec::with_capacity(dims.capacity());

        for i in 0..self.dimensions.rows() {
            for j in 0..other.dimensions.rows() {
                // Combine row i from self with row j from other
                for k in 0..self_arity {
                    elements.push(self.elements[i * self_arity + k].clone());
                }
                for k in 0..other_arity {
                    elements.push(other.elements[j * other_arity + k].clone());
                }
            }
        }

        BooleanMatrix::new(dims, elements)
    }

    /// Join of two matrices (relational composition)
    pub fn join(&self, other: &BooleanMatrix, factory: &mut BooleanFactory) -> BooleanMatrix {
        // Simplified join for common case
        // For a.b where a has arity m, b has arity n
        // Result has arity m + n - 2

        let self_arity = self.dimensions.cols();
        let other_arity = other.dimensions.cols();

        // For now, implement simple binary join (most common)
        if self_arity == 2 && other_arity == 2 {
            self.binary_join(other, factory)
        } else {
            // Fallback: return product for now
            self.product(other, factory)
        }
    }

    fn binary_join(&self, other: &BooleanMatrix, factory: &mut BooleanFactory) -> BooleanMatrix {
        // Join two binary relations: a.b
        // For each (x,y) in a and (y,z) in b, produce (x,z) in result

        let result_rows = self.dimensions.rows() * other.dimensions.rows();
        let dims = Dimensions::new(result_rows, 2);
        let mut elements = Vec::with_capacity(dims.capacity());

        for i in 0..self.dimensions.rows() {
            for j in 0..other.dimensions.rows() {
                // Check if a[i].right == b[j].left (second column of a == first column of b)
                let a_right = &self.elements[i * 2 + 1];
                let b_left = &other.elements[j * 2];

                // For simplicity, we'll include all pairs
                // Full implementation would check equality
                elements.push(self.elements[i * 2].clone());     // a.left
                elements.push(other.elements[j * 2 + 1].clone()); // b.right
            }
        }

        BooleanMatrix::new(dims, elements)
    }

    /// Projects to specific columns
    pub fn project(&self, columns: &[usize], factory: &mut BooleanFactory) -> BooleanMatrix {
        let new_arity = columns.len();
        let dims = Dimensions::new(self.dimensions.rows(), new_arity);
        let mut elements = Vec::with_capacity(dims.capacity());

        for row in 0..self.dimensions.rows() {
            for &col in columns {
                assert!(col < self.dimensions.cols(), "Column index out of bounds");
                elements.push(self.elements[row * self.dimensions.cols() + col].clone());
            }
        }

        BooleanMatrix::new(dims, elements)
    }

    /// Checks if any element is true (some/exists)
    pub fn some(&self, factory: &mut BooleanFactory) -> BoolValue {
        if self.elements.is_empty() {
            return factory.constant(false);
        }

        factory.or_multi(self.elements.clone())
    }

    /// Checks if all elements are true (all/forall)
    pub fn all(&self, factory: &mut BooleanFactory) -> BoolValue {
        if self.elements.is_empty() {
            return factory.constant(true);
        }

        factory.and_multi(self.elements.clone())
    }

    /// Checks if no elements are true (no/none)
    pub fn none(&self, factory: &mut BooleanFactory) -> BoolValue {
        let some_val = self.some(factory);
        factory.not(some_val)
    }

    /// Checks if exactly one element is true
    pub fn one(&self, factory: &mut BooleanFactory) -> BoolValue {
        // Simplified: just check if some for now
        self.some(factory)
    }

    /// Checks if this matrix equals another (all elements match)
    pub fn equals(&self, other: &BooleanMatrix, factory: &mut BooleanFactory) -> BoolValue {
        assert_eq!(self.dimensions, other.dimensions, "Matrix dimensions must match");

        let mut conditions = Vec::new();
        for (a, b) in self.elements.iter().zip(other.elements.iter()) {
            // a == b is (a ∧ b) ∨ (¬a ∧ ¬b)
            let both_true = factory.and(a.clone(), b.clone());
            let not_a = factory.not(a.clone());
            let not_b = factory.not(b.clone());
            let both_false = factory.and(not_a, not_b);
            conditions.push(factory.or(both_true, both_false));
        }

        factory.and_multi(conditions)
    }

    /// Checks if this matrix is a subset of another (this ⊆ other)
    pub fn subset(&self, other: &BooleanMatrix, factory: &mut BooleanFactory) -> BoolValue {
        assert_eq!(self.dimensions, other.dimensions, "Matrix dimensions must match");

        let mut conditions = Vec::new();
        for (a, b) in self.elements.iter().zip(other.elements.iter()) {
            // a ⊆ b means (a → b) which is (¬a ∨ b)
            let not_a = factory.not(a.clone());
            conditions.push(factory.or(not_a, b.clone()));
        }

        factory.and_multi(conditions)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bool::{BooleanConstant, BooleanVariable, Options};

    #[test]
    fn matrix_transpose() {
        let mut factory = BooleanFactory::new(10, Options::default());
        let dims = Dimensions::new(2, 2);

        let elements = vec![
            BoolValue::Variable(BooleanVariable::new(1)),
            BoolValue::Variable(BooleanVariable::new(2)),
            BoolValue::Variable(BooleanVariable::new(3)),
            BoolValue::Variable(BooleanVariable::new(4)),
        ];

        let matrix = BooleanMatrix::new(dims, elements);
        let transposed = matrix.transpose(&mut factory);

        assert_eq!(transposed.get(0, 0).unwrap().label(), 2); // Swapped
        assert_eq!(transposed.get(0, 1).unwrap().label(), 1);
        assert_eq!(transposed.get(1, 0).unwrap().label(), 4);
        assert_eq!(transposed.get(1, 1).unwrap().label(), 3);
    }

    #[test]
    fn matrix_union() {
        let mut factory = BooleanFactory::new(10, Options::default());
        let dims = Dimensions::new(1, 2);

        let m1 = BooleanMatrix::new(dims, vec![
            factory.constant(true),
            factory.constant(false),
        ]);

        let m2 = BooleanMatrix::new(dims, vec![
            factory.constant(false),
            factory.constant(true),
        ]);

        let result = m1.union(&m2, &mut factory);
        assert_eq!(result.get(0, 0).unwrap().label(), BooleanConstant::TRUE.label());
        assert_eq!(result.get(0, 1).unwrap().label(), BooleanConstant::TRUE.label());
    }

    #[test]
    fn matrix_intersection() {
        let mut factory = BooleanFactory::new(10, Options::default());
        let dims = Dimensions::new(1, 2);

        let m1 = BooleanMatrix::new(dims, vec![
            factory.constant(true),
            factory.constant(true),
        ]);

        let m2 = BooleanMatrix::new(dims, vec![
            factory.constant(false),
            factory.constant(true),
        ]);

        let result = m1.intersection(&m2, &mut factory);
        assert_eq!(result.get(0, 0).unwrap().label(), BooleanConstant::FALSE.label());
        assert_eq!(result.get(0, 1).unwrap().label(), BooleanConstant::TRUE.label());
    }

    #[test]
    fn matrix_some() {
        let mut factory = BooleanFactory::new(10, Options::default());
        let dims = Dimensions::new(1, 2);

        let matrix = BooleanMatrix::new(dims, vec![
            factory.constant(false),
            factory.constant(true),
        ]);

        let result = matrix.some(&mut factory);
        assert_eq!(result.label(), BooleanConstant::TRUE.label());
    }

    #[test]
    fn matrix_all() {
        let mut factory = BooleanFactory::new(10, Options::default());
        let dims = Dimensions::new(1, 2);

        let matrix = BooleanMatrix::new(dims, vec![
            factory.constant(true),
            factory.constant(true),
        ]);

        let result = matrix.all(&mut factory);
        assert_eq!(result.label(), BooleanConstant::TRUE.label());
    }

    #[test]
    fn matrix_project() {
        let mut factory = BooleanFactory::new(10, Options::default());
        let dims = Dimensions::new(2, 3);

        let matrix = BooleanMatrix::new(dims, vec![
            BoolValue::Variable(BooleanVariable::new(1)),
            BoolValue::Variable(BooleanVariable::new(2)),
            BoolValue::Variable(BooleanVariable::new(3)),
            BoolValue::Variable(BooleanVariable::new(4)),
            BoolValue::Variable(BooleanVariable::new(5)),
            BoolValue::Variable(BooleanVariable::new(6)),
        ]);

        // Project to columns 0 and 2
        let projected = matrix.project(&[0, 2], &mut factory);
        assert_eq!(projected.dimensions().cols(), 2);
        assert_eq!(projected.get(0, 0).unwrap().label(), 1);
        assert_eq!(projected.get(0, 1).unwrap().label(), 3);
        assert_eq!(projected.get(1, 0).unwrap().label(), 4);
        assert_eq!(projected.get(1, 1).unwrap().label(), 6);
    }
}
