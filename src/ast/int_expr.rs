//! Integer expression types

use super::{Decls, Expression, Formula};

/// Binary operators for integer expressions
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntBinaryOp {
    /// Addition
    Plus,
    /// Subtraction
    Minus,
    /// Multiplication
    Multiply,
    /// Division
    Divide,
    /// Modulo
    Modulo,
    /// Bitwise AND
    And,
    /// Bitwise OR
    Or,
    /// Bitwise XOR
    Xor,
    /// Shift left
    Shl,
    /// Shift right (arithmetic)
    Shr,
    /// Shift right (unsigned)
    Sha,
}

/// Unary operators for integer expressions
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntUnaryOp {
    /// Negation
    Negate,
    /// Absolute value
    Abs,
    /// Sign (-1, 0, or 1)
    Sgn,
    /// Bitwise NOT
    Not,
}

/// Integer comparison operators
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntCompareOp {
    /// Equal
    Eq,
    /// Less than
    Lt,
    /// Less than or equal
    Lte,
    /// Greater than
    Gt,
    /// Greater than or equal
    Gte,
}

/// An expression that evaluates to an integer
#[expect(missing_docs)]
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum IntExpression {
    /// Integer constant
    Constant(i32),
    /// Binary operation
    Binary {
        left: Box<IntExpression>,
        op: IntBinaryOp,
        right: Box<IntExpression>,
    },
    /// Unary operation
    Unary {
        op: IntUnaryOp,
        expr: Box<IntExpression>,
    },
    /// N-ary sum
    Nary {
        exprs: Vec<IntExpression>,
    },
    /// Cardinality of an expression (#expr)
    Cardinality(Expression),
    /// Sum over declarations
    Sum {
        decls: Decls,
        expr: Box<IntExpression>,
    },
    /// If-then-else for integers
    If {
        condition: Box<Formula>,
        then_expr: Box<IntExpression>,
        else_expr: Box<IntExpression>,
    },
    /// Cast expression to int (for bitset representation)
    ExprCast(Expression),
}

impl IntExpression {
    /// Integer constant
    pub fn constant(value: i32) -> Self {
        IntExpression::Constant(value)
    }

    /// Addition
    pub fn plus(self, other: IntExpression) -> Self {
        IntExpression::Binary {
            left: Box::new(self),
            op: IntBinaryOp::Plus,
            right: Box::new(other),
        }
    }

    /// Subtraction
    pub fn minus(self, other: IntExpression) -> Self {
        IntExpression::Binary {
            left: Box::new(self),
            op: IntBinaryOp::Minus,
            right: Box::new(other),
        }
    }

    /// Multiplication
    pub fn multiply(self, other: IntExpression) -> Self {
        IntExpression::Binary {
            left: Box::new(self),
            op: IntBinaryOp::Multiply,
            right: Box::new(other),
        }
    }

    /// Division
    pub fn divide(self, other: IntExpression) -> Self {
        IntExpression::Binary {
            left: Box::new(self),
            op: IntBinaryOp::Divide,
            right: Box::new(other),
        }
    }

    /// Modulo
    pub fn modulo(self, other: IntExpression) -> Self {
        IntExpression::Binary {
            left: Box::new(self),
            op: IntBinaryOp::Modulo,
            right: Box::new(other),
        }
    }

    /// Negation
    pub fn negate(self) -> Self {
        IntExpression::Unary {
            op: IntUnaryOp::Negate,
            expr: Box::new(self),
        }
    }

    /// Absolute value
    pub fn abs(self) -> Self {
        IntExpression::Unary {
            op: IntUnaryOp::Abs,
            expr: Box::new(self),
        }
    }

    /// N-ary sum
    pub fn sum_all(exprs: Vec<IntExpression>) -> Self {
        assert!(!exprs.is_empty(), "Cannot create empty sum");
        if exprs.len() == 1 {
            return exprs.into_iter().next().unwrap();
        }
        IntExpression::Nary { exprs }
    }

    /// Sum over declarations
    pub fn sum(decls: Decls, expr: IntExpression) -> Self {
        IntExpression::Sum {
            decls,
            expr: Box::new(expr),
        }
    }

    /// Equal to
    pub fn eq(self, other: IntExpression) -> Formula {
        Formula::IntComparison {
            left: Box::new(self),
            op: IntCompareOp::Eq,
            right: Box::new(other),
        }
    }

    /// Less than
    pub fn lt(self, other: IntExpression) -> Formula {
        Formula::IntComparison {
            left: Box::new(self),
            op: IntCompareOp::Lt,
            right: Box::new(other),
        }
    }

    /// Less than or equal
    pub fn lte(self, other: IntExpression) -> Formula {
        Formula::IntComparison {
            left: Box::new(self),
            op: IntCompareOp::Lte,
            right: Box::new(other),
        }
    }

    /// Greater than
    pub fn gt(self, other: IntExpression) -> Formula {
        Formula::IntComparison {
            left: Box::new(self),
            op: IntCompareOp::Gt,
            right: Box::new(other),
        }
    }

    /// Greater than or equal
    pub fn gte(self, other: IntExpression) -> Formula {
        Formula::IntComparison {
            left: Box::new(self),
            op: IntCompareOp::Gte,
            right: Box::new(other),
        }
    }
}

impl Expression {
    /// Cardinality (#expr)
    pub fn count(self) -> IntExpression {
        IntExpression::Cardinality(self)
    }

    /// Sum of expression values over declarations
    pub fn sum(self, decls: Decls) -> IntExpression {
        IntExpression::Sum {
            decls,
            expr: Box::new(IntExpression::ExprCast(self)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::{Expression, Formula, Relation, Variable, Decl};
    use super::*;

    #[test]
    fn int_constants() {
        let i = IntExpression::constant(42);
        assert!(matches!(i, IntExpression::Constant(42)));
    }

    #[test]
    fn int_arithmetic() {
        let a = IntExpression::constant(10);
        let b = IntExpression::constant(5);

        let sum = a.clone().plus(b.clone());
        assert!(matches!(sum, IntExpression::Binary { op: IntBinaryOp::Plus, .. }));

        let diff = a.clone().minus(b.clone());
        assert!(matches!(diff, IntExpression::Binary { op: IntBinaryOp::Minus, .. }));

        let prod = a.clone().multiply(b.clone());
        assert!(matches!(prod, IntExpression::Binary { op: IntBinaryOp::Multiply, .. }));

        let quot = a.divide(b);
        assert!(matches!(quot, IntExpression::Binary { op: IntBinaryOp::Divide, .. }));
    }

    #[test]
    fn int_unary() {
        let a = IntExpression::constant(-5);

        let neg = a.clone().negate();
        assert!(matches!(neg, IntExpression::Unary { op: IntUnaryOp::Negate, .. }));

        let abs = a.abs();
        assert!(matches!(abs, IntExpression::Unary { op: IntUnaryOp::Abs, .. }));
    }

    #[test]
    fn int_comparisons() {
        let a = IntExpression::constant(10);
        let b = IntExpression::constant(5);

        let eq = a.clone().eq(b.clone());
        assert!(matches!(eq, Formula::IntComparison { op: IntCompareOp::Eq, .. }));

        let lt = a.clone().lt(b.clone());
        assert!(matches!(lt, Formula::IntComparison { op: IntCompareOp::Lt, .. }));

        let gt = a.gt(b);
        assert!(matches!(gt, Formula::IntComparison { op: IntCompareOp::Gt, .. }));
    }

    #[test]
    fn cardinality() {
        let r = Relation::unary("Person");
        let card = Expression::from(r).count();
        assert!(matches!(card, IntExpression::Cardinality(_)));
    }

    #[test]
    fn sum_expression() {
        let person = Relation::unary("Person");
        let x = Variable::unary("x");
        let decl = Decl::one_of(x, Expression::from(&person));
        let decls = Decls::from(decl);

        let sum = Expression::from(person).sum(decls);
        assert!(matches!(sum, IntExpression::Sum { .. }));
    }

    #[test]
    fn nary_sum() {
        let a = IntExpression::constant(1);
        let b = IntExpression::constant(2);
        let c = IntExpression::constant(3);

        let sum = IntExpression::sum_all(vec![a, b, c]);
        assert!(matches!(sum, IntExpression::Nary { .. }));
    }
}
