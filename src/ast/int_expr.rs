//! Integer expression types

use std::rc::Rc;
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

/// An expression that evaluates to an integer (reference-counted for efficient sharing)
#[derive(Clone, Debug)]
pub struct IntExpression(Rc<IntExpressionInner>);

impl PartialEq for IntExpression {
    fn eq(&self, other: &Self) -> bool {
        self.0.as_ref() == other.0.as_ref()
    }
}

impl Eq for IntExpression {}

impl std::hash::Hash for IntExpression {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.as_ref().hash(state);
    }
}

/// Inner representation of an integer expression
#[expect(missing_docs)]
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum IntExpressionInner {
    /// Integer constant
    Constant(i32),
    /// Binary operation
    Binary {
        left: IntExpression,
        op: IntBinaryOp,
        right: IntExpression,
    },
    /// Unary operation
    Unary {
        op: IntUnaryOp,
        expr: IntExpression,
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
        expr: IntExpression,
    },
    /// If-then-else for integers
    If {
        condition: Formula,
        then_expr: IntExpression,
        else_expr: IntExpression,
    },
    /// Cast expression to int (for bitset representation)
    ExprCast(Expression),
}

impl IntExpression {
    /// Returns a reference to the inner expression
    pub fn inner(&self) -> &IntExpressionInner {
        &self.0
    }

    /// Returns a raw pointer to the inner expression for identity-based caching
    pub fn as_ptr(&self) -> *const IntExpressionInner {
        Rc::as_ptr(&self.0)
    }

    /// Integer constant
    pub fn constant(value: i32) -> Self {
        IntExpression(Rc::new(IntExpressionInner::Constant(value)))
    }

    /// Addition
    pub fn plus(self, other: IntExpression) -> Self {
        IntExpression(Rc::new(IntExpressionInner::Binary {
            left: self,
            op: IntBinaryOp::Plus,
            right: other,
        }))
    }

    /// Subtraction
    pub fn minus(self, other: IntExpression) -> Self {
        IntExpression(Rc::new(IntExpressionInner::Binary {
            left: self,
            op: IntBinaryOp::Minus,
            right: other,
        }))
    }

    /// Multiplication
    pub fn multiply(self, other: IntExpression) -> Self {
        IntExpression(Rc::new(IntExpressionInner::Binary {
            left: self,
            op: IntBinaryOp::Multiply,
            right: other,
        }))
    }

    /// Division
    pub fn divide(self, other: IntExpression) -> Self {
        IntExpression(Rc::new(IntExpressionInner::Binary {
            left: self,
            op: IntBinaryOp::Divide,
            right: other,
        }))
    }

    /// Modulo
    pub fn modulo(self, other: IntExpression) -> Self {
        IntExpression(Rc::new(IntExpressionInner::Binary {
            left: self,
            op: IntBinaryOp::Modulo,
            right: other,
        }))
    }

    /// Generic binary operation
    pub fn binary(left: IntExpression, op: IntBinaryOp, right: IntExpression) -> Self {
        IntExpression(Rc::new(IntExpressionInner::Binary { left, op, right }))
    }

    /// Generic unary operation
    pub fn unary(op: IntUnaryOp, expr: IntExpression) -> Self {
        IntExpression(Rc::new(IntExpressionInner::Unary { op, expr }))
    }

    /// Negation
    pub fn negate(self) -> Self {
        IntExpression(Rc::new(IntExpressionInner::Unary {
            op: IntUnaryOp::Negate,
            expr: self,
        }))
    }

    /// Absolute value
    pub fn abs(self) -> Self {
        IntExpression(Rc::new(IntExpressionInner::Unary {
            op: IntUnaryOp::Abs,
            expr: self,
        }))
    }

    /// N-ary sum
    pub fn sum_all(exprs: Vec<IntExpression>) -> Self {
        assert!(!exprs.is_empty(), "Cannot create empty sum");
        if exprs.len() == 1 {
            return exprs.into_iter().next().unwrap();
        }
        IntExpression(Rc::new(IntExpressionInner::Nary { exprs }))
    }

    /// Sum over declarations
    pub fn sum(decls: Decls, expr: IntExpression) -> Self {
        IntExpression(Rc::new(IntExpressionInner::Sum { decls, expr }))
    }

    /// Cardinality of an expression
    pub fn cardinality(expr: Expression) -> Self {
        IntExpression(Rc::new(IntExpressionInner::Cardinality(expr)))
    }

    /// Cast expression to int
    pub fn expr_cast(expr: Expression) -> Self {
        IntExpression(Rc::new(IntExpressionInner::ExprCast(expr)))
    }

    /// If-then-else for integers
    pub fn if_then_else(condition: Formula, then_expr: IntExpression, else_expr: IntExpression) -> Self {
        IntExpression(Rc::new(IntExpressionInner::If { condition, then_expr, else_expr }))
    }

    /// Equal to
    pub fn eq(self, other: IntExpression) -> Formula {
        Formula::int_comparison(self, IntCompareOp::Eq, other)
    }

    /// Less than
    pub fn lt(self, other: IntExpression) -> Formula {
        Formula::int_comparison(self, IntCompareOp::Lt, other)
    }

    /// Less than or equal
    pub fn lte(self, other: IntExpression) -> Formula {
        Formula::int_comparison(self, IntCompareOp::Lte, other)
    }

    /// Greater than
    pub fn gt(self, other: IntExpression) -> Formula {
        Formula::int_comparison(self, IntCompareOp::Gt, other)
    }

    /// Greater than or equal
    pub fn gte(self, other: IntExpression) -> Formula {
        Formula::int_comparison(self, IntCompareOp::Gte, other)
    }

    /// Convert to an expression representing a singleton set containing the atom for this integer
    pub fn to_expression(self) -> Expression {
        Expression::int_to_expr(self, super::IntCastOp::IntCast)
    }

    /// Convert to an expression representing the set of powers of 2 (bits) in this integer
    pub fn to_bitset(self) -> Expression {
        Expression::int_to_expr(self, super::IntCastOp::BitsetCast)
    }
}

impl From<IntExpression> for Expression {
    /// Convert an integer expression to a relational expression (singleton set with the atom for this integer)
    fn from(int_expr: IntExpression) -> Self {
        int_expr.to_expression()
    }
}

impl Expression {
    /// Cardinality (#expr)
    pub fn count(self) -> IntExpression {
        IntExpression::cardinality(self)
    }

    /// Sum of integer atoms in expression (cast expression to int via SUM)
    pub fn sum_cast(self) -> IntExpression {
        IntExpression::expr_cast(self)
    }

    /// Sum of expression values over declarations
    pub fn sum(self, decls: Decls) -> IntExpression {
        IntExpression::sum(decls, IntExpression::expr_cast(self))
    }
}

#[cfg(test)]
mod tests {
    use super::super::{Expression, ExpressionInner, FormulaInner, Relation, Variable, Decl};
    use super::*;

    #[test]
    fn int_constants() {
        let i = IntExpression::constant(42);
        assert!(matches!(i.inner(), IntExpressionInner::Constant(42)));
    }

    #[test]
    fn int_arithmetic() {
        let a = IntExpression::constant(10);
        let b = IntExpression::constant(5);

        let sum = a.clone().plus(b.clone());
        assert!(matches!(sum.inner(), IntExpressionInner::Binary { op: IntBinaryOp::Plus, .. }));

        let diff = a.clone().minus(b.clone());
        assert!(matches!(diff.inner(), IntExpressionInner::Binary { op: IntBinaryOp::Minus, .. }));

        let prod = a.clone().multiply(b.clone());
        assert!(matches!(prod.inner(), IntExpressionInner::Binary { op: IntBinaryOp::Multiply, .. }));

        let quot = a.divide(b);
        assert!(matches!(quot.inner(), IntExpressionInner::Binary { op: IntBinaryOp::Divide, .. }));
    }

    #[test]
    fn int_unary() {
        let a = IntExpression::constant(-5);

        let neg = a.clone().negate();
        assert!(matches!(neg.inner(), IntExpressionInner::Unary { op: IntUnaryOp::Negate, .. }));

        let abs = a.abs();
        assert!(matches!(abs.inner(), IntExpressionInner::Unary { op: IntUnaryOp::Abs, .. }));
    }

    #[test]
    fn int_comparisons() {
        let a = IntExpression::constant(10);
        let b = IntExpression::constant(5);

        let eq = a.clone().eq(b.clone());
        assert!(matches!(&*eq.inner(), FormulaInner::IntComparison { op: IntCompareOp::Eq, .. }));

        let lt = a.clone().lt(b.clone());
        assert!(matches!(&*lt.inner(), FormulaInner::IntComparison { op: IntCompareOp::Lt, .. }));

        let gt = a.gt(b);
        assert!(matches!(&*gt.inner(), FormulaInner::IntComparison { op: IntCompareOp::Gt, .. }));
    }

    #[test]
    fn cardinality() {
        let r = Relation::unary("Person");
        let card = Expression::from(r).count();
        assert!(matches!(card.inner(), IntExpressionInner::Cardinality(_)));
    }

    #[test]
    fn sum_expression() {
        let person = Relation::unary("Person");
        let x = Variable::unary("x");
        let decl = Decl::one_of(x, Expression::from(&person));
        let decls = Decls::from(decl);

        let sum = Expression::from(person).sum(decls);
        assert!(matches!(sum.inner(), IntExpressionInner::Sum { .. }));
    }

    #[test]
    fn nary_sum() {
        let a = IntExpression::constant(1);
        let b = IntExpression::constant(2);
        let c = IntExpression::constant(3);

        let sum = IntExpression::sum_all(vec![a, b, c]);
        assert!(matches!(sum.inner(), IntExpressionInner::Nary { .. }));
    }

    #[test]
    fn int_to_expression_cast() {
        use super::super::IntCastOp;

        let int_expr = IntExpression::constant(5);
        let expr = int_expr.to_expression();

        // Should create IntToExprCast with IntCast operator
        assert!(matches!(&*expr.inner(), ExpressionInner::IntToExprCast { op: IntCastOp::IntCast, .. }));

        // Test From trait
        let int_expr2 = IntExpression::constant(10);
        let expr2: Expression = int_expr2.into();
        assert!(matches!(&*expr2.inner(), ExpressionInner::IntToExprCast { op: IntCastOp::IntCast, .. }));
    }

    #[test]
    fn int_to_bitset_cast() {
        use super::super::IntCastOp;

        let int_expr = IntExpression::constant(7);
        let expr = int_expr.to_bitset();

        // Should create IntToExprCast with BitsetCast operator
        assert!(matches!(&*expr.inner(), ExpressionInner::IntToExprCast { op: IntCastOp::BitsetCast, .. }));
    }

    #[test]
    fn int_cast_arity() {
        // IntToExprCast expressions should have arity 1
        let int_expr = IntExpression::constant(42);
        let expr = int_expr.to_expression();
        assert_eq!(expr.arity(), 1);

        let bitset_expr = IntExpression::constant(15).to_bitset();
        assert_eq!(bitset_expr.arity(), 1);
    }
}
