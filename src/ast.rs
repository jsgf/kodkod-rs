//! AST types for relational logic formulas
//!
//! This module contains the types that make up Kodkod's abstract syntax tree.

pub mod formula;
pub mod int_expr;
pub mod visitor;

pub use formula::{
    BinaryFormulaOp, CompareOp, Decl, Decls, Formula, Multiplicity, Quantifier,
    RelationPredicate, RelationPredicateName,
};
pub use int_expr::{IntBinaryOp, IntCompareOp, IntExpression, IntUnaryOp};
pub use visitor::{ExpressionVisitor, FormulaVisitor};

use std::fmt;
use std::sync::Arc;

/// A relation - a named variable in relational logic
///
/// Relations are leaf expressions with a fixed arity. Two relations are equal
/// if and only if they are the same object (identity equality).
#[derive(Clone)]
pub struct Relation {
    inner: Arc<RelationInner>,
}

struct RelationInner {
    name: String,
    arity: usize,
}

impl Relation {
    /// Creates a new relation with the given name and arity
    ///
    /// # Panics
    /// Panics if arity < 1
    pub fn nary(name: impl Into<String>, arity: usize) -> Self {
        assert!(arity >= 1, "arity must be at least 1, got {}", arity);
        Self {
            inner: Arc::new(RelationInner {
                name: name.into(),
                arity,
            }),
        }
    }

    /// Creates a new unary relation (arity = 1)
    pub fn unary(name: impl Into<String>) -> Self {
        Self::nary(name, 1)
    }

    /// Creates a new binary relation (arity = 2)
    pub fn binary(name: impl Into<String>) -> Self {
        Self::nary(name, 2)
    }

    /// Creates a new ternary relation (arity = 3)
    pub fn ternary(name: impl Into<String>) -> Self {
        Self::nary(name, 3)
    }

    /// Returns the name of this relation
    pub fn name(&self) -> &str {
        &self.inner.name
    }

    /// Returns the arity of this relation
    pub fn arity(&self) -> usize {
        self.inner.arity
    }
}

// Identity equality - two relations are equal iff they're the same Arc
impl PartialEq for Relation {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.inner, &other.inner)
    }
}

impl Eq for Relation {}

impl std::hash::Hash for Relation {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        Arc::as_ptr(&self.inner).hash(state);
    }
}

impl fmt::Debug for Relation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Relation({}/{})", self.name(), self.arity())
    }
}

impl fmt::Display for Relation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

/// A variable in a quantified formula or comprehension
///
/// Variables have identity equality like relations.
#[derive(Clone)]
pub struct Variable {
    inner: Arc<VariableInner>,
}

struct VariableInner {
    name: String,
    arity: usize,
}

impl Variable {
    /// Creates a new unary variable
    pub fn unary(name: impl Into<String>) -> Self {
        Self::nary(name, 1)
    }

    /// Creates a new variable with the given arity
    pub fn nary(name: impl Into<String>, arity: usize) -> Self {
        assert!(arity >= 1, "arity must be at least 1");
        Self {
            inner: Arc::new(VariableInner {
                name: name.into(),
                arity,
            }),
        }
    }

    /// Returns the name of this variable
    pub fn name(&self) -> &str {
        &self.inner.name
    }

    /// Returns the arity of this variable
    pub fn arity(&self) -> usize {
        self.inner.arity
    }

    /// Bind this variable to an expression in a quantifier
    /// Returns a formula representing "variable in expression"
    pub fn one_of(self, expression: Expression) -> crate::ast::formula::Formula {
        Expression::from(self).in_set(expression)
    }
}

impl PartialEq for Variable {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.inner, &other.inner)
    }
}

impl Eq for Variable {}

impl std::hash::Hash for Variable {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        Arc::as_ptr(&self.inner).hash(state);
    }
}

impl fmt::Debug for Variable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Variable({}/{})", self.name(), self.arity())
    }
}

/// Operators for binary expressions
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    /// Relational composition/join
    Join,
    /// Cartesian product
    Product,
    /// Set union
    Union,
    /// Set difference
    Difference,
    /// Set intersection
    Intersection,
    /// Relational override
    Override,
}

/// Operators for unary expressions
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    /// Transpose of a binary relation
    Transpose,
    /// Transitive closure
    Closure,
    /// Reflexive transitive closure
    ReflexiveClosure,
}

/// A relational expression
#[expect(missing_docs)]
#[derive(Clone, Debug, PartialEq)]
pub enum Expression {
    /// A relation (leaf)
    Relation(Relation),
    /// A variable (leaf)
    Variable(Variable),
    /// A constant expression
    Constant(ConstantExpr),
    /// Binary expression (e.g., join, product, union)
    Binary {
        left: Box<Expression>,
        op: BinaryOp,
        right: Box<Expression>,
        arity: usize,
    },
    /// Unary expression (e.g., transpose, closure)
    Unary {
        op: UnaryOp,
        expr: Box<Expression>,
    },
    /// N-ary union
    Nary {
        exprs: Vec<Expression>,
        arity: usize,
    },
}

/// Constant expressions
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstantExpr {
    /// Universal relation (all atoms)
    Univ,
    /// Identity relation (diagonal)
    Iden,
    /// Empty relation
    None,
    /// Integer atoms
    Ints,
}

impl Expression {
    /// Universal relation constant
    pub const UNIV: Expression = Expression::Constant(ConstantExpr::Univ);
    /// Identity relation constant
    pub const IDEN: Expression = Expression::Constant(ConstantExpr::Iden);
    /// Empty relation constant
    pub const NONE: Expression = Expression::Constant(ConstantExpr::None);
    /// Integer relation constant
    pub const INTS: Expression = Expression::Constant(ConstantExpr::Ints);

    /// Returns the arity of this expression
    pub fn arity(&self) -> usize {
        match self {
            Expression::Relation(r) => r.arity(),
            Expression::Variable(v) => v.arity(),
            Expression::Constant(c) => match c {
                ConstantExpr::Univ => 1,
                ConstantExpr::Iden => 2,
                ConstantExpr::None => 1,
                ConstantExpr::Ints => 1,
            },
            Expression::Binary { arity, .. } => *arity,
            Expression::Unary { .. } => 2,
            Expression::Nary { arity, .. } => *arity,
        }
    }

    /// Relational join
    pub fn join(self, other: Expression) -> Expression {
        self.binary(BinaryOp::Join, other)
    }

    /// Cartesian product
    pub fn product(self, other: Expression) -> Expression {
        self.binary(BinaryOp::Product, other)
    }

    /// Set union
    pub fn union(self, other: Expression) -> Expression {
        self.binary(BinaryOp::Union, other)
    }

    /// Set difference
    pub fn difference(self, other: Expression) -> Expression {
        self.binary(BinaryOp::Difference, other)
    }

    /// Set intersection
    pub fn intersection(self, other: Expression) -> Expression {
        self.binary(BinaryOp::Intersection, other)
    }

    /// Relational override
    pub fn override_with(self, other: Expression) -> Expression {
        self.binary(BinaryOp::Override, other)
    }

    /// Transpose
    pub fn transpose(self) -> Expression {
        assert_eq!(self.arity(), 2, "transpose requires arity 2");
        Expression::Unary {
            op: UnaryOp::Transpose,
            expr: Box::new(self),
        }
    }

    /// Transitive closure
    pub fn closure(self) -> Expression {
        assert_eq!(self.arity(), 2, "closure requires arity 2");
        Expression::Unary {
            op: UnaryOp::Closure,
            expr: Box::new(self),
        }
    }

    /// Reflexive transitive closure
    pub fn reflexive_closure(self) -> Expression {
        assert_eq!(self.arity(), 2, "reflexive_closure requires arity 2");
        Expression::Unary {
            op: UnaryOp::ReflexiveClosure,
            expr: Box::new(self),
        }
    }

    fn binary(self, op: BinaryOp, other: Expression) -> Expression {
        let arity = match op {
            BinaryOp::Union | BinaryOp::Difference | BinaryOp::Intersection | BinaryOp::Override => {
                assert_eq!(
                    self.arity(),
                    other.arity(),
                    "Incompatible arities for {:?}: {} and {}",
                    op,
                    self.arity(),
                    other.arity()
                );
                self.arity()
            }
            BinaryOp::Join => {
                let result_arity = self.arity() + other.arity() - 2;
                assert!(
                    result_arity >= 1,
                    "Join would result in arity < 1: {} + {} - 2",
                    self.arity(),
                    other.arity()
                );
                result_arity
            }
            BinaryOp::Product => self.arity() + other.arity(),
        };

        Expression::Binary {
            left: Box::new(self),
            op,
            right: Box::new(other),
            arity,
        }
    }

    /// Create an n-ary union from multiple expressions
    pub fn union_all(exprs: Vec<Expression>) -> Expression {
        assert!(!exprs.is_empty(), "Cannot create empty union");
        if exprs.len() == 1 {
            return exprs.into_iter().next().unwrap();
        }

        let arity = exprs[0].arity();
        for expr in &exprs[1..] {
            assert_eq!(
                expr.arity(),
                arity,
                "All expressions in union must have same arity"
            );
        }

        Expression::Nary { exprs, arity }
    }

    /// Check membership in a relation (convenience method)
    /// This is equivalent to `self.in_set(Expression::from(relation))`
    pub fn in_relation(self, relation: &Relation) -> crate::ast::formula::Formula {
        self.in_set(Expression::from(relation.clone()))
    }
}

impl From<Relation> for Expression {
    fn from(r: Relation) -> Self {
        Expression::Relation(r)
    }
}

impl From<&Relation> for Expression {
    fn from(r: &Relation) -> Self {
        Expression::Relation(r.clone())
    }
}

impl From<Variable> for Expression {
    fn from(v: Variable) -> Self {
        Expression::Variable(v)
    }
}

impl From<&Variable> for Expression {
    fn from(v: &Variable) -> Self {
        Expression::Variable(v.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn create_relations() {
        let r1 = Relation::unary("Person");
        assert_eq!(r1.name(), "Person");
        assert_eq!(r1.arity(), 1);

        let r2 = Relation::binary("knows");
        assert_eq!(r2.name(), "knows");
        assert_eq!(r2.arity(), 2);

        let r3 = Relation::ternary("teaches");
        assert_eq!(r3.name(), "teaches");
        assert_eq!(r3.arity(), 3);

        let r4 = Relation::nary("custom", 5);
        assert_eq!(r4.arity(), 5);
    }

    #[test]
    fn relation_identity() {
        let r1 = Relation::unary("Person");
        let r2 = Relation::unary("Person");
        let r3 = r1.clone();

        // Same relation (cloned) should be equal
        assert_eq!(r1, r3);

        // Different relations with same name should NOT be equal
        assert_ne!(r1, r2);
    }

    #[test]
    #[should_panic(expected = "arity must be at least 1")]
    fn zero_arity_panics() {
        Relation::nary("invalid", 0);
    }

    #[test]
    fn create_variables() {
        let v1 = Variable::unary("x");
        assert_eq!(v1.name(), "x");
        assert_eq!(v1.arity(), 1);

        let v2 = Variable::nary("y", 2);
        assert_eq!(v2.arity(), 2);
    }

    #[test]
    fn variable_identity() {
        let v1 = Variable::unary("x");
        let v2 = Variable::unary("x");
        let v3 = v1.clone();

        assert_eq!(v1, v3);
        assert_ne!(v1, v2);
    }

    #[test]
    fn expression_constants() {
        assert_eq!(Expression::UNIV.arity(), 1);
        assert_eq!(Expression::IDEN.arity(), 2);
        assert_eq!(Expression::NONE.arity(), 1);
        assert_eq!(Expression::INTS.arity(), 1);
    }

    #[test]
    fn build_expression_tree() {
        let r1 = Relation::binary("knows");
        let r2 = Relation::unary("Person");

        // r1.join(r2) - arity is 2 + 1 - 2 = 1
        let expr = Expression::from(r1.clone()).join(Expression::from(r2.clone()));
        assert_eq!(expr.arity(), 1);

        // r2.product(r2) - arity is 1 + 1 = 2
        let product = Expression::from(r2.clone()).product(Expression::from(r2.clone()));
        assert_eq!(product.arity(), 2);

        // transpose
        let transpose = Expression::from(r1.clone()).transpose();
        assert_eq!(transpose.arity(), 2);
    }

    #[test]
    fn set_operations() {
        let r1 = Relation::unary("A");
        let r2 = Relation::unary("B");

        let union = Expression::from(r1.clone()).union(Expression::from(r2.clone()));
        assert_eq!(union.arity(), 1);

        let diff = Expression::from(r1.clone()).difference(Expression::from(r2.clone()));
        assert_eq!(diff.arity(), 1);

        let inter = Expression::from(r1).intersection(Expression::from(r2));
        assert_eq!(inter.arity(), 1);
    }

    #[test]
    #[should_panic(expected = "Incompatible arities")]
    fn incompatible_union() {
        let r1 = Relation::unary("A");
        let r2 = Relation::binary("B");

        let _ = Expression::from(r1).union(Expression::from(r2));
    }

    #[test]
    fn closure_operations() {
        let r = Relation::binary("parent");

        let closure = Expression::from(r.clone()).closure();
        assert_eq!(closure.arity(), 2);

        let ref_closure = Expression::from(r).reflexive_closure();
        assert_eq!(ref_closure.arity(), 2);
    }

    #[test]
    fn nary_union() {
        let r1 = Relation::unary("A");
        let r2 = Relation::unary("B");
        let r3 = Relation::unary("C");

        let union = Expression::union_all(vec![
            Expression::from(r1),
            Expression::from(r2),
            Expression::from(r3),
        ]);

        assert_eq!(union.arity(), 1);
    }
}

