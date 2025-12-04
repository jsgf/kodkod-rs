//! Visitor traits for traversing AST nodes
//!
//! Since Rust uses enums for the AST, we don't need the full visitor pattern
//! from the Java version. Instead, we provide pattern matching on enum variants
//! and optional visitor traits for convenience.

use super::formula::{Decls, Formula, FormulaInner};
use super::int_expr::IntExpression;
use super::{Expression, ExpressionInner, Relation, Variable};

/// A visitor that can traverse expressions and return values
///
/// This trait provides default implementations that recursively visit
/// child nodes. Override methods to customize behavior.
pub trait ExpressionVisitor {
    /// The type returned from visiting an expression
    type Output;

    /// Visit an expression
    fn visit_expression(&mut self, expr: &Expression) -> Self::Output {
        match &*expr.inner() {
            ExpressionInner::Relation(r) => self.visit_relation(r),
            ExpressionInner::Variable(v) => self.visit_variable(v),
            ExpressionInner::Constant(_) => self.visit_constant(expr),
            ExpressionInner::Binary { left, right, .. } => {
                self.visit_expression(left);
                self.visit_expression(right);
                self.visit_binary(expr)
            }
            ExpressionInner::Unary { expr: inner, .. } => {
                self.visit_expression(inner);
                self.visit_unary(expr)
            }
            ExpressionInner::Nary { exprs, .. } => {
                for e in exprs {
                    self.visit_expression(e);
                }
                self.visit_nary(expr)
            }
            ExpressionInner::Comprehension { declarations, formula } => {
                self.visit_comprehension(expr, declarations, formula)
            }
            ExpressionInner::IntToExprCast { int_expr, .. } => {
                self.visit_int_to_expr_cast(expr, int_expr)
            }
            ExpressionInner::If { condition, then_expr, else_expr, .. } => {
                self.visit_if(expr, condition, then_expr, else_expr)
            }
        }
    }

    /// Visit a relation
    fn visit_relation(&mut self, relation: &Relation) -> Self::Output;

    /// Visit a variable
    fn visit_variable(&mut self, variable: &Variable) -> Self::Output;

    /// Visit a constant expression
    fn visit_constant(&mut self, expr: &Expression) -> Self::Output;

    /// Visit a binary expression (after visiting children)
    fn visit_binary(&mut self, expr: &Expression) -> Self::Output;

    /// Visit a unary expression (after visiting children)
    fn visit_unary(&mut self, expr: &Expression) -> Self::Output;

    /// Visit an n-ary expression (after visiting children)
    fn visit_nary(&mut self, expr: &Expression) -> Self::Output;

    /// Visit a comprehension expression
    fn visit_comprehension(&mut self, expr: &Expression, declarations: &Decls, formula: &Formula) -> Self::Output;

    /// Visit an integer-to-expression cast
    fn visit_int_to_expr_cast(&mut self, expr: &Expression, int_expr: &IntExpression) -> Self::Output;

    /// Visit an if-then-else expression
    fn visit_if(
        &mut self,
        expr: &Expression,
        condition: &Formula,
        then_expr: &Expression,
        else_expr: &Expression,
    ) -> Self::Output;
}

/// A visitor that can traverse formulas and return values
pub trait FormulaVisitor {
    /// The type returned from visiting a formula
    type Output;

    /// Visit a formula
    fn visit_formula(&mut self, formula: &Formula) -> Self::Output {
        match &*formula.inner() {
            FormulaInner::Constant(_) => self.visit_constant(formula),
            FormulaInner::Binary { left, right, .. } => {
                self.visit_formula(left);
                self.visit_formula(right);
                self.visit_binary(formula)
            }
            FormulaInner::Nary { formulas, .. } => {
                for f in formulas {
                    self.visit_formula(f);
                }
                self.visit_nary(formula)
            }
            FormulaInner::Not(inner) => {
                self.visit_formula(inner);
                self.visit_not(formula)
            }
            FormulaInner::Comparison { .. } => self.visit_comparison(formula),
            FormulaInner::Multiplicity { .. } => self.visit_multiplicity(formula),
            FormulaInner::Quantified { declarations, body, .. } => {
                self.visit_decls(declarations);
                self.visit_formula(body);
                self.visit_quantified(formula)
            }
            FormulaInner::IntComparison { left, right, .. } => {
                self.visit_int_expression(left);
                self.visit_int_expression(right);
                self.visit_int_comparison(formula)
            }
            FormulaInner::RelationPredicate(pred) => {
                // Convert to constraints and visit that
                let constraints = pred.to_constraints();
                self.visit_formula(&constraints)
            }
        }
    }

    /// Visit a constant formula
    fn visit_constant(&mut self, formula: &Formula) -> Self::Output;

    /// Visit a binary formula (after visiting children)
    fn visit_binary(&mut self, formula: &Formula) -> Self::Output;

    /// Visit an n-ary formula (after visiting children)
    fn visit_nary(&mut self, formula: &Formula) -> Self::Output;

    /// Visit a negation (after visiting child)
    fn visit_not(&mut self, formula: &Formula) -> Self::Output;

    /// Visit a comparison formula
    fn visit_comparison(&mut self, formula: &Formula) -> Self::Output;

    /// Visit a multiplicity formula
    fn visit_multiplicity(&mut self, formula: &Formula) -> Self::Output;

    /// Visit a quantified formula (after visiting children)
    fn visit_quantified(&mut self, formula: &Formula) -> Self::Output;

    /// Visit an integer comparison (after visiting children)
    fn visit_int_comparison(&mut self, formula: &Formula) -> Self::Output;

    /// Visit declarations
    fn visit_decls(&mut self, decls: &Decls);

    /// Visit an integer expression (default: do nothing)
    fn visit_int_expression(&mut self, _expr: &IntExpression) {}
}

/// A simple expression counter visitor
pub struct ExpressionCounter {
    count: usize,
}

impl ExpressionCounter {
    /// Creates a new expression counter
    pub fn new() -> Self {
        Self { count: 0 }
    }

    /// Returns the count
    pub fn count(&self) -> usize {
        self.count
    }

    /// Counts expressions in the given expression
    pub fn count_in(expr: &Expression) -> usize {
        let mut counter = Self::new();
        counter.visit_expression(expr);
        counter.count
    }
}

impl Default for ExpressionCounter {
    fn default() -> Self {
        Self::new()
    }
}

impl ExpressionVisitor for ExpressionCounter {
    type Output = ();

    fn visit_relation(&mut self, _: &Relation) {
        self.count += 1;
    }

    fn visit_variable(&mut self, _: &Variable) {
        self.count += 1;
    }

    fn visit_constant(&mut self, _: &Expression) {
        self.count += 1;
    }

    fn visit_binary(&mut self, _: &Expression) {
        self.count += 1;
    }

    fn visit_unary(&mut self, _: &Expression) {
        self.count += 1;
    }

    fn visit_nary(&mut self, _: &Expression) {
        self.count += 1;
    }

    fn visit_comprehension(&mut self, _: &Expression, _: &Decls, _: &Formula) {
        self.count += 1;
    }

    fn visit_int_to_expr_cast(&mut self, _: &Expression, _: &IntExpression) {
        self.count += 1;
    }

    fn visit_if(
        &mut self,
        _: &Expression,
        _condition: &Formula,
        then_expr: &Expression,
        else_expr: &Expression,
    ) {
        // Note: we don't visit the formula condition here because this is an ExpressionVisitor
        // The condition contributes to the expression structure but we just count expressions
        self.visit_expression(then_expr);
        self.visit_expression(else_expr);
        self.count += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::super::{Expression, Formula, Relation, Variable, Decl, Decls};
    use super::*;

    #[test]
    fn count_simple_expression() {
        let r = Relation::unary("R");
        let expr = Expression::from(r);

        let count = ExpressionCounter::count_in(&expr);
        assert_eq!(count, 1);
    }

    #[test]
    fn count_binary_expression() {
        let r1 = Relation::unary("A");
        let r2 = Relation::unary("B");

        let expr = Expression::from(r1).union(Expression::from(r2));

        let count = ExpressionCounter::count_in(&expr);
        assert_eq!(count, 3); // r1, r2, union
    }

    #[test]
    fn count_nested_expression() {
        let r1 = Relation::unary("A");
        let r2 = Relation::unary("B");
        let r3 = Relation::unary("C");

        // (A union B) union C
        let expr = Expression::from(r1)
            .union(Expression::from(r2))
            .union(Expression::from(r3));

        let count = ExpressionCounter::count_in(&expr);
        assert_eq!(count, 5); // r1, r2, union1, r3, union2
    }

    #[test]
    fn visit_formula() {
        struct FormulaCounter {
            count: usize,
        }

        impl FormulaVisitor for FormulaCounter {
            type Output = ();

            fn visit_constant(&mut self, _: &Formula) {
                self.count += 1;
            }
            fn visit_binary(&mut self, _: &Formula) {
                self.count += 1;
            }
            fn visit_nary(&mut self, _: &Formula) {
                self.count += 1;
            }
            fn visit_not(&mut self, _: &Formula) {
                self.count += 1;
            }
            fn visit_comparison(&mut self, _: &Formula) {
                self.count += 1;
            }
            fn visit_multiplicity(&mut self, _: &Formula) {
                self.count += 1;
            }
            fn visit_quantified(&mut self, _: &Formula) {
                self.count += 1;
            }
            fn visit_int_comparison(&mut self, _: &Formula) {
                self.count += 1;
            }
            fn visit_decls(&mut self, _: &Decls) {}
        }

        let r = Relation::unary("Person");
        let formula = Expression::from(r).some();

        let mut counter = FormulaCounter { count: 0 };
        counter.visit_formula(&formula);
        assert_eq!(counter.count, 1); // Just the multiplicity formula
    }

    #[test]
    fn visit_quantified_formula() {
        struct FormulaCounter {
            count: usize,
        }

        impl FormulaVisitor for FormulaCounter {
            type Output = ();

            fn visit_constant(&mut self, _: &Formula) { self.count += 1; }
            fn visit_binary(&mut self, _: &Formula) { self.count += 1; }
            fn visit_nary(&mut self, _: &Formula) { self.count += 1; }
            fn visit_not(&mut self, _: &Formula) { self.count += 1; }
            fn visit_comparison(&mut self, _: &Formula) { self.count += 1; }
            fn visit_multiplicity(&mut self, _: &Formula) { self.count += 1; }
            fn visit_quantified(&mut self, _: &Formula) { self.count += 1; }
            fn visit_int_comparison(&mut self, _: &Formula) { self.count += 1; }
            fn visit_decls(&mut self, _: &Decls) {}
        }

        let person = Relation::unary("Person");
        let p = Variable::unary("p");
        let decl = Decl::one_of(p.clone(), Expression::from(&person));
        let decls = Decls::from(decl);
        let body = Expression::from(p).in_set(Expression::from(&person));

        let formula = Formula::forall(decls, body);

        let mut counter = FormulaCounter { count: 0 };
        counter.visit_formula(&formula);
        assert_eq!(counter.count, 2); // comparison + quantified
    }
}
