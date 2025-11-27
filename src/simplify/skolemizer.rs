//! Skolemization - eliminates existential quantifiers by introducing Skolem functions
//!
//! Based on Java: kodkod.engine.fol2sat.Skolemizer

use crate::ast::{
    Formula, Expression, Quantifier, Decls, Decl, Variable, Relation, Multiplicity,
    BinaryFormulaOp,
};
use crate::instance::Bounds;
use crate::bool::Options as BoolOptions;
use std::collections::HashMap;

/// Skolemizes existential quantifiers by replacing them with Skolem functions.
///
/// This transformation eliminates existential quantifiers by introducing new
/// relations (Skolem constants/functions) that depend on any universally
/// quantified variables in scope.
pub struct Skolemizer<'a> {
    /// Bounds to which Skolem relations will be added
    bounds: &'a mut Bounds,
    /// Options controlling skolemization depth
    options: &'a BoolOptions,
    /// Maps original formulas to their skolemized versions
    cache: HashMap<Formula, Formula>,
    /// Environment mapping variables to their replacements
    replacement_env: HashMap<Variable, Expression>,
    /// Non-skolemizable declarations in current scope
    non_skolems: Vec<Decl>,
    /// Skolem constraints to add at top level
    top_constraints: Vec<Formula>,
    /// Current negation state (affects when to skolemize)
    negated: bool,
    /// Depth to which to skolemize (-1 means disabled)
    skolem_depth: i32,
    /// Counter for generating unique Skolem names
    skolem_counter: usize,
}

impl<'a> Skolemizer<'a> {
    /// Creates a new Skolemizer with the given bounds and options
    pub fn new(bounds: &'a mut Bounds, options: &'a BoolOptions) -> Self {
        Self {
            bounds,
            options,
            cache: HashMap::new(),
            replacement_env: HashMap::new(),
            non_skolems: Vec::new(),
            top_constraints: Vec::new(),
            negated: false,
            skolem_depth: options.skolem_depth.unwrap_or(0) as i32,
            skolem_counter: 0,
        }
    }

    /// Skolemizes the given formula
    pub fn skolemize(&mut self, formula: &Formula) -> Formula {
        self.visit_formula(formula)
    }

    fn visit_formula(&mut self, formula: &Formula) -> Formula {
        // Check cache
        if let Some(cached) = self.cache.get(formula) {
            return cached.clone();
        }

        let result = match formula {
            Formula::Constant(_) => formula.clone(),

            Formula::Not(inner) => {
                // Flip negation state
                self.negated = !self.negated;
                let result = Formula::Not(Box::new(self.visit_formula(inner)));
                self.negated = !self.negated;
                result
            }

            Formula::Binary { op, left, right } => {
                match op {
                    BinaryFormulaOp::Implies => {
                        // p => q is treated as !p OR q for negation tracking
                        self.negated = !self.negated;
                        let left_result = self.visit_formula(left);
                        self.negated = !self.negated;
                        let right_result = self.visit_formula(right);
                        Formula::Binary {
                            op: *op,
                            left: Box::new(left_result),
                            right: Box::new(right_result),
                        }
                    }
                    _ => {
                        let left_result = self.visit_formula(left);
                        let right_result = self.visit_formula(right);
                        if left_result == **left && right_result == **right {
                            formula.clone()
                        } else {
                            Formula::Binary {
                                op: *op,
                                left: Box::new(left_result),
                                right: Box::new(right_result),
                            }
                        }
                    }
                }
            }

            Formula::Nary { op, formulas } => {
                let mut changed = false;
                let results: Vec<Formula> = formulas.iter().map(|f| {
                    let result = self.visit_formula(f);
                    if result != *f {
                        changed = true;
                    }
                    result
                }).collect();

                if changed {
                    Formula::Nary { op: *op, formulas: results }
                } else {
                    formula.clone()
                }
            }

            Formula::Quantified { quantifier, declarations, body } => {
                self.visit_quantified(*quantifier, declarations, body)
            }

            Formula::Comparison { op, left, right } => {
                // Replace variables in expressions
                let left_replaced = self.replace_in_expression(left);
                let right_replaced = self.replace_in_expression(right);
                if left_replaced == *left && right_replaced == *right {
                    formula.clone()
                } else {
                    Formula::Comparison {
                        op: *op,
                        left: left_replaced,
                        right: right_replaced,
                    }
                }
            }

            Formula::IntComparison { op, left, right } => {
                // Replace variables in integer expressions
                let left_replaced = self.replace_in_int_expression(left);
                let right_replaced = self.replace_in_int_expression(right);
                if left_replaced == **left && right_replaced == **right {
                    formula.clone()
                } else {
                    Formula::IntComparison {
                        op: *op,
                        left: Box::new(left_replaced),
                        right: Box::new(right_replaced),
                    }
                }
            }

            Formula::Multiplicity { mult, expr } => {
                // Replace variables in expression
                let expr_replaced = self.replace_in_expression(expr);
                if expr_replaced == *expr {
                    formula.clone()
                } else {
                    Formula::Multiplicity {
                        mult: *mult,
                        expr: expr_replaced,
                    }
                }
            }

            // For other formula types, just return as-is
            _ => formula.clone(),
        };

        self.cache.insert(formula.clone(), result.clone());
        result
    }

    fn visit_quantified(&mut self, quantifier: Quantifier, declarations: &Decls, body: &Formula) -> Formula {
        // Check if this formula is skolemizable
        let skolemizable = self.skolem_depth >= 0 &&
            ((self.negated && quantifier == Quantifier::All) ||
             (!self.negated && quantifier == Quantifier::Some));

        if skolemizable {
            // This is an existential quantifier (or universal under negation) - skolemize it
            self.skolemize_quantifier(quantifier, declarations, body)
        } else {
            // This is a universal quantifier (or existential under negation) - can't skolemize
            // but may be able to skolemize nested quantifiers

            let old_non_skolems_len = self.non_skolems.len();

            // Add these declarations to non-skolems (they become parameters for nested skolems)
            for decl in declarations.iter() {
                self.non_skolems.push(decl.clone());
            }

            // Visit the body
            let can_skolemize_below = self.skolem_depth >= self.non_skolems.len() as i32;

            let body_result = if can_skolemize_below {
                self.visit_formula(body)
            } else {
                // Can't skolemize below - disable skolemization temporarily
                let old_depth = self.skolem_depth;
                self.skolem_depth = -1;
                let result = self.visit_formula(body);
                self.skolem_depth = old_depth;
                result
            };

            // Remove the declarations we added
            self.non_skolems.truncate(old_non_skolems_len);

            Formula::Quantified {
                quantifier,
                declarations: declarations.clone(),
                body: Box::new(body_result),
            }
        }
    }

    fn skolemize_quantifier(&mut self, _quantifier: Quantifier, declarations: &Decls, body: &Formula) -> Formula {
        let mut range_constraints = Vec::new();
        let mut domain_constraints = Vec::new();

        // Save old replacement environment
        let old_env = self.replacement_env.clone();

        // For each declaration, create a Skolem constant/function
        for decl in declarations.iter() {
            let var = decl.variable();

            // Create Skolem relation
            // Arity = variable arity + number of non-skolem parameters
            let skolem_arity = var.arity() + self.non_skolems.len();
            let skolem_name = format!("$skolem_{}", self.skolem_counter);
            self.skolem_counter += 1;

            let skolem = Relation::nary(&skolem_name, skolem_arity);

            // Create Skolem expression
            let mut skolem_expr = Expression::from(skolem.clone());

            // If there are parameters (non-skolem variables), join with them
            for param_decl in &self.non_skolems {
                let param_var = param_decl.variable();
                skolem_expr = skolem_expr.join(Expression::from(param_var.clone()));
            }

            // Add constraint that Skolem is in the declared expression
            range_constraints.push(skolem_expr.clone().in_set(decl.expression().clone()));

            // Add multiplicity constraint if needed
            match decl.multiplicity() {
                Multiplicity::One => {
                    range_constraints.push(skolem_expr.clone().one());
                }
                Multiplicity::Lone => {
                    range_constraints.push(skolem_expr.clone().lone());
                }
                Multiplicity::Some => {
                    range_constraints.push(skolem_expr.clone().some());
                }
                Multiplicity::No => {
                    // A declaration with No multiplicity means the variable can't take any value.
                    // This makes existential quantifiers always false and universal always true.
                    // This shouldn't normally appear in well-formed formulas, but we handle it.
                    range_constraints.push(skolem_expr.clone().no());
                }
                Multiplicity::Set => {
                    // Set multiplicity means no constraint - any subset is allowed
                }
            }

            // If there are parameters, add domain constraint
            if !self.non_skolems.is_empty() {
                domain_constraints.push(self.domain_constraint(&skolem, decl));
            }

            // Add Skolem to replacement environment
            self.replacement_env.insert(var.clone(), skolem_expr);

            // Add bounds for the Skolem relation
            self.add_skolem_bounds(&skolem, decl);
        }

        // Visit the body with the new replacements
        let body_result = self.visit_formula(body);

        // Restore old environment
        self.replacement_env = old_env;

        // Build the result formula
        let mut result = body_result;

        // Add range constraints
        if !range_constraints.is_empty() {
            let range_formula = Formula::and_all(range_constraints);
            result = if self.negated {
                Formula::implies(range_formula, result)
            } else {
                Formula::and(range_formula, result)
            };
        }

        // Store domain constraints to add at top level
        if !domain_constraints.is_empty() {
            self.top_constraints.extend(domain_constraints);
        }

        // If we're at the top level and have constraints, add them
        if self.replacement_env.is_empty() && !self.top_constraints.is_empty() {
            let constraints = Formula::and_all(self.top_constraints.drain(..).collect());
            result = if self.negated {
                Formula::implies(constraints, result)
            } else {
                Formula::and(constraints, result)
            };
        }

        result
    }

    fn domain_constraint(&self, skolem: &Relation, decl: &Decl) -> Formula {
        // For each parameter combination, the Skolem function must be defined
        // This creates: ∀p1...pn. skolem[p1,...,pn] in decl.expression

        // Create the Skolem expression joined with parameters
        let mut skolem_expr = Expression::from(skolem.clone());
        let mut param_decls = Vec::new();

        for param_decl in &self.non_skolems {
            let param_var = param_decl.variable();
            skolem_expr = skolem_expr.join(Expression::from(param_var.clone()));
            param_decls.push(param_decl.clone());
        }

        // Create the constraint
        let constraint = skolem_expr.in_set(decl.expression().clone());

        // Quantify over parameters
        if param_decls.is_empty() {
            constraint
        } else {
            Formula::Quantified {
                quantifier: Quantifier::All,
                declarations: Decls::from_vec(param_decls),
                body: Box::new(constraint),
            }
        }
    }

    fn add_skolem_bounds(&mut self, skolem: &Relation, decl: &Decl) {
        // Add upper bound for Skolem relation
        // For now, use a conservative upper bound - the cross product of universes
        let factory = self.bounds.universe().factory();
        let arity = skolem.arity();

        // Upper bound is universe^arity
        let upper = factory.all(arity);

        // Add the bound
        self.bounds.bound(skolem, factory.none(arity), upper).unwrap();
    }

    fn replace_in_expression(&self, expr: &Expression) -> Expression {
        match expr {
            Expression::Variable(var) => {
                // Check if this variable has a replacement
                if let Some(replacement) = self.replacement_env.get(var) {
                    replacement.clone()
                } else {
                    expr.clone()
                }
            }
            Expression::Binary { op, left, right, arity } => {
                let left_replaced = self.replace_in_expression(left);
                let right_replaced = self.replace_in_expression(right);
                if left_replaced == **left && right_replaced == **right {
                    expr.clone()
                } else {
                    Expression::Binary {
                        op: *op,
                        left: Box::new(left_replaced),
                        right: Box::new(right_replaced),
                        arity: *arity,
                    }
                }
            }
            Expression::Unary { op, expr: sub } => {
                let sub_replaced = self.replace_in_expression(sub);
                if sub_replaced == **sub {
                    expr.clone()
                } else {
                    Expression::Unary {
                        op: *op,
                        expr: Box::new(sub_replaced),
                    }
                }
            }
            Expression::Nary { exprs, arity } => {
                let mut changed = false;
                let results: Vec<Expression> = exprs.iter().map(|e| {
                    let result = self.replace_in_expression(e);
                    if result != *e {
                        changed = true;
                    }
                    result
                }).collect();

                if changed {
                    Expression::Nary { exprs: results, arity: *arity }
                } else {
                    expr.clone()
                }
            }
            Expression::If { condition, then_expr, else_expr, arity } => {
                let then_replaced = self.replace_in_expression(then_expr);
                let else_replaced = self.replace_in_expression(else_expr);
                // Note: condition is a Formula, would need separate handling
                if then_replaced == **then_expr && else_replaced == **else_expr {
                    expr.clone()
                } else {
                    Expression::If {
                        condition: condition.clone(),
                        then_expr: Box::new(then_replaced),
                        else_expr: Box::new(else_replaced),
                        arity: *arity,
                    }
                }
            }
            Expression::Comprehension { .. } => {
                // Comprehensions have their own scope, don't replace variables in them
                // This may need more careful handling
                expr.clone()
            }
            // For other expression types, just return as-is
            _ => expr.clone(),
        }
    }

    fn replace_in_int_expression(&self, expr: &crate::ast::IntExpression) -> crate::ast::IntExpression {
        use crate::ast::IntExpression;

        match expr {
            IntExpression::Cardinality(inner_expr) => {
                // Replace variables in the expression
                let replaced = self.replace_in_expression(inner_expr);
                if replaced == *inner_expr {
                    expr.clone()
                } else {
                    IntExpression::Cardinality(replaced)
                }
            }
            IntExpression::Binary { left, op, right } => {
                let left_replaced = self.replace_in_int_expression(left);
                let right_replaced = self.replace_in_int_expression(right);
                if left_replaced == **left && right_replaced == **right {
                    expr.clone()
                } else {
                    IntExpression::Binary {
                        left: Box::new(left_replaced),
                        op: *op,
                        right: Box::new(right_replaced),
                    }
                }
            }
            IntExpression::Unary { op, expr: inner } => {
                let inner_replaced = self.replace_in_int_expression(inner);
                if inner_replaced == **inner {
                    expr.clone()
                } else {
                    IntExpression::Unary {
                        op: *op,
                        expr: Box::new(inner_replaced),
                    }
                }
            }
            IntExpression::Nary { exprs } => {
                let mut changed = false;
                let results: Vec<IntExpression> = exprs.iter().map(|e| {
                    let result = self.replace_in_int_expression(e);
                    if result != *e {
                        changed = true;
                    }
                    result
                }).collect();

                if changed {
                    IntExpression::Nary { exprs: results }
                } else {
                    expr.clone()
                }
            }
            IntExpression::Sum { decls, expr: inner } => {
                // Sum has its own scope, but we might need to handle this more carefully
                // For now, don't replace in the body as it has its own bindings
                expr.clone()
            }
            IntExpression::If { condition, then_expr, else_expr } => {
                // Note: condition is a Formula, would need separate handling
                let then_replaced = self.replace_in_int_expression(then_expr);
                let else_replaced = self.replace_in_int_expression(else_expr);
                if then_replaced == **then_expr && else_replaced == **else_expr {
                    expr.clone()
                } else {
                    IntExpression::If {
                        condition: condition.clone(),
                        then_expr: Box::new(then_replaced),
                        else_expr: Box::new(else_replaced),
                    }
                }
            }
            IntExpression::ExprCast(inner_expr) => {
                let replaced = self.replace_in_expression(inner_expr);
                if replaced == *inner_expr {
                    expr.clone()
                } else {
                    IntExpression::ExprCast(replaced)
                }
            }
            // Constants don't need replacement
            IntExpression::Constant(_) => expr.clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::instance::Universe;

    #[test]
    fn test_simple_skolemization() {
        let universe = Universe::new(&["A", "B", "C"]).unwrap();
        let mut bounds = Bounds::new(universe);
        let options = BoolOptions::default();

        // ∃x. P(x) should become P($skolem_0)
        let x = Variable::unary("x");
        let p = Relation::unary("P");
        let factory = bounds.universe().factory();
        bounds.bound(&p, factory.none(1), factory.all(1)).unwrap();

        let formula = Formula::Quantified {
            quantifier: Quantifier::Some,
            declarations: Decls::from(Decl::one_of(x.clone(), Expression::UNIV)),
            body: Box::new(Expression::from(x).in_set(Expression::from(p))),
        };

        let mut skolemizer = Skolemizer::new(&mut bounds, &options);
        let result = skolemizer.skolemize(&formula);

        // Result should not have the quantifier
        assert!(!matches!(result, Formula::Quantified { .. }));
    }
}