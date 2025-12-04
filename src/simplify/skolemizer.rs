//! Skolemization - eliminates existential quantifiers by introducing Skolem functions
//!
//! Based on Java: kodkod.engine.fol2sat.Skolemizer

use crate::ast::{
    Formula, FormulaInner, Expression, ExpressionInner, Quantifier, Decls, Decl, Variable, Relation, Multiplicity,
    BinaryFormulaOp,
};
use crate::instance::Bounds;
use crate::solver::Options;
use std::collections::HashMap;

/// Skolemizes existential quantifiers by replacing them with Skolem functions.
///
/// This transformation eliminates existential quantifiers by introducing new
/// relations (Skolem constants/functions) that depend on any universally
/// quantified variables in scope.
pub struct Skolemizer<'a> {
    /// Bounds to which Skolem relations will be added
    bounds: &'a mut Bounds,
    /// Solver options (needed for bound computation via translator)
    solver_options: &'a Options,
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
    pub fn new(bounds: &'a mut Bounds, options: &'a Options) -> Self {
        Self {
            bounds,
            solver_options: options,
            replacement_env: HashMap::new(),
            non_skolems: Vec::new(),
            top_constraints: Vec::new(),
            negated: false,
            skolem_depth: options.bool_options.skolem_depth.unwrap_or(0) as i32,
            skolem_counter: 0,
        }
    }

    /// Skolemizes the given formula
    pub fn skolemize(&mut self, formula: &Formula) -> Formula {
        // Early exit: if there are no quantifiers, there's nothing to skolemize
        if !has_quantifiers(formula) {
            return formula.clone();
        }
        self.visit_formula(formula)
    }

    fn visit_formula(&mut self, formula: &Formula) -> Formula {
        // NOTE: Caching is disabled because the same formula may appear with different
        // replacement environments. The Java version only caches formulas with no free
        // variables, but we haven't implemented that check yet.
        // TODO: Implement proper caching that considers free variables

        let result = match &*formula.inner() {
            FormulaInner::Constant(_) => formula.clone(),

            FormulaInner::Not(inner) => {
                // Flip negation state
                self.negated = !self.negated;
                let result = self.visit_formula(inner).not();
                self.negated = !self.negated;
                result
            }

            FormulaInner::Binary { op, left, right } => {
                match op {
                    BinaryFormulaOp::Implies => {
                        // p => q is treated as !p OR q for negation tracking
                        self.negated = !self.negated;
                        let left_result = self.visit_formula(left);
                        self.negated = !self.negated;
                        let right_result = self.visit_formula(right);
                        left_result.implies(right_result)
                    }
                    BinaryFormulaOp::And => {
                        let left_result = self.visit_formula(left);
                        let right_result = self.visit_formula(right);
                        if left_result == *left && right_result == *right {
                            formula.clone()
                        } else {
                            left_result.and(right_result)
                        }
                    }
                    BinaryFormulaOp::Or => {
                        let left_result = self.visit_formula(left);
                        let right_result = self.visit_formula(right);
                        if left_result == *left && right_result == *right {
                            formula.clone()
                        } else {
                            left_result.or(right_result)
                        }
                    }
                    BinaryFormulaOp::Iff => {
                        let left_result = self.visit_formula(left);
                        let right_result = self.visit_formula(right);
                        if left_result == *left && right_result == *right {
                            formula.clone()
                        } else {
                            left_result.iff(right_result)
                        }
                    }
                }
            }

            FormulaInner::Nary { op, formulas } => {
                let mut changed = false;
                let results: Vec<Formula> = formulas.iter().map(|f| {
                    let result = self.visit_formula(f);
                    if result != *f {
                        changed = true;
                    }
                    result
                }).collect();

                if changed {
                    match op {
                        BinaryFormulaOp::And => Formula::and_all(results),
                        BinaryFormulaOp::Or => Formula::or_all(results),
                        _ => formula.clone(),
                    }
                } else {
                    formula.clone()
                }
            }

            FormulaInner::Quantified { quantifier, declarations, body } => {
                self.visit_quantified(*quantifier, declarations, body)
            }

            FormulaInner::Comparison { op, left, right } => {
                // Replace variables in expressions
                let left_replaced = self.replace_in_expression(left);
                let right_replaced = self.replace_in_expression(right);
                if left_replaced == *left && right_replaced == *right {
                    formula.clone()
                } else {
                    match op {
                        crate::ast::CompareOp::Equals => left_replaced.equals(right_replaced),
                        crate::ast::CompareOp::Subset => left_replaced.in_set(right_replaced),
                    }
                }
            }

            FormulaInner::IntComparison { op, left, right } => {
                // Replace variables in integer expressions
                let left_replaced = self.replace_in_int_expression(left);
                let right_replaced = self.replace_in_int_expression(right);
                if left_replaced == **left && right_replaced == **right {
                    formula.clone()
                } else {
                    Formula::int_comparison(left_replaced, *op, right_replaced)
                }
            }

            FormulaInner::Multiplicity { mult, expr } => {
                // Replace variables in expression
                let expr_replaced = self.replace_in_expression(expr);
                if expr_replaced == *expr {
                    formula.clone()
                } else {
                    match mult {
                        Multiplicity::Some => expr_replaced.some(),
                        Multiplicity::One => expr_replaced.one(),
                        Multiplicity::Lone => expr_replaced.lone(),
                        Multiplicity::No => expr_replaced.no(),
                        Multiplicity::Set => formula.clone(),
                    }
                }
            }

            // RelationPredicate only contains Relations, no variables to replace
            FormulaInner::RelationPredicate(_) => formula.clone(),
        };

        // Caching disabled - see note at top of function
        result
    }

    /// Visits a declaration, replacing any variables in its expression according to
    /// the current replacement environment. This is essential for nested quantifiers
    /// where inner quantifier domains may reference outer quantified variables.
    fn visit_decl(&mut self, decl: &Decl) -> Decl {
        // Save skolem depth and disable skolemization inside declarations
        let old_depth = self.skolem_depth;
        self.skolem_depth = -1;

        // Replace variables in the declaration's expression
        let replaced_expr = self.replace_in_expression(decl.expression());

        // Restore skolem depth
        self.skolem_depth = old_depth;

        // Return new declaration if expression changed, otherwise return original
        if replaced_expr == *decl.expression() {
            decl.clone()
        } else {
            Decl::new(
                decl.variable().clone(),
                decl.multiplicity(),
                replaced_expr,
            )
        }
    }

    fn visit_quantified(&mut self, quantifier: Quantifier, declarations: &Decls, body: &Formula) -> Formula {
        // Check if this formula is skolemizable
        let skolemizable = self.skolem_depth >= 0 &&
            ((self.negated && quantifier == Quantifier::All) ||
             (!self.negated && quantifier == Quantifier::Some));

        if skolemizable {
            // This is an existential quantifier (or universal under negation) - skolemize it
            self.skolemize_quantifier(declarations, body)
        } else {
            // This is a universal quantifier (or existential under negation) - can't skolemize
            // but may be able to skolemize nested quantifiers

            let old_non_skolems_len = self.non_skolems.len();
            let old_env = self.replacement_env.clone();

            // Visit each declaration to replace variables in their expressions,
            // then add the visited declarations to non-skolems and extend the
            // replacement environment with identity mappings
            let mut visited_decls = Vec::new();
            for decl in declarations.iter() {
                let visited_decl = self.visit_decl(decl);
                self.non_skolems.push(visited_decl.clone());
                // Extend environment with identity mapping so the variable doesn't get
                // replaced inside the quantifier body
                self.replacement_env.insert(
                    visited_decl.variable().clone(),
                    Expression::from(visited_decl.variable().clone())
                );
                visited_decls.push(visited_decl);
            }
            let visited_decls = Decls::from_vec(visited_decls);

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
            // Restore replacement environment
            self.replacement_env = old_env;

            match quantifier {
                Quantifier::All => Formula::forall(visited_decls, body_result),
                Quantifier::Some => Formula::exists(visited_decls, body_result),
            }
        }
    }

    fn skolemize_quantifier(&mut self, declarations: &Decls, body: &Formula) -> Formula {
        let mut range_constraints = Vec::new();
        let mut domain_constraints = Vec::new();

        // Save old replacement environment
        let old_env = self.replacement_env.clone();

        // For each declaration, create a Skolem constant/function
        for decl in declarations.iter() {
            // Visit the declaration to replace any variables in its expression
            // This is critical for nested quantifiers: if we have
            // exists u. exists v (domain: u.E), the second declaration's
            // expression must have u replaced with $skolem_0
            let skolem_decl = self.visit_decl(decl);
            let var = skolem_decl.variable();

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
            range_constraints.push(skolem_expr.clone().in_set(skolem_decl.expression().clone()));

            // Add multiplicity constraint if needed
            match skolem_decl.multiplicity() {
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
                domain_constraints.push(self.domain_constraint(&skolem, &skolem_decl));
            }

            // Add Skolem to replacement environment
            self.replacement_env.insert(var.clone(), skolem_expr);

            // Add bounds for the Skolem relation
            self.add_skolem_bounds(&skolem, &skolem_decl);
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
                range_formula.implies(result)
            } else {
                range_formula.and(result)
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
                constraints.implies(result)
            } else {
                constraints.and(result)
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
            Formula::forall(Decls::from_vec(param_decls), constraint)
        }
    }

    fn add_skolem_bounds(&mut self, skolem: &Relation, decl: &Decl) {
        use crate::translator::Translator;

        // TODO: Implement full Java approach with Environment tracking for parameter crossing
        // Java version:
        //   1. Creates Environment with all non_skolem parameter bounds
        //   2. Computes upperBound(skolemDecl.expression(), skolemEnv) using FOL2BoolTranslator.approximate
        //   3. Crosses matrixBound with bounds of all non_skolem parameters
        //   4. Creates TupleSet from matrixBound.denseIndices()
        //
        // Current implementation: Use Translator::approximate_expression to get tight bounds
        // This is better than factory.all() but doesn't yet handle parameter crossing for
        // Skolem functions with non_skolem parameters

        // Get dense indices for the expression (upper bound)
        let dense_indices = Translator::approximate_expression(
            decl.expression(),
            self.bounds,
            &self.solver_options.bool_options
        );

        // Create TupleSet from the dense indices
        let factory = self.bounds.universe().factory();
        let arity = skolem.arity();

        if dense_indices.is_empty() {
            // Empty bound - use conservative fallback
            let upper = factory.all(arity);
            self.bounds.bound(skolem, factory.none(arity), upper).unwrap();
        } else {
            let skolem_bound = factory.set_of(arity, &dense_indices);
            // Set lower to none (Skolem can be any subset) and upper to computed bound
            self.bounds.bound(skolem, factory.none(arity), skolem_bound).unwrap();
        }
    }

    fn replace_in_expression(&mut self, expr: &Expression) -> Expression {
        match &*expr.inner() {
            ExpressionInner::Variable(var) => {
                // Check if this variable has a replacement
                if let Some(replacement) = self.replacement_env.get(var) {
                    replacement.clone()
                } else {
                    expr.clone()
                }
            }
            ExpressionInner::Binary { op, left, right, arity: _ } => {
                let left_replaced = self.replace_in_expression(left);
                let right_replaced = self.replace_in_expression(right);
                if left_replaced == *left && right_replaced == *right {
                    expr.clone()
                } else {
                    // Use the binary method to construct the expression
                    match op {
                        crate::ast::BinaryOp::Join => left_replaced.join(right_replaced),
                        crate::ast::BinaryOp::Product => left_replaced.product(right_replaced),
                        crate::ast::BinaryOp::Union => left_replaced.union(right_replaced),
                        crate::ast::BinaryOp::Difference => left_replaced.difference(right_replaced),
                        crate::ast::BinaryOp::Intersection => left_replaced.intersection(right_replaced),
                        crate::ast::BinaryOp::Override => left_replaced.override_with(right_replaced),
                    }
                }
            }
            ExpressionInner::Unary { op, expr: sub } => {
                let sub_replaced = self.replace_in_expression(sub);
                if sub_replaced == *sub {
                    expr.clone()
                } else {
                    match op {
                        crate::ast::UnaryOp::Transpose => sub_replaced.transpose(),
                        crate::ast::UnaryOp::Closure => sub_replaced.closure(),
                        crate::ast::UnaryOp::ReflexiveClosure => sub_replaced.reflexive_closure(),
                    }
                }
            }
            ExpressionInner::Nary { exprs, arity: _ } => {
                let mut changed = false;
                let results: Vec<Expression> = exprs.iter().map(|e| {
                    let result = self.replace_in_expression(e);
                    if result != *e {
                        changed = true;
                    }
                    result
                }).collect();

                if changed {
                    Expression::union_all(results)
                } else {
                    expr.clone()
                }
            }
            ExpressionInner::If { condition, then_expr, else_expr, arity } => {
                let condition_replaced = self.visit_formula(condition);
                let then_replaced = self.replace_in_expression(then_expr);
                let else_replaced = self.replace_in_expression(else_expr);
                if condition_replaced == *condition && then_replaced == *then_expr && else_replaced == *else_expr {
                    expr.clone()
                } else {
                    Expression::if_then_else(condition_replaced, then_replaced, else_replaced, *arity)
                }
            }
            ExpressionInner::Comprehension { declarations, formula } => {
                // Comprehensions have their own scope - save and restore the replacement environment
                // But we still need to visit the decls and formula to replace free variables
                let old_env = self.replacement_env.clone();

                // Visit declarations (which extends environment with identity mappings for bound vars)
                let mut replaced_decls = Vec::new();
                let mut any_changed = false;
                for decl in declarations.iter() {
                    let replaced_decl = self.visit_decl(decl);
                    if replaced_decl != *decl {
                        any_changed = true;
                    }
                    // Extend environment with identity mapping for this variable
                    // (so it doesn't get replaced inside the comprehension body)
                    self.replacement_env.insert(decl.variable().clone(), Expression::from(decl.variable().clone()));
                    replaced_decls.push(replaced_decl);
                }
                let replaced_decls = Decls::from_vec(replaced_decls);

                // Visit the formula
                let replaced_formula = self.visit_formula(formula);

                // Restore environment
                self.replacement_env = old_env;

                if !any_changed && replaced_formula == *formula {
                    expr.clone()
                } else {
                    Expression::comprehension(replaced_decls, replaced_formula)
                }
            }
            ExpressionInner::IntToExprCast { int_expr, op } => {
                let replaced_int_expr = self.replace_in_int_expression(int_expr);
                if replaced_int_expr == **int_expr {
                    expr.clone()
                } else {
                    Expression::int_to_expr(replaced_int_expr, *op)
                }
            }
            // Leaf expressions - no variables to replace
            ExpressionInner::Relation(_) | ExpressionInner::Constant(_) => expr.clone(),
        }
    }

    fn replace_in_int_expression(&mut self, expr: &crate::ast::IntExpression) -> crate::ast::IntExpression {
        use crate::ast::{IntExpression, IntExpressionInner};

        match &*expr.inner() {
            IntExpressionInner::Cardinality(inner_expr) => {
                // Replace variables in the expression
                let replaced = self.replace_in_expression(inner_expr);
                if replaced == *inner_expr {
                    expr.clone()
                } else {
                    IntExpression::cardinality(replaced)
                }
            }
            IntExpressionInner::Binary { left, op, right } => {
                let left_replaced = self.replace_in_int_expression(left);
                let right_replaced = self.replace_in_int_expression(right);
                if left_replaced == *left && right_replaced == *right {
                    expr.clone()
                } else {
                    IntExpression::binary(left_replaced, *op, right_replaced)
                }
            }
            IntExpressionInner::Unary { op, expr: inner } => {
                let inner_replaced = self.replace_in_int_expression(inner);
                if inner_replaced == *inner {
                    expr.clone()
                } else {
                    IntExpression::unary(*op, inner_replaced)
                }
            }
            IntExpressionInner::Nary { exprs } => {
                let mut changed = false;
                let results: Vec<IntExpression> = exprs.iter().map(|e| {
                    let result = self.replace_in_int_expression(e);
                    if result != *e {
                        changed = true;
                    }
                    result
                }).collect();

                if changed {
                    IntExpression::sum_all(results)
                } else {
                    expr.clone()
                }
            }
            IntExpressionInner::Sum { decls, expr: sum_expr } => {
                // Sum creates its own scope - save and restore the replacement environment
                // But we still need to visit the decls and expr to replace free variables
                let old_env = self.replacement_env.clone();

                // Visit declarations (which extends environment with identity mappings for bound vars)
                let mut replaced_decls = Vec::new();
                let mut any_changed = false;
                for decl in decls.iter() {
                    let replaced_decl = self.visit_decl(decl);
                    if replaced_decl != *decl {
                        any_changed = true;
                    }
                    // Extend environment with identity mapping for this variable
                    // (so it doesn't get replaced inside the sum body)
                    self.replacement_env.insert(decl.variable().clone(), Expression::from(decl.variable().clone()));
                    replaced_decls.push(replaced_decl);
                }
                let replaced_decls = Decls::from_vec(replaced_decls);

                // Visit the expression
                let replaced_expr = self.replace_in_int_expression(sum_expr);

                // Restore environment
                self.replacement_env = old_env;

                if !any_changed && replaced_expr == *sum_expr {
                    expr.clone()
                } else {
                    IntExpression::sum(replaced_decls, replaced_expr)
                }
            }
            IntExpressionInner::If { condition, then_expr, else_expr } => {
                let condition_replaced = self.visit_formula(condition);
                let then_replaced = self.replace_in_int_expression(then_expr);
                let else_replaced = self.replace_in_int_expression(else_expr);
                if condition_replaced == *condition && then_replaced == *then_expr && else_replaced == *else_expr {
                    expr.clone()
                } else {
                    IntExpression::if_then_else(condition_replaced, then_replaced, else_replaced)
                }
            }
            IntExpressionInner::ExprCast(inner_expr) => {
                let replaced = self.replace_in_expression(inner_expr);
                if replaced == *inner_expr {
                    expr.clone()
                } else {
                    IntExpression::expr_cast(replaced)
                }
            }
            // Constants don't need replacement
            IntExpressionInner::Constant(_) => expr.clone(),
        }
    }
}

/// Checks if a formula contains any quantifiers
pub fn has_quantifiers(formula: &Formula) -> bool {
    match &*formula.inner() {
        FormulaInner::Constant(_) => false,
        FormulaInner::RelationPredicate(_) => false,
        FormulaInner::IntComparison { .. } => false,
        FormulaInner::Comparison { .. } => false,
        FormulaInner::Multiplicity { .. } => false,
        FormulaInner::Not(inner) => has_quantifiers(inner),
        FormulaInner::Binary { left, right, .. } => has_quantifiers(left) || has_quantifiers(right),
        FormulaInner::Nary { formulas, .. } => formulas.iter().any(has_quantifiers),
        FormulaInner::Quantified { .. } => true,
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
        let mut solver_options = crate::solver::Options::default();
        solver_options.bool_options.skolem_depth = Some(10);  // Enable skolemization

        // ∃x. P(x) should become P($skolem_0)
        let x = Variable::unary("x");
        let p = Relation::unary("P");
        let factory = bounds.universe().factory();
        bounds.bound(&p, factory.none(1), factory.all(1)).unwrap();

        let formula = Formula::exists(
            Decls::from(Decl::one_of(x.clone(), Expression::UNIV)),
            Expression::from(x).in_set(Expression::from(p)),
        );

        let mut skolemizer = Skolemizer::new(&mut bounds, &solver_options);
        let result = skolemizer.skolemize(&formula);

        // Result should not have the quantifier
        assert!(!matches!(&*result.inner(), FormulaInner::Quantified { .. }));
    }
}