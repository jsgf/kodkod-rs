//! FOL to Boolean translation cache
//!
//! Implements caching for AST node translations, following Java's FOL2BoolCache.
//! Handles both nodes without free variables (simple caching) and nodes with
//! free variables (caching keyed by variable bindings).
//!
//! Following Java: kodkod.engine.fol2sat.FOL2BoolCache

use crate::ast::{
    Decls, Expression, ExpressionInner, Formula, FormulaInner, IntExpression, IntExpressionInner,
    RelationPredicate, Variable,
};
use crate::bool::{BoolValue, BooleanMatrix};
use rustc_hash::{FxHashMap, FxHashSet};
use std::rc::Rc;

/// Detects shared nodes in an AST (nodes that appear multiple times).
/// Following Java: AnnotatedNode.SharingDetector
pub struct SharingDetector {
    /// Maps node pointer to visit count: None = not visited, Some(false) = visited once, Some(true) = shared
    visited: FxHashMap<NodeId, bool>,
}

/// Unique identifier for a node based on Rc pointer
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum NodeId {
    Expr(*const ExpressionInner),
    Formula(*const FormulaInner),
    IntExpr(*const IntExpressionInner),
}

impl NodeId {
    fn from_expr(expr: &Expression) -> Option<Self> {
        match expr {
            Expression::Ref(rc) => Some(NodeId::Expr(Rc::as_ptr(rc))),
            _ => None,
        }
    }

    fn from_formula(formula: &Formula) -> Option<Self> {
        match formula {
            Formula::Ref(rc) => Some(NodeId::Formula(Rc::as_ptr(rc))),
            _ => None,
        }
    }

    fn from_int_expr(expr: &IntExpression) -> Option<Self> {
        // IntExpression is a newtype around Rc<IntExpressionInner>
        Some(NodeId::IntExpr(expr.as_ptr()))
    }
}

impl SharingDetector {
    pub fn new() -> Self {
        Self {
            visited: FxHashMap::default(),
        }
    }

    /// Analyze a formula and return the set of shared node IDs
    pub fn detect_sharing(formula: &Formula) -> FxHashSet<NodeId> {
        let mut detector = Self::new();
        detector.visit_formula(formula);

        // Collect nodes that were visited more than once
        detector
            .visited
            .into_iter()
            .filter_map(|(id, is_shared)| if is_shared { Some(id) } else { None })
            .collect()
    }

    /// Record a visit to a node. Returns true if already visited (shared).
    fn visit_node(&mut self, id: NodeId) -> bool {
        match self.visited.get_mut(&id) {
            None => {
                self.visited.insert(id, false);
                false
            }
            Some(is_shared) => {
                if !*is_shared {
                    *is_shared = true;
                }
                true
            }
        }
    }

    fn visit_formula(&mut self, formula: &Formula) {
        if let Some(id) = NodeId::from_formula(formula) {
            if self.visit_node(id) {
                return; // Already visited
            }
        }

        match &*formula.inner() {
            FormulaInner::Constant(_) => {}
            FormulaInner::Binary { left, right, .. } => {
                self.visit_formula(left);
                self.visit_formula(right);
            }
            FormulaInner::Nary { formulas, .. } => {
                for f in formulas {
                    self.visit_formula(f);
                }
            }
            FormulaInner::Not(inner) => {
                self.visit_formula(inner);
            }
            FormulaInner::Quantified { declarations, body, .. } => {
                for decl in declarations.iter() {
                    self.visit_expression(decl.expression());
                }
                self.visit_formula(body);
            }
            FormulaInner::Comparison { left, right, .. } => {
                self.visit_expression(left);
                self.visit_expression(right);
            }
            FormulaInner::Multiplicity { expr, .. } => {
                self.visit_expression(expr);
            }
            FormulaInner::IntComparison { left, right, .. } => {
                self.visit_int_expr(left);
                self.visit_int_expr(right);
            }
            FormulaInner::RelationPredicate(pred) => {
                self.visit_relation_predicate(pred);
            }
        }
    }

    fn visit_relation_predicate(&mut self, pred: &RelationPredicate) {
        match pred {
            RelationPredicate::Acyclic { .. } => {
                // relation is a Relation, not an Expression - no need to visit
            }
            RelationPredicate::TotalOrdering { .. } => {
                // All fields are Relations, not Expressions
            }
            RelationPredicate::Function { domain, range, .. } => {
                self.visit_expression(domain);
                self.visit_expression(range);
            }
        }
    }

    fn visit_expression(&mut self, expr: &Expression) {
        if let Some(id) = NodeId::from_expr(expr) {
            if self.visit_node(id) {
                return; // Already visited
            }
        }

        match &*expr.inner() {
            ExpressionInner::Relation(_) | ExpressionInner::Variable(_) | ExpressionInner::Constant(_) => {}
            ExpressionInner::Binary { left, right, .. } => {
                self.visit_expression(left);
                self.visit_expression(right);
            }
            ExpressionInner::Unary { expr, .. } => {
                self.visit_expression(expr);
            }
            ExpressionInner::Nary { exprs, .. } => {
                for e in exprs {
                    self.visit_expression(e);
                }
            }
            ExpressionInner::Comprehension { declarations, formula } => {
                for decl in declarations.iter() {
                    self.visit_expression(decl.expression());
                }
                self.visit_formula(formula);
            }
            ExpressionInner::IntToExprCast { int_expr, .. } => {
                self.visit_int_expr(int_expr);
            }
            ExpressionInner::If { condition, then_expr, else_expr, .. } => {
                self.visit_formula(condition);
                self.visit_expression(then_expr);
                self.visit_expression(else_expr);
            }
        }
    }

    fn visit_int_expr(&mut self, expr: &IntExpression) {
        if let Some(id) = NodeId::from_int_expr(expr) {
            if self.visit_node(id) {
                return; // Already visited
            }
        }

        match expr.inner() {
            IntExpressionInner::Constant(_) => {}
            IntExpressionInner::Cardinality(expr) | IntExpressionInner::ExprCast(expr) => {
                self.visit_expression(expr);
            }
            IntExpressionInner::Binary { left, right, .. } => {
                self.visit_int_expr(left);
                self.visit_int_expr(right);
            }
            IntExpressionInner::Nary { exprs, .. } => {
                for e in exprs {
                    self.visit_int_expr(e);
                }
            }
            IntExpressionInner::Unary { expr, .. } => {
                self.visit_int_expr(expr);
            }
            IntExpressionInner::If { condition, then_expr, else_expr } => {
                self.visit_formula(condition);
                self.visit_int_expr(then_expr);
                self.visit_int_expr(else_expr);
            }
            IntExpressionInner::Sum { decls, expr } => {
                for decl in decls.iter() {
                    self.visit_expression(decl.expression());
                }
                self.visit_int_expr(expr);
            }
        }
    }
}

/// Collects free variables for AST nodes.
/// Following Java: FreeVariableCollector
pub struct FreeVariableCollector {
    /// Stack of variables currently in scope (bound by quantifiers/comprehensions)
    vars_in_scope: Vec<Variable>,
    /// Cache of free variables for each node
    free_vars: FxHashMap<NodeId, FxHashSet<Variable>>,
    /// Set of shared nodes (for caching decisions)
    shared_nodes: FxHashSet<NodeId>,
}

impl FreeVariableCollector {
    pub fn new(shared_nodes: FxHashSet<NodeId>) -> Self {
        Self {
            vars_in_scope: Vec::new(),
            free_vars: FxHashMap::default(),
            shared_nodes,
        }
    }

    /// Analyze a formula and return free variable info for cacheable nodes
    pub fn collect(formula: &Formula, shared_nodes: FxHashSet<NodeId>) -> FxHashMap<NodeId, FxHashSet<Variable>> {
        let mut collector = Self::new(shared_nodes);
        collector.visit_formula(formula);
        collector.free_vars
    }

    /// Check if we should cache this node
    fn should_cache(&self, id: NodeId, free_vars: &FxHashSet<Variable>) -> bool {
        // Cache if:
        // 1. Node is shared (appears multiple times), OR
        // 2. Node has free vars but none is the most recently bound variable
        if self.shared_nodes.contains(&id) {
            return true;
        }
        if !self.vars_in_scope.is_empty() && !free_vars.is_empty() {
            let top_var = self.vars_in_scope.last().unwrap();
            if !free_vars.contains(top_var) {
                return true;
            }
        }
        false
    }

    fn cache_if_needed(&mut self, id: NodeId, free_vars: FxHashSet<Variable>) -> FxHashSet<Variable> {
        if self.should_cache(id, &free_vars) {
            self.free_vars.insert(id, free_vars.clone());
        }
        free_vars
    }

    fn visit_formula(&mut self, formula: &Formula) -> FxHashSet<Variable> {
        let id = NodeId::from_formula(formula);

        // Check if already computed
        if let Some(id) = id {
            if let Some(cached) = self.free_vars.get(&id) {
                return cached.clone();
            }
        }

        let free_vars = match &*formula.inner() {
            FormulaInner::Constant(_) => FxHashSet::default(),
            FormulaInner::Binary { left, right, .. } => {
                let mut fv = self.visit_formula(left);
                fv.extend(self.visit_formula(right));
                fv
            }
            FormulaInner::Nary { formulas, .. } => {
                let mut fv = FxHashSet::default();
                for f in formulas {
                    fv.extend(self.visit_formula(f));
                }
                fv
            }
            FormulaInner::Not(inner) => self.visit_formula(inner),
            FormulaInner::Quantified { declarations, body, .. } => {
                self.visit_quantified(declarations, |this| this.visit_formula(body))
            }
            FormulaInner::Comparison { left, right, .. } => {
                let mut fv = self.visit_expression(left);
                fv.extend(self.visit_expression(right));
                fv
            }
            FormulaInner::Multiplicity { expr, .. } => {
                self.visit_expression(expr)
            }
            FormulaInner::IntComparison { left, right, .. } => {
                let mut fv = self.visit_int_expr(left);
                fv.extend(self.visit_int_expr(right));
                fv
            }
            FormulaInner::RelationPredicate(pred) => {
                self.visit_relation_predicate(pred)
            }
        };

        if let Some(id) = id {
            self.cache_if_needed(id, free_vars)
        } else {
            free_vars
        }
    }

    fn visit_relation_predicate(&mut self, pred: &RelationPredicate) -> FxHashSet<Variable> {
        match pred {
            RelationPredicate::Acyclic { .. } => FxHashSet::default(),
            RelationPredicate::TotalOrdering { .. } => FxHashSet::default(),
            RelationPredicate::Function { domain, range, .. } => {
                let mut fv = self.visit_expression(domain);
                fv.extend(self.visit_expression(range));
                fv
            }
        }
    }

    fn visit_expression(&mut self, expr: &Expression) -> FxHashSet<Variable> {
        let id = NodeId::from_expr(expr);

        // Check if already computed
        if let Some(id) = id {
            if let Some(cached) = self.free_vars.get(&id) {
                return cached.clone();
            }
        }

        let free_vars = match &*expr.inner() {
            ExpressionInner::Relation(_) | ExpressionInner::Constant(_) => FxHashSet::default(),
            ExpressionInner::Variable(var) => {
                let mut fv = FxHashSet::default();
                fv.insert(var.clone());
                fv
            }
            ExpressionInner::Binary { left, right, .. } => {
                let mut fv = self.visit_expression(left);
                fv.extend(self.visit_expression(right));
                fv
            }
            ExpressionInner::Unary { expr, .. } => self.visit_expression(expr),
            ExpressionInner::Nary { exprs, .. } => {
                let mut fv = FxHashSet::default();
                for e in exprs {
                    fv.extend(self.visit_expression(e));
                }
                fv
            }
            ExpressionInner::Comprehension { declarations, formula } => {
                self.visit_quantified(declarations, |this| this.visit_formula(formula))
            }
            ExpressionInner::IntToExprCast { int_expr, .. } => {
                self.visit_int_expr(int_expr)
            }
            ExpressionInner::If { condition, then_expr, else_expr, .. } => {
                let mut fv = self.visit_formula(condition);
                fv.extend(self.visit_expression(then_expr));
                fv.extend(self.visit_expression(else_expr));
                fv
            }
        };

        if let Some(id) = id {
            self.cache_if_needed(id, free_vars)
        } else {
            free_vars
        }
    }

    fn visit_int_expr(&mut self, expr: &IntExpression) -> FxHashSet<Variable> {
        let id = NodeId::from_int_expr(expr);

        // Check if already computed
        if let Some(id) = id {
            if let Some(cached) = self.free_vars.get(&id) {
                return cached.clone();
            }
        }

        let free_vars = match expr.inner() {
            IntExpressionInner::Constant(_) => FxHashSet::default(),
            IntExpressionInner::Cardinality(expr) | IntExpressionInner::ExprCast(expr) => {
                self.visit_expression(expr)
            }
            IntExpressionInner::Binary { left, right, .. } => {
                let mut fv = self.visit_int_expr(left);
                fv.extend(self.visit_int_expr(right));
                fv
            }
            IntExpressionInner::Nary { exprs, .. } => {
                let mut fv = FxHashSet::default();
                for e in exprs {
                    fv.extend(self.visit_int_expr(e));
                }
                fv
            }
            IntExpressionInner::Unary { expr, .. } => self.visit_int_expr(expr),
            IntExpressionInner::If { condition, then_expr, else_expr } => {
                let mut fv = self.visit_formula(condition);
                fv.extend(self.visit_int_expr(then_expr));
                fv.extend(self.visit_int_expr(else_expr));
                fv
            }
            IntExpressionInner::Sum { decls, expr } => {
                self.visit_quantified(decls, |this| this.visit_int_expr(expr))
            }
        };

        if let Some(id) = id {
            self.cache_if_needed(id, free_vars)
        } else {
            free_vars
        }
    }

    /// Visit a quantified construct (quantifier, comprehension, sum)
    fn visit_quantified<F, R>(&mut self, decls: &Decls, body: F) -> FxHashSet<Variable>
    where
        F: FnOnce(&mut Self) -> R,
        R: IntoIterator<Item = Variable>,
    {
        let mut free_vars = FxHashSet::default();
        let mut bound_vars = FxHashSet::default();

        // Process declarations, collecting free vars from each decl's expression
        for decl in decls.iter() {
            let decl_fv = self.visit_expression(decl.expression());
            for v in decl_fv {
                if !bound_vars.contains(&v) {
                    free_vars.insert(v);
                }
            }
            self.vars_in_scope.push(decl.variable().clone());
            bound_vars.insert(decl.variable().clone());
        }

        // Process body
        let body_fv = body(self);
        for v in body_fv {
            if !bound_vars.contains(&v) {
                free_vars.insert(v);
            }
        }

        // Pop bound variables from scope
        for _ in 0..decls.size() {
            self.vars_in_scope.pop();
        }

        free_vars
    }
}

/// Cache record for nodes without free variables
struct NoVarRecord<T> {
    translation: Option<T>,
}

impl<T: Clone> NoVarRecord<T> {
    fn new() -> Self {
        Self { translation: None }
    }

    fn get(&self) -> Option<T> {
        self.translation.clone()
    }

    fn set(&mut self, translation: T) {
        self.translation = Some(translation);
    }
}

/// Cache record for nodes with free variables
/// Stores translation along with the variable bindings used to generate it
struct MultiVarRecord<T> {
    /// The free variables of this node
    variables: Vec<Variable>,
    /// The tuple indices for each variable when the translation was created
    bindings: Vec<usize>,
    /// The cached translation
    translation: Option<T>,
}

impl<T: Clone> MultiVarRecord<T> {
    fn new(variables: impl IntoIterator<Item = Variable>) -> Self {
        let variables: Vec<_> = variables.into_iter().collect();
        let bindings = vec![0; variables.len()];
        Self {
            variables,
            bindings,
            translation: None,
        }
    }

    /// Get cached translation if current bindings match
    fn get<'a>(&self, env: &super::Environment<'a>) -> Option<T> {
        let translation = self.translation.as_ref()?;

        // Check if all variable bindings match
        for (i, var) in self.variables.iter().enumerate() {
            if let Some(matrix) = env.lookup(var) {
                // Get the tuple index from the matrix (should have density 1)
                if let Some((idx, _)) = matrix.iter_indexed().next() {
                    if idx != self.bindings[i] {
                        return None; // Binding doesn't match
                    }
                } else {
                    return None; // No binding
                }
            } else {
                return None; // Variable not in environment
            }
        }

        Some(translation.clone())
    }

    /// Set cached translation with current bindings
    fn set<'a>(&mut self, translation: T, env: &super::Environment<'a>) {
        for (i, var) in self.variables.iter().enumerate() {
            if let Some(matrix) = env.lookup(var) {
                if let Some((idx, _)) = matrix.iter_indexed().next() {
                    self.bindings[i] = idx;
                }
            }
        }
        self.translation = Some(translation);
    }
}

/// Cache record enum
enum CacheRecord<T> {
    NoVar(NoVarRecord<T>),
    MultiVar(MultiVarRecord<T>),
}

impl<T: Clone> CacheRecord<T> {
    fn get<'a>(&self, env: &super::Environment<'a>) -> Option<T> {
        match self {
            CacheRecord::NoVar(r) => r.get(),
            CacheRecord::MultiVar(r) => r.get(env),
        }
    }

    fn set<'a>(&mut self, translation: T, env: &super::Environment<'a>) {
        match self {
            CacheRecord::NoVar(r) => r.set(translation),
            CacheRecord::MultiVar(r) => r.set(translation, env),
        }
    }
}

/// Main translation cache following Java's FOL2BoolCache
pub struct TranslationCache<'a> {
    expr_cache: FxHashMap<NodeId, CacheRecord<BooleanMatrix<'a>>>,
    formula_cache: FxHashMap<NodeId, CacheRecord<BoolValue<'a>>>,
}

impl<'a> TranslationCache<'a> {
    /// Create an empty cache (for approximate translations that don't need caching)
    pub fn empty() -> Self {
        Self {
            expr_cache: FxHashMap::default(),
            formula_cache: FxHashMap::default(),
        }
    }

    /// Build a translation cache for the given formula
    pub fn new(formula: &Formula) -> Self {
        // Phase 1: Detect shared nodes
        let shared_nodes = SharingDetector::detect_sharing(formula);

        // Phase 2: Collect free variables for cacheable nodes
        let free_vars = FreeVariableCollector::collect(formula, shared_nodes);

        // Phase 3: Build cache records
        let mut expr_cache = FxHashMap::default();
        let mut formula_cache = FxHashMap::default();

        for (id, vars) in free_vars {
            let record: CacheRecord<BooleanMatrix<'a>> = if vars.is_empty() {
                CacheRecord::NoVar(NoVarRecord::new())
            } else {
                CacheRecord::MultiVar(MultiVarRecord::new(vars.clone()))
            };

            match id {
                NodeId::Expr(_) | NodeId::IntExpr(_) => {
                    expr_cache.insert(id, record);
                }
                NodeId::Formula(_) => {
                    let record: CacheRecord<BoolValue<'a>> = if vars.is_empty() {
                        CacheRecord::NoVar(NoVarRecord::new())
                    } else {
                        CacheRecord::MultiVar(MultiVarRecord::new(vars))
                    };
                    formula_cache.insert(id, record);
                }
            }
        }

        Self {
            expr_cache,
            formula_cache,
        }
    }

    /// Look up cached expression translation
    pub fn lookup_expr(&self, expr: &Expression, env: &super::Environment<'a>) -> Option<BooleanMatrix<'a>> {
        let id = NodeId::from_expr(expr)?;
        self.expr_cache.get(&id)?.get(env)
    }

    /// Cache expression translation
    pub fn cache_expr(&mut self, expr: &Expression, translation: BooleanMatrix<'a>, env: &super::Environment<'a>) {
        if let Some(id) = NodeId::from_expr(expr) {
            if let Some(record) = self.expr_cache.get_mut(&id) {
                record.set(translation, env);
            }
        }
    }

    /// Look up cached formula translation
    pub fn lookup_formula(&self, formula: &Formula, env: &super::Environment<'a>) -> Option<BoolValue<'a>> {
        let id = NodeId::from_formula(formula)?;
        self.formula_cache.get(&id)?.get(env)
    }

    /// Cache formula translation
    pub fn cache_formula(&mut self, formula: &Formula, translation: BoolValue<'a>, env: &super::Environment<'a>) {
        if let Some(id) = NodeId::from_formula(formula) {
            if let Some(record) = self.formula_cache.get_mut(&id) {
                record.set(translation, env);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Expression, Formula, Relation};

    #[test]
    fn test_sharing_detector_no_sharing() {
        let r = Relation::unary("R");
        let s = Relation::unary("S");
        let formula = Expression::from(r).some().and(Expression::from(s).some());

        let shared = SharingDetector::detect_sharing(&formula);
        assert!(shared.is_empty());
    }

    #[test]
    fn test_sharing_detector_with_sharing() {
        let r = Relation::unary("R");
        let r_expr = Expression::from(r);
        // Use the same expression twice
        let formula = r_expr.clone().some().and(r_expr.some());

        let shared = SharingDetector::detect_sharing(&formula);
        // The r_expr should be detected as shared
        assert!(!shared.is_empty());
    }
}
