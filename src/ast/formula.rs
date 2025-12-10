//! Formula types for first-order logic

use std::borrow::Cow;
use std::rc::Rc;

use super::int_expr::{IntCompareOp, IntExpression};
use super::{Expression, Relation, Variable};

/// Relation predicate names
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RelationPredicateName {
    /// Acyclic predicate - relation has no cycles
    Acyclic,
    /// Total ordering predicate - relation is a total order
    TotalOrdering,
    /// Function predicate - relation is a total function
    Function,
}

/// Relation predicates - special constraints on binary relations
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum RelationPredicate {
    /// Acyclic predicate: relation.closure() & IDEN = empty
    Acyclic {
        /// The binary relation that must be acyclic
        relation: Relation,
    },
    /// Total ordering predicate: relation orders a set with first/last elements
    TotalOrdering {
        /// The binary relation representing the ordering
        relation: Relation,
        /// The set of atoms being ordered
        ordered: Relation,
        /// The first element in the ordering
        first: Relation,
        /// The last element in the ordering
        last: Relation,
    },
    /// Function predicate: relation is a total function
    Function {
        /// The binary relation that must be a function
        relation: Relation,
        /// Domain of the function
        domain: Expression,
        /// Range of the function
        range: Expression,
    },
}

impl RelationPredicate {
    /// Returns the name of this predicate
    pub fn name(&self) -> RelationPredicateName {
        match self {
            RelationPredicate::Acyclic { .. } => RelationPredicateName::Acyclic,
            RelationPredicate::TotalOrdering { .. } => RelationPredicateName::TotalOrdering,
            RelationPredicate::Function { .. } => RelationPredicateName::Function,
        }
    }

    /// Returns the primary relation constrained by this predicate
    pub fn relation(&self) -> &Relation {
        match self {
            RelationPredicate::Acyclic { relation } => relation,
            RelationPredicate::TotalOrdering { relation, .. } => relation,
            RelationPredicate::Function { relation, .. } => relation,
        }
    }

    /// Converts this predicate to explicit constraints
    pub fn to_constraints(&self) -> Formula {
        match self {
            RelationPredicate::Acyclic { relation } => {
                // acyclic <=> no (relation.closure() & IDEN)
                let closure = Expression::from(relation.clone()).closure();
                let iden = Expression::IDEN;
                closure.intersection(iden).no()
            }
            RelationPredicate::TotalOrdering {
                relation,
                ordered,
                first,
                last,
            } => {
                // one first && one last && last in ordered
                let f0 = Expression::from(first.clone())
                    .one()
                    .and(Expression::from(last.clone()).one())
                    .and(Expression::from(last.clone()).in_set(Expression::from(ordered.clone())));

                // ordered = first.*relation
                let f1 = Expression::from(ordered.clone()).equals(
                    Expression::from(first.clone())
                        .join(Expression::from(relation.clone()).reflexive_closure()),
                );

                // no relation.first && no last.relation
                let f2 = Expression::from(relation.clone())
                    .join(Expression::from(first.clone()))
                    .no()
                    .and(
                        Expression::from(last.clone())
                            .join(Expression::from(relation.clone()))
                            .no(),
                    );

                // all e: ordered - last | one e.relation
                let e = Variable::unary(format!("e{}", relation.name()));
                let f3 = Formula::forall(
                    Decls::from(Decl::one_of(
                        e.clone(),
                        Expression::from(ordered.clone())
                            .difference(Expression::from(last.clone())),
                    )),
                    Expression::from(e).join(Expression::from(relation.clone())).one(),
                );

                Formula::and(Formula::and(f0, f1), Formula::and(f2, f3))
            }
            RelationPredicate::Function { relation, domain, range } => {
                // function <=> relation in domain->range && all x: domain | one x.relation
                let domain_to_range = domain.clone().product(range.clone());
                let f0 = Expression::from(relation.clone()).in_set(domain_to_range);

                let x = Variable::unary(format!("x{}", relation.name()));
                let f1 = Formula::forall(
                    Decls::from(Decl::one_of(x.clone(), domain.clone())),
                    Expression::from(x).join(Expression::from(relation.clone())).one(),
                );

                f0.and(f1)
            }
        }
    }

    /// Creates an acyclic predicate
    pub fn acyclic(relation: Relation) -> Self {
        assert_eq!(relation.arity(), 2, "Acyclic requires a binary relation");
        RelationPredicate::Acyclic { relation }
    }

    /// Creates a total ordering predicate
    pub fn total_ordering(
        relation: Relation,
        ordered: Relation,
        first: Relation,
        last: Relation,
    ) -> Self {
        assert_eq!(relation.arity(), 2, "TotalOrdering requires a binary relation");
        assert_eq!(ordered.arity(), 1, "ordered must be unary");
        assert_eq!(first.arity(), 1, "first must be unary");
        assert_eq!(last.arity(), 1, "last must be unary");
        RelationPredicate::TotalOrdering {
            relation,
            ordered,
            first,
            last,
        }
    }

    /// Creates a function predicate
    /// Following Java: Relation.function(Expression domain, Expression range)
    pub fn function(relation: Relation, domain: Expression, range: Expression) -> Self {
        assert_eq!(relation.arity(), 2, "Function requires a binary relation");
        assert_eq!(domain.arity(), 1, "Domain must be unary");
        assert_eq!(range.arity(), 1, "Range must be unary");
        RelationPredicate::Function { relation, domain, range }
    }
}

/// Operators for binary formulas
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinaryFormulaOp {
    /// Logical AND
    And,
    /// Logical OR
    Or,
    /// If and only if
    Iff,
    /// Implies
    Implies,
}

/// Comparison operators for expressions
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CompareOp {
    /// Set equality
    Equals,
    /// Subset
    Subset,
}

/// Multiplicity operators
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Multiplicity {
    /// At least one element (some)
    Some,
    /// Exactly one element
    One,
    /// At most one element (lone)
    Lone,
    /// No elements
    No,
    /// Any number of elements (no constraint)
    Set,
}

/// Quantifiers
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Quantifier {
    /// Universal quantification (forall)
    All,
    /// Existential quantification (exists)
    Some,
}

/// A first-order formula (reference-counted for efficient sharing)
#[derive(Clone, Debug)]
pub enum Formula {
    /// Reference-counted shared formula (for compound formulas)
    Ref(Rc<FormulaInner>),
    /// Constant TRUE (inline, no allocation)
    True,
    /// Constant FALSE (inline, no allocation)
    False,
}

impl Formula {
    /// Constant TRUE formula
    pub const TRUE: Formula = Formula::True;

    /// Constant FALSE formula
    pub const FALSE: Formula = Formula::False;
}

impl PartialEq for Formula {
    fn eq(&self, other: &Self) -> bool {
        // Use structural equality through the inner representation
        self.inner() == other.inner()
    }
}

impl Eq for Formula {}

impl std::hash::Hash for Formula {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.inner().hash(state);
    }
}

/// Inner representation of a formula
#[expect(missing_docs)]
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum FormulaInner {
    /// Constant formula (TRUE or FALSE)
    Constant(bool),
    /// Binary formula (AND, OR, IFF, IMPLIES)
    Binary {
        left: Formula,
        op: BinaryFormulaOp,
        right: Formula,
    },
    /// N-ary formula (conjunction/disjunction of multiple formulas)
    Nary {
        op: BinaryFormulaOp, // Only AND or OR
        formulas: Vec<Formula>,
    },
    /// Negation
    Not(Formula),
    /// Expression comparison (equals, subset)
    Comparison {
        left: Expression,
        op: CompareOp,
        right: Expression,
    },
    /// Multiplicity constraint (some, one, lone, no)
    Multiplicity {
        mult: Multiplicity,
        expr: Expression,
    },
    /// Quantified formula (forall/exists)
    Quantified {
        quantifier: Quantifier,
        declarations: Decls,
        body: Formula,
    },
    /// Integer comparison
    IntComparison {
        left: Box<IntExpression>,
        op: IntCompareOp,
        right: Box<IntExpression>,
    },
    /// Relation predicate (acyclic, total ordering, function)
    RelationPredicate(RelationPredicate),
}

impl Formula {
    /// Returns a constant formula with the given value
    pub fn constant(value: bool) -> Formula {
        if value { Formula::TRUE } else { Formula::FALSE }
    }

    /// Logical AND
    pub fn and(self, other: Formula) -> Formula {
        Formula::Ref(Rc::new(FormulaInner::Binary {
            left: self,
            op: BinaryFormulaOp::And,
            right: other,
        }))
    }

    /// Logical OR
    pub fn or(self, other: Formula) -> Formula {
        Formula::Ref(Rc::new(FormulaInner::Binary {
            left: self,
            op: BinaryFormulaOp::Or,
            right: other,
        }))
    }

    /// If and only if (biconditional)
    pub fn iff(self, other: Formula) -> Formula {
        Formula::Ref(Rc::new(FormulaInner::Binary {
            left: self,
            op: BinaryFormulaOp::Iff,
            right: other,
        }))
    }

    /// Implication
    pub fn implies(self, other: Formula) -> Formula {
        Formula::Ref(Rc::new(FormulaInner::Binary {
            left: self,
            op: BinaryFormulaOp::Implies,
            right: other,
        }))
    }

    /// Negation
    pub fn not(self) -> Formula {
        Formula::Ref(Rc::new(FormulaInner::Not(self)))
    }

    /// N-ary conjunction
    pub fn and_all(formulas: Vec<Formula>) -> Formula {
        if formulas.is_empty() {
            return Formula::TRUE;
        }
        if formulas.len() == 1 {
            return formulas.into_iter().next().unwrap();
        }
        Formula::Ref(Rc::new(FormulaInner::Nary {
            op: BinaryFormulaOp::And,
            formulas,
        }))
    }

    /// N-ary disjunction
    pub fn or_all(formulas: Vec<Formula>) -> Formula {
        if formulas.is_empty() {
            return Formula::FALSE;
        }
        if formulas.len() == 1 {
            return formulas.into_iter().next().unwrap();
        }
        Formula::Ref(Rc::new(FormulaInner::Nary {
            op: BinaryFormulaOp::Or,
            formulas,
        }))
    }

    /// Universal quantification (forall)
    pub fn forall(declarations: Decls, body: Formula) -> Formula {
        Formula::Ref(Rc::new(FormulaInner::Quantified {
            quantifier: Quantifier::All,
            declarations,
            body,
        }))
    }

    /// Existential quantification (exists)
    pub fn exists(declarations: Decls, body: Formula) -> Formula {
        Formula::Ref(Rc::new(FormulaInner::Quantified {
            quantifier: Quantifier::Some,
            declarations,
            body,
        }))
    }

    /// Returns a reference to the inner formula
    /// Returns Cow::Borrowed for Ref variant, Cow::Owned for True/False
    pub fn inner(&self) -> Cow<'_, FormulaInner> {
        match self {
            Formula::Ref(rc) => Cow::Borrowed(rc.as_ref()),
            Formula::True => Cow::Owned(FormulaInner::Constant(true)),
            Formula::False => Cow::Owned(FormulaInner::Constant(false)),
        }
    }

    /// Creates an integer comparison formula
    pub fn int_comparison(left: IntExpression, op: IntCompareOp, right: IntExpression) -> Formula {
        Formula::Ref(Rc::new(FormulaInner::IntComparison {
            left: Box::new(left),
            op,
            right: Box::new(right),
        }))
    }

    /// Creates a relation predicate formula
    pub fn relation_predicate(pred: RelationPredicate) -> Formula {
        Formula::Ref(Rc::new(FormulaInner::RelationPredicate(pred)))
    }

    /// If-then-else for expressions
    /// Following Java: Formula.thenElse(Expression, Expression)
    /// Returns an expression that evaluates to then_expr if this formula is true,
    /// otherwise evaluates to else_expr.
    ///
    /// # Panics
    /// Panics if then_expr and else_expr have different arities
    pub fn then_else(self, then_expr: Expression, else_expr: Expression) -> Expression {
        assert_eq!(
            then_expr.arity(),
            else_expr.arity(),
            "Arity mismatch: {:?}::{} and {:?}::{}",
            then_expr,
            then_expr.arity(),
            else_expr,
            else_expr.arity()
        );
        let arity = then_expr.arity();
        Expression::if_then_else(self, then_expr, else_expr, arity)
    }

    /// If-then-else for integer expressions
    /// Following Java: Formula.thenElse(IntExpression, IntExpression)
    pub fn then_else_int(self, then_expr: IntExpression, else_expr: IntExpression) -> IntExpression {
        IntExpression::if_then_else(self, then_expr, else_expr)
    }
}

impl Expression {
    /// Expression equals another
    pub fn equals(self, other: Expression) -> Formula {
        Formula::Ref(Rc::new(FormulaInner::Comparison {
            left: self,
            op: CompareOp::Equals,
            right: other,
        }))
    }

    /// Expression does not equal another (convenience method)
    pub fn ne(self, other: Expression) -> Formula {
        self.equals(other).not()
    }

    /// Expression is subset of another
    pub fn in_set(self, other: Expression) -> Formula {
        Formula::Ref(Rc::new(FormulaInner::Comparison {
            left: self,
            op: CompareOp::Subset,
            right: other,
        }))
    }

    /// Expression has at least one element
    pub fn some(self) -> Formula {
        Formula::Ref(Rc::new(FormulaInner::Multiplicity {
            mult: Multiplicity::Some,
            expr: self,
        }))
    }

    /// Expression has exactly one element
    pub fn one(self) -> Formula {
        Formula::Ref(Rc::new(FormulaInner::Multiplicity {
            mult: Multiplicity::One,
            expr: self,
        }))
    }

    /// Expression has at most one element
    pub fn lone(self) -> Formula {
        Formula::Ref(Rc::new(FormulaInner::Multiplicity {
            mult: Multiplicity::Lone,
            expr: self,
        }))
    }

    /// Expression has no elements
    pub fn no(self) -> Formula {
        Formula::Ref(Rc::new(FormulaInner::Multiplicity {
            mult: Multiplicity::No,
            expr: self,
        }))
    }
}

impl Formula {
    /// Creates a set comprehension expression from this formula
    /// Following Java: Formula.comprehension(Decls)
    /// Returns {declarations | self}
    pub fn comprehension(self, declarations: Decls) -> Expression {
        Expression::comprehension(declarations, self)
    }
}

/// A variable declaration (e.g., "x: Expression")
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Decl {
    variable: Variable,
    multiplicity: Multiplicity,
    expression: Expression,
}

impl Decl {
    /// Creates a new declaration with the given multiplicity
    pub fn new(variable: Variable, multiplicity: Multiplicity, expression: Expression) -> Self {
        Self {
            variable,
            multiplicity,
            expression,
        }
    }

    /// Creates a new declaration with "one of" multiplicity
    /// Takes owned values since Variable and Expression clone cheaply (Arc-based)
    pub fn one_of(variable: Variable, expression: Expression) -> Self {
        Self::new(variable, Multiplicity::One, expression)
    }

    /// Creates a new declaration with "lone" multiplicity
    pub fn lone_of(variable: Variable, expression: Expression) -> Self {
        Self {
            variable,
            multiplicity: Multiplicity::Lone,
            expression,
        }
    }

    /// Creates a new declaration with "some" multiplicity
    pub fn some_of(variable: Variable, expression: Expression) -> Self {
        Self {
            variable,
            multiplicity: Multiplicity::Some,
            expression,
        }
    }

    /// Creates a new declaration with "set" multiplicity (no constraint)
    pub fn set_of(variable: Variable, expression: Expression) -> Self {
        Self {
            variable,
            multiplicity: Multiplicity::Set,
            expression,
        }
    }

    /// Returns the variable being declared
    pub fn variable(&self) -> &Variable {
        &self.variable
    }

    /// Returns the multiplicity
    pub fn multiplicity(&self) -> Multiplicity {
        self.multiplicity
    }

    /// Returns the expression
    pub fn expression(&self) -> &Expression {
        &self.expression
    }
}

/// A sequence of variable declarations
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Decls {
    declarations: Vec<Decl>,
}

impl Decls {
    /// Creates a new Decls from a single declaration
    pub fn from(decl: Decl) -> Self {
        Self {
            declarations: vec![decl],
        }
    }

    /// Creates a new Decls from multiple declarations
    pub fn from_vec(declarations: Vec<Decl>) -> Self {
        assert!(!declarations.is_empty(), "Cannot create empty Decls");
        Self { declarations }
    }

    /// Returns the number of declarations
    pub fn size(&self) -> usize {
        self.declarations.len()
    }

    /// Returns an iterator over the declarations
    pub fn iter(&self) -> impl Iterator<Item = &Decl> {
        self.declarations.iter()
    }

    /// Adds a declaration to this Decls
    pub fn and(mut self, decl: Decl) -> Self {
        self.declarations.push(decl);
        self
    }

    /// Combines this Decls with another Decls
    pub fn and_decls(mut self, other: Decls) -> Self {
        self.declarations.extend(other.declarations);
        self
    }
}

#[cfg(test)]
mod tests {
    use super::super::{Expression, Relation};
    use super::*;

    #[test]
    fn constant_formulas() {
        assert!(matches!(&*Formula::TRUE.inner(), FormulaInner::Constant(true)));
        assert!(matches!(&*Formula::FALSE.inner(), FormulaInner::Constant(false)));
        assert!(matches!(&*Formula::constant(true).inner(), FormulaInner::Constant(true)));
    }

    #[test]
    fn binary_formulas() {
        let f1 = Formula::TRUE;
        let f2 = Formula::FALSE;

        let and = f1.clone().and(f2.clone());
        assert!(matches!(&*and.inner(), FormulaInner::Binary { op: BinaryFormulaOp::And, .. }));

        let or = f1.clone().or(f2.clone());
        assert!(matches!(&*or.inner(), FormulaInner::Binary { op: BinaryFormulaOp::Or, .. }));

        let iff = f1.clone().iff(f2.clone());
        assert!(matches!(&*iff.inner(), FormulaInner::Binary { op: BinaryFormulaOp::Iff, .. }));

        let implies = f1.implies(f2);
        assert!(matches!(&*implies.inner(), FormulaInner::Binary { op: BinaryFormulaOp::Implies, .. }));
    }

    #[test]
    fn negation() {
        let not = Formula::TRUE.not();
        assert!(matches!(&*not.inner(), FormulaInner::Not(_)));
    }

    #[test]
    fn nary_formulas() {
        let f1 = Formula::TRUE;
        let f2 = Formula::FALSE;
        let f3 = Formula::TRUE;

        let and = Formula::and_all(vec![f1.clone(), f2.clone(), f3.clone()]);
        assert!(matches!(&*and.inner(), FormulaInner::Nary { op: BinaryFormulaOp::And, .. }));

        let or = Formula::or_all(vec![f1, f2, f3]);
        assert!(matches!(&*or.inner(), FormulaInner::Nary { op: BinaryFormulaOp::Or, .. }));

        // Empty cases
        assert!(matches!(&*Formula::and_all(vec![]).inner(), FormulaInner::Constant(true)));
        assert!(matches!(&*Formula::or_all(vec![]).inner(), FormulaInner::Constant(false)));
    }

    #[test]
    fn expression_comparisons() {
        let r1 = Relation::unary("A");
        let r2 = Relation::unary("B");

        let eq = Expression::from(r1.clone()).equals(Expression::from(r2.clone()));
        assert!(matches!(&*eq.inner(), FormulaInner::Comparison { op: CompareOp::Equals, .. }));

        let subset = Expression::from(r1).in_set(Expression::from(r2));
        assert!(matches!(&*subset.inner(), FormulaInner::Comparison { op: CompareOp::Subset, .. }));
    }

    #[test]
    fn multiplicity_formulas() {
        let r = Relation::unary("Person");

        let some = Expression::from(r.clone()).some();
        assert!(matches!(&*some.inner(), FormulaInner::Multiplicity { mult: Multiplicity::Some, .. }));

        let one = Expression::from(r.clone()).one();
        assert!(matches!(&*one.inner(), FormulaInner::Multiplicity { mult: Multiplicity::One, .. }));

        let lone = Expression::from(r.clone()).lone();
        assert!(matches!(&*lone.inner(), FormulaInner::Multiplicity { mult: Multiplicity::Lone, .. }));

        let no = Expression::from(r).no();
        assert!(matches!(&*no.inner(), FormulaInner::Multiplicity { mult: Multiplicity::No, .. }));
    }

    #[test]
    fn declarations() {
        let person = Relation::unary("Person");
        let x = Variable::unary("x");

        let decl = Decl::one_of(x.clone(), Expression::from(&person));
        assert_eq!(decl.variable(), &x);
        assert_eq!(decl.multiplicity(), Multiplicity::One);

        let decls = Decls::from(decl);
        assert_eq!(decls.size(), 1);
    }

    #[test]
    fn quantified_formulas() {
        let person = Relation::unary("Person");
        let x = Variable::unary("x");

        let decl = Decl::one_of(x.clone(), Expression::from(&person));
        let decls = Decls::from(decl);

        let body = Expression::from(x.clone()).in_set(Expression::from(&person));
        let forall = Formula::forall(decls.clone(), body.clone());
        assert!(matches!(&*forall.inner(), FormulaInner::Quantified { quantifier: Quantifier::All, .. }));

        let exists = Formula::exists(decls, body);
        assert!(matches!(&*exists.inner(), FormulaInner::Quantified { quantifier: Quantifier::Some, .. }));
    }

    #[test]
    fn complex_formula() {
        // all p: Person | p in Person
        let person = Relation::unary("Person");
        let p = Variable::unary("p");

        let decl = Decl::one_of(p.clone(), Expression::from(&person));
        let decls = Decls::from(decl);

        let body = Expression::from(p).in_set(Expression::from(&person));
        let formula = Formula::forall(decls, body);

        assert!(matches!(&*formula.inner(), FormulaInner::Quantified { .. }));
    }
}
