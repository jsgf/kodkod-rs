//! Formula types for first-order logic

use super::int_expr::{IntCompareOp, IntExpression};
use super::{Expression, Variable};

/// Operators for binary formulas
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompareOp {
    /// Set equality
    Equals,
    /// Subset
    Subset,
}

/// Multiplicity operators
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Multiplicity {
    /// At least one element (some)
    Some,
    /// Exactly one element
    One,
    /// At most one element (lone)
    Lone,
    /// No elements
    No,
}

/// Quantifiers
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Quantifier {
    /// Universal quantification (forall)
    All,
    /// Existential quantification (exists)
    Some,
}

/// A first-order formula
#[expect(missing_docs)]
#[derive(Clone, Debug)]
pub enum Formula {
    /// Constant formula (TRUE or FALSE)
    Constant(bool),
    /// Binary formula (AND, OR, IFF, IMPLIES)
    Binary {
        left: Box<Formula>,
        op: BinaryFormulaOp,
        right: Box<Formula>,
    },
    /// N-ary formula (conjunction/disjunction of multiple formulas)
    Nary {
        op: BinaryFormulaOp, // Only AND or OR
        formulas: Vec<Formula>,
    },
    /// Negation
    Not(Box<Formula>),
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
        body: Box<Formula>,
    },
    /// Integer comparison
    IntComparison {
        left: Box<IntExpression>,
        op: IntCompareOp,
        right: Box<IntExpression>,
    },
}

impl Formula {
    /// Constant TRUE formula
    pub const TRUE: Formula = Formula::Constant(true);
    /// Constant FALSE formula
    pub const FALSE: Formula = Formula::Constant(false);

    /// Returns a constant formula with the given value
    pub fn constant(value: bool) -> Formula {
        Formula::Constant(value)
    }

    /// Logical AND
    pub fn and(self, other: Formula) -> Formula {
        Formula::Binary {
            left: Box::new(self),
            op: BinaryFormulaOp::And,
            right: Box::new(other),
        }
    }

    /// Logical OR
    pub fn or(self, other: Formula) -> Formula {
        Formula::Binary {
            left: Box::new(self),
            op: BinaryFormulaOp::Or,
            right: Box::new(other),
        }
    }

    /// If and only if (biconditional)
    pub fn iff(self, other: Formula) -> Formula {
        Formula::Binary {
            left: Box::new(self),
            op: BinaryFormulaOp::Iff,
            right: Box::new(other),
        }
    }

    /// Implication
    pub fn implies(self, other: Formula) -> Formula {
        Formula::Binary {
            left: Box::new(self),
            op: BinaryFormulaOp::Implies,
            right: Box::new(other),
        }
    }

    /// Negation
    pub fn not(self) -> Formula {
        Formula::Not(Box::new(self))
    }

    /// N-ary conjunction
    pub fn and_all(formulas: Vec<Formula>) -> Formula {
        if formulas.is_empty() {
            return Formula::TRUE;
        }
        if formulas.len() == 1 {
            return formulas.into_iter().next().unwrap();
        }
        Formula::Nary {
            op: BinaryFormulaOp::And,
            formulas,
        }
    }

    /// N-ary disjunction
    pub fn or_all(formulas: Vec<Formula>) -> Formula {
        if formulas.is_empty() {
            return Formula::FALSE;
        }
        if formulas.len() == 1 {
            return formulas.into_iter().next().unwrap();
        }
        Formula::Nary {
            op: BinaryFormulaOp::Or,
            formulas,
        }
    }

    /// Universal quantification (forall)
    pub fn forall(declarations: Decls, body: Formula) -> Formula {
        Formula::Quantified {
            quantifier: Quantifier::All,
            declarations,
            body: Box::new(body),
        }
    }

    /// Existential quantification (exists)
    pub fn exists(declarations: Decls, body: Formula) -> Formula {
        Formula::Quantified {
            quantifier: Quantifier::Some,
            declarations,
            body: Box::new(body),
        }
    }
}

impl Expression {
    /// Expression equals another
    pub fn equals(self, other: Expression) -> Formula {
        Formula::Comparison {
            left: self,
            op: CompareOp::Equals,
            right: other,
        }
    }

    /// Expression is subset of another
    pub fn in_set(self, other: Expression) -> Formula {
        Formula::Comparison {
            left: self,
            op: CompareOp::Subset,
            right: other,
        }
    }

    /// Expression has at least one element
    pub fn some(self) -> Formula {
        Formula::Multiplicity {
            mult: Multiplicity::Some,
            expr: self,
        }
    }

    /// Expression has exactly one element
    pub fn one(self) -> Formula {
        Formula::Multiplicity {
            mult: Multiplicity::One,
            expr: self,
        }
    }

    /// Expression has at most one element
    pub fn lone(self) -> Formula {
        Formula::Multiplicity {
            mult: Multiplicity::Lone,
            expr: self,
        }
    }

    /// Expression has no elements
    pub fn no(self) -> Formula {
        Formula::Multiplicity {
            mult: Multiplicity::No,
            expr: self,
        }
    }
}

/// A variable declaration (e.g., "x: Expression")
#[derive(Clone, Debug)]
pub struct Decl {
    variable: Variable,
    multiplicity: Multiplicity,
    expression: Expression,
}

impl Decl {
    /// Creates a new declaration with "one of" multiplicity
    pub fn one_of(variable: &Variable, expression: &Expression) -> Self {
        Self {
            variable: variable.clone(),
            multiplicity: Multiplicity::One,
            expression: expression.clone(),
        }
    }

    /// Creates a new declaration with "lone" multiplicity
    pub fn lone_of(variable: &Variable, expression: &Expression) -> Self {
        Self {
            variable: variable.clone(),
            multiplicity: Multiplicity::Lone,
            expression: expression.clone(),
        }
    }

    /// Creates a new declaration with "some" multiplicity
    pub fn some_of(variable: &Variable, expression: &Expression) -> Self {
        Self {
            variable: variable.clone(),
            multiplicity: Multiplicity::Some,
            expression: expression.clone(),
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
#[derive(Clone, Debug)]
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
}

#[cfg(test)]
mod tests {
    use super::super::{Expression, Relation};
    use super::*;

    #[test]
    fn constant_formulas() {
        assert!(matches!(Formula::TRUE, Formula::Constant(true)));
        assert!(matches!(Formula::FALSE, Formula::Constant(false)));
        assert!(matches!(Formula::constant(true), Formula::Constant(true)));
    }

    #[test]
    fn binary_formulas() {
        let f1 = Formula::TRUE;
        let f2 = Formula::FALSE;

        let and = f1.clone().and(f2.clone());
        assert!(matches!(and, Formula::Binary { op: BinaryFormulaOp::And, .. }));

        let or = f1.clone().or(f2.clone());
        assert!(matches!(or, Formula::Binary { op: BinaryFormulaOp::Or, .. }));

        let iff = f1.clone().iff(f2.clone());
        assert!(matches!(iff, Formula::Binary { op: BinaryFormulaOp::Iff, .. }));

        let implies = f1.implies(f2);
        assert!(matches!(implies, Formula::Binary { op: BinaryFormulaOp::Implies, .. }));
    }

    #[test]
    fn negation() {
        let not = Formula::TRUE.not();
        assert!(matches!(not, Formula::Not(_)));
    }

    #[test]
    fn nary_formulas() {
        let f1 = Formula::TRUE;
        let f2 = Formula::FALSE;
        let f3 = Formula::TRUE;

        let and = Formula::and_all(vec![f1.clone(), f2.clone(), f3.clone()]);
        assert!(matches!(and, Formula::Nary { op: BinaryFormulaOp::And, .. }));

        let or = Formula::or_all(vec![f1, f2, f3]);
        assert!(matches!(or, Formula::Nary { op: BinaryFormulaOp::Or, .. }));

        // Empty cases
        assert!(matches!(Formula::and_all(vec![]), Formula::Constant(true)));
        assert!(matches!(Formula::or_all(vec![]), Formula::Constant(false)));
    }

    #[test]
    fn expression_comparisons() {
        let r1 = Relation::unary("A");
        let r2 = Relation::unary("B");

        let eq = Expression::from(r1.clone()).equals(Expression::from(r2.clone()));
        assert!(matches!(eq, Formula::Comparison { op: CompareOp::Equals, .. }));

        let subset = Expression::from(r1).in_set(Expression::from(r2));
        assert!(matches!(subset, Formula::Comparison { op: CompareOp::Subset, .. }));
    }

    #[test]
    fn multiplicity_formulas() {
        let r = Relation::unary("Person");

        let some = Expression::from(r.clone()).some();
        assert!(matches!(some, Formula::Multiplicity { mult: Multiplicity::Some, .. }));

        let one = Expression::from(r.clone()).one();
        assert!(matches!(one, Formula::Multiplicity { mult: Multiplicity::One, .. }));

        let lone = Expression::from(r.clone()).lone();
        assert!(matches!(lone, Formula::Multiplicity { mult: Multiplicity::Lone, .. }));

        let no = Expression::from(r).no();
        assert!(matches!(no, Formula::Multiplicity { mult: Multiplicity::No, .. }));
    }

    #[test]
    fn declarations() {
        let person = Relation::unary("Person");
        let x = Variable::unary("x");

        let decl = Decl::one_of(&x, &Expression::from(person.clone()));
        assert_eq!(decl.variable(), &x);
        assert_eq!(decl.multiplicity(), Multiplicity::One);

        let decls = Decls::from(decl);
        assert_eq!(decls.size(), 1);
    }

    #[test]
    fn quantified_formulas() {
        let person = Relation::unary("Person");
        let x = Variable::unary("x");

        let decl = Decl::one_of(&x, &Expression::from(person.clone()));
        let decls = Decls::from(decl);

        let body = Expression::from(x.clone()).in_set(Expression::from(person));
        let forall = Formula::forall(decls.clone(), body.clone());
        assert!(matches!(forall, Formula::Quantified { quantifier: Quantifier::All, .. }));

        let exists = Formula::exists(decls, body);
        assert!(matches!(exists, Formula::Quantified { quantifier: Quantifier::Some, .. }));
    }

    #[test]
    fn complex_formula() {
        // all p: Person | p in Person
        let person = Relation::unary("Person");
        let p = Variable::unary("p");

        let decl = Decl::one_of(&p, &Expression::from(person.clone()));
        let decls = Decls::from(decl);

        let body = Expression::from(p).in_set(Expression::from(person));
        let formula = Formula::forall(decls, body);

        assert!(matches!(formula, Formula::Quantified { .. }));
    }
}
