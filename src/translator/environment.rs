//! Environment for variable bindings during translation
//!
//! Following Java: kodkod.engine.fol2sat.Environment

use crate::ast::Variable;
use crate::bool::BooleanMatrix;

/// Stack-based environment for quantified variable bindings
///
/// Following Java: Environment
pub struct Environment<'arena> {
    /// Stack of (variable, value) bindings
    bindings: Vec<(Variable, BooleanMatrix<'arena>)>,
}

impl<'arena> Environment<'arena> {
    /// Creates an empty environment
    pub fn empty() -> Self {
        Self {
            bindings: Vec::new(),
        }
    }

    /// Pushes a new binding (for entering quantifier scope)
    /// Following Java: Environment.extend(Variable, T)
    pub fn extend(&mut self, var: Variable, value: BooleanMatrix<'arena>) {
        self.bindings.push((var, value));
    }

    /// Pops the most recent binding (for exiting quantifier scope)
    /// Following Java: env = env.parent()
    pub fn pop(&mut self) {
        self.bindings.pop();
    }

    /// Looks up a variable in the environment (searches from top to bottom)
    /// Following Java: Environment.lookup(Variable)
    pub fn lookup(&self, var: &Variable) -> Option<&BooleanMatrix<'arena>> {
        // Search backwards (most recent binding first)
        for (v, value) in self.bindings.iter().rev() {
            if v == var {
                return Some(value);
            }
        }
        None
    }

    /// Looks up a variable mutably in the environment
    pub fn lookup_mut(&mut self, var: &Variable) -> Option<&mut BooleanMatrix<'arena>> {
        // Search backwards (most recent binding first)
        for (v, value) in self.bindings.iter_mut().rev() {
            if v == var {
                return Some(value);
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bool::{BooleanMatrix, Dimensions};

    #[test]
    fn test_empty_environment() {
        let env = Environment::empty();
        let x = Variable::unary("x");
        assert!(env.lookup(&x).is_none());
    }

    #[test]
    fn test_extend_and_lookup() {
        let mut env = Environment::empty();
        let x = Variable::unary("x");
        let y = Variable::unary("y");

        let matrix1 = BooleanMatrix::empty(Dimensions::new(2, 1));
        let matrix2 = BooleanMatrix::empty(Dimensions::new(3, 1));

        env.extend(x.clone(), matrix1.clone());
        assert!(env.lookup(&x).is_some());
        assert!(env.lookup(&y).is_none());

        env.extend(y.clone(), matrix2.clone());
        assert!(env.lookup(&x).is_some());
        assert!(env.lookup(&y).is_some());
    }

    #[test]
    fn test_pop() {
        let mut env = Environment::empty();
        let x = Variable::unary("x");
        let y = Variable::unary("y");

        let matrix1 = BooleanMatrix::empty(Dimensions::new(2, 1));
        let matrix2 = BooleanMatrix::empty(Dimensions::new(3, 1));

        env.extend(x.clone(), matrix1.clone());
        env.extend(y.clone(), matrix2.clone());

        assert!(env.lookup(&x).is_some());
        assert!(env.lookup(&y).is_some());

        env.pop();
        assert!(env.lookup(&x).is_some());
        assert!(env.lookup(&y).is_none());

        env.pop();
        assert!(env.lookup(&x).is_none());
    }

    #[test]
    fn test_shadowing() {
        let mut env = Environment::empty();
        let x = Variable::unary("x");

        let matrix1 = BooleanMatrix::empty(Dimensions::new(2, 1));
        let matrix2 = BooleanMatrix::empty(Dimensions::new(3, 1));

        env.extend(x.clone(), matrix1.clone());
        let lookup1 = env.lookup(&x).unwrap();
        assert_eq!(lookup1.dimensions().capacity(), 2);

        // Shadow x with a different binding
        env.extend(x.clone(), matrix2.clone());
        let lookup2 = env.lookup(&x).unwrap();
        assert_eq!(lookup2.dimensions().capacity(), 3);

        // Pop should reveal the original binding
        env.pop();
        let lookup3 = env.lookup(&x).unwrap();
        assert_eq!(lookup3.dimensions().capacity(), 2);
    }

    #[test]
    fn test_lookup_mut() {
        let mut env = Environment::empty();
        let x = Variable::unary("x");

        let matrix = BooleanMatrix::empty(Dimensions::new(2, 1));
        env.extend(x.clone(), matrix);

        // Mutate the binding
        if let Some(m) = env.lookup_mut(&x) {
            *m = BooleanMatrix::empty(Dimensions::new(5, 1));
        }

        let lookup = env.lookup(&x).unwrap();
        assert_eq!(lookup.dimensions().capacity(), 5);
    }
}
