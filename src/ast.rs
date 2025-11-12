//! AST types for relational logic formulas
//!
//! This module contains the types that make up Kodkod's abstract syntax tree.

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
}
