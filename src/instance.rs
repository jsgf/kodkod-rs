//! Instance types: Universe, Tuple, TupleSet, and TupleFactory
//!
//! These types define the domain of discourse and bindings for relations.

use std::collections::HashMap;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use crate::error::{KodkodError, Result};

/// An ordered set of unique atoms
///
/// A universe provides the domain for all tuples and relations in a problem.
/// Atoms are stored in a specific order which is used for indexing.
#[derive(Clone)]
pub struct Universe {
    inner: Arc<UniverseInner>,
}

struct UniverseInner {
    atoms: Vec<String>,
    indices: HashMap<String, usize>,
}

impl Universe {
    /// Creates a new universe from a slice of atom names
    ///
    /// # Errors
    /// Returns an error if the slice is empty or contains duplicates
    pub fn new(atoms: &[&str]) -> Result<Self> {
        if atoms.is_empty() {
            return Err(KodkodError::InvalidArgument(
                "Cannot create an empty universe".to_string(),
            ));
        }

        let mut atom_vec = Vec::with_capacity(atoms.len());
        let mut indices = HashMap::new();

        for (i, &atom) in atoms.iter().enumerate() {
            let atom_string = atom.to_string();
            if indices.contains_key(&atom_string) {
                return Err(KodkodError::InvalidArgument(format!(
                    "{} appears multiple times",
                    atom
                )));
            }
            indices.insert(atom_string.clone(), i);
            atom_vec.push(atom_string);
        }

        Ok(Self {
            inner: Arc::new(UniverseInner {
                atoms: atom_vec,
                indices,
            }),
        })
    }

    /// Returns the number of atoms in this universe
    pub fn size(&self) -> usize {
        self.inner.atoms.len()
    }

    /// Returns the atom at the given index
    pub fn atom(&self, index: usize) -> Option<&str> {
        self.inner.atoms.get(index).map(|s| s.as_str())
    }

    /// Returns the index of the given atom
    pub fn index_of(&self, atom: &str) -> Option<usize> {
        self.inner.indices.get(atom).copied()
    }

    /// Returns true if this universe contains the given atom
    pub fn contains(&self, atom: &str) -> bool {
        self.inner.indices.contains_key(atom)
    }

    /// Returns a factory for creating tuples from this universe
    pub fn factory(&self) -> TupleFactory {
        TupleFactory {
            universe: self.clone(),
        }
    }
}

impl PartialEq for Universe {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.inner, &other.inner)
    }
}

impl Eq for Universe {}

impl fmt::Debug for Universe {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Universe({:?})", self.inner.atoms)
    }
}

/// A tuple of atoms from a universe
#[derive(Clone, Debug)]
pub struct Tuple {
    universe: Universe,
    atom_indices: Vec<usize>,
    index: usize,
}

impl Tuple {
    /// Returns the universe this tuple belongs to
    pub fn universe(&self) -> &Universe {
        &self.universe
    }

    /// Returns the arity (number of atoms) in this tuple
    pub fn arity(&self) -> usize {
        self.atom_indices.len()
    }

    /// Returns the index of this tuple in n-dimensional space
    pub fn index(&self) -> usize {
        self.index
    }

    /// Returns the atom at the given position
    pub fn atom(&self, i: usize) -> Option<&str> {
        self.atom_indices
            .get(i)
            .and_then(|&idx| self.universe.atom(idx))
    }

    /// Returns the index of the atom at position i
    pub fn atom_index(&self, i: usize) -> Option<usize> {
        self.atom_indices.get(i).copied()
    }
}

impl PartialEq for Tuple {
    fn eq(&self, other: &Self) -> bool {
        self.universe == other.universe
            && self.arity() == other.arity()
            && self.index == other.index
    }
}

impl Eq for Tuple {}

impl Hash for Tuple {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.arity().hash(state);
        self.index.hash(state);
        Arc::as_ptr(&self.universe.inner).hash(state);
    }
}

/// A set of tuples all of the same arity from the same universe
#[derive(Clone, Debug)]
pub struct TupleSet {
    universe: Universe,
    arity: usize,
    tuples: Vec<Tuple>,
}

impl TupleSet {
    /// Creates an empty tuple set with the given arity
    pub fn empty(universe: Universe, arity: usize) -> Self {
        Self {
            universe,
            arity,
            tuples: Vec::new(),
        }
    }

    /// Returns the universe this tuple set belongs to
    pub fn universe(&self) -> &Universe {
        &self.universe
    }

    /// Returns the arity of tuples in this set
    pub fn arity(&self) -> usize {
        self.arity
    }

    /// Returns the number of tuples in this set
    pub fn size(&self) -> usize {
        self.tuples.len()
    }

    /// Returns true if this set is empty
    pub fn is_empty(&self) -> bool {
        self.tuples.is_empty()
    }

    /// Adds a tuple to this set
    pub fn add(&mut self, tuple: Tuple) -> Result<()> {
        if tuple.universe() != &self.universe {
            return Err(KodkodError::InvalidArgument(
                "Tuple from different universe".to_string(),
            ));
        }
        if tuple.arity() != self.arity {
            return Err(KodkodError::InvalidArgument(format!(
                "Expected arity {}, got {}",
                self.arity,
                tuple.arity()
            )));
        }
        if !self.tuples.contains(&tuple) {
            self.tuples.push(tuple);
        }
        Ok(())
    }

    /// Returns an iterator over the tuples in this set
    pub fn iter(&self) -> impl Iterator<Item = &Tuple> {
        self.tuples.iter()
    }
}

/// Factory for creating tuples and tuple sets
pub struct TupleFactory {
    universe: Universe,
}

impl TupleFactory {
    /// Returns the universe this factory belongs to
    pub fn universe(&self) -> &Universe {
        &self.universe
    }

    /// Creates a tuple from the given atoms
    pub fn tuple(&self, atoms: &[&str]) -> Result<Tuple> {
        if atoms.is_empty() {
            return Err(KodkodError::InvalidArgument(
                "Cannot create empty tuple".to_string(),
            ));
        }

        let mut atom_indices = Vec::with_capacity(atoms.len());
        for &atom in atoms {
            let idx = self.universe.index_of(atom).ok_or_else(|| {
                KodkodError::InvalidArgument(format!("Atom {} not in universe", atom))
            })?;
            atom_indices.push(idx);
        }

        // Calculate index in n-dimensional space
        let base = self.universe.size();
        let mut index = 0;
        for (i, &atom_idx) in atom_indices.iter().enumerate() {
            index += atom_idx * base.pow((atoms.len() - 1 - i) as u32);
        }

        Ok(Tuple {
            universe: self.universe.clone(),
            atom_indices,
            index,
        })
    }

    /// Creates a tuple set from an array of atom sequences
    pub fn tuple_set(&self, tuples: &[&[&str]]) -> Result<TupleSet> {
        if tuples.is_empty() {
            return Err(KodkodError::InvalidArgument(
                "Cannot create tuple set from empty array".to_string(),
            ));
        }

        let arity = tuples[0].len();
        let mut set = TupleSet::empty(self.universe.clone(), arity);

        for &atoms in tuples {
            if atoms.len() != arity {
                return Err(KodkodError::InvalidArgument(
                    "All tuples must have the same arity".to_string(),
                ));
            }
            let tuple = self.tuple(atoms)?;
            set.add(tuple)?;
        }

        Ok(set)
    }

    /// Creates an empty tuple set with the given arity
    pub fn none(&self, arity: usize) -> TupleSet {
        TupleSet::empty(self.universe.clone(), arity)
    }

    /// Creates a tuple set containing all tuples of the given arity
    pub fn all(&self, arity: usize) -> TupleSet {
        let mut set = TupleSet::empty(self.universe.clone(), arity);
        let total = self.universe.size().pow(arity as u32);

        for i in 0..total {
            if let Ok(tuple) = self.tuple_from_index(arity, i) {
                let _ = set.add(tuple);
            }
        }

        set
    }

    /// Creates a tuple from an index in n-dimensional space
    fn tuple_from_index(&self, arity: usize, index: usize) -> Result<Tuple> {
        let base = self.universe.size();
        let max_index = base.pow(arity as u32);

        if index >= max_index {
            return Err(KodkodError::InvalidArgument(format!(
                "Index {} out of range for arity {}",
                index, arity
            )));
        }

        let mut atom_indices = Vec::with_capacity(arity);
        let mut remaining = index;

        for pos in (0..arity).rev() {
            let divisor = base.pow(pos as u32);
            let atom_idx = remaining / divisor;
            atom_indices.push(atom_idx);
            remaining %= divisor;
        }

        atom_indices.reverse();

        Ok(Tuple {
            universe: self.universe.clone(),
            atom_indices,
            index,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn create_universe() -> Result<()> {
        let universe = Universe::new(&["A", "B", "C"])?;
        assert_eq!(universe.size(), 3);
        assert_eq!(universe.atom(0), Some("A"));
        assert_eq!(universe.atom(1), Some("B"));
        assert_eq!(universe.atom(2), Some("C"));
        assert_eq!(universe.index_of("B"), Some(1));
        assert!(universe.contains("A"));
        assert!(!universe.contains("D"));
        Ok(())
    }

    #[test]
    fn universe_rejects_duplicates() {
        let result = Universe::new(&["A", "B", "A"]);
        assert!(result.is_err());
    }

    #[test]
    fn universe_rejects_empty() {
        let result = Universe::new(&[]);
        assert!(result.is_err());
    }

    #[test]
    fn create_tuple() -> Result<()> {
        let universe = Universe::new(&["A", "B", "C"])?;
        let factory = universe.factory();

        let tuple = factory.tuple(&["A"])?;
        assert_eq!(tuple.arity(), 1);
        assert_eq!(tuple.atom(0), Some("A"));

        let tuple2 = factory.tuple(&["B", "C"])?;
        assert_eq!(tuple2.arity(), 2);
        assert_eq!(tuple2.atom(0), Some("B"));
        assert_eq!(tuple2.atom(1), Some("C"));

        Ok(())
    }

    #[test]
    fn tuple_rejects_invalid_atom() {
        let universe = Universe::new(&["A", "B"]).unwrap();
        let factory = universe.factory();

        let result = factory.tuple(&["X"]);
        assert!(result.is_err());
    }

    #[test]
    fn create_tuple_set() -> Result<()> {
        let universe = Universe::new(&["A", "B", "C"])?;
        let factory = universe.factory();

        let set = factory.tuple_set(&[&["A"], &["B"]])?;
        assert_eq!(set.arity(), 1);
        assert_eq!(set.size(), 2);

        Ok(())
    }

    #[test]
    fn create_empty_and_full_sets() -> Result<()> {
        let universe = Universe::new(&["A", "B"])?;
        let factory = universe.factory();

        let empty = factory.none(1);
        assert_eq!(empty.size(), 0);
        assert!(empty.is_empty());

        let all = factory.all(1);
        assert_eq!(all.size(), 2); // {A}, {B}

        let all2 = factory.all(2);
        assert_eq!(all2.size(), 4); // {A,A}, {A,B}, {B,A}, {B,B}

        Ok(())
    }
}
