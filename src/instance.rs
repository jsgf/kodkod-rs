//! Instance types: Universe, Tuple, TupleSet, TupleFactory, Bounds, and Instance
//!
//! These types define the domain of discourse and bindings for relations.

use rustc_hash::FxHashMap;
use std::any::{Any, TypeId};
use std::collections::BTreeSet;
use std::fmt::{self, Debug};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use crate::ast::Relation;
use crate::error::{KodkodError, Result};

/// Index of an atom in a universe
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct AtomIndex(usize);

impl AtomIndex {
    /// Creates a new atom index (private to this module)
    fn new(index: usize) -> Self {
        Self(index)
    }

    /// Returns the raw index value (private to this module)
    fn get(self) -> usize {
        self.0
    }
}

/// Trait for atoms that can be stored in a Universe
///
/// Atoms must implement `Any` for downcasting and `Debug` for display.
/// They must also be comparable and hashable for universe indexing.
pub trait Atom: Any + Debug {
    /// Compare this atom with another for equality
    fn atom_eq(&self, other: &dyn Atom) -> bool;

    /// Compute the hash of this atom
    fn atom_hash(&self) -> u64;
}

// Convenience downcast helpers for common types (free functions, not trait methods)

/// Try to downcast an atom to String
pub fn atom_as_string(atom: &dyn Atom) -> Option<&String> {
    let any: &dyn Any = atom;
    any.downcast_ref::<String>()
}

/// Try to downcast an atom to &str (convenience wrapper around atom_as_string)
pub fn atom_as_str(atom: &dyn Atom) -> Option<&str> {
    atom_as_string(atom).map(|s| s.as_str())
}

/// Try to downcast an atom to i32
pub fn atom_as_i32(atom: &dyn Atom) -> Option<&i32> {
    let any: &dyn Any = atom;
    any.downcast_ref::<i32>()
}

/// Try to downcast an atom to usize
pub fn atom_as_usize(atom: &dyn Atom) -> Option<&usize> {
    let any: &dyn Any = atom;
    any.downcast_ref::<usize>()
}

/// Generic downcast for atoms
pub fn atom_downcast_ref<T: 'static>(atom: &dyn Atom) -> Option<&T> {
    let any: &dyn Any = atom;
    any.downcast_ref::<T>()
}

/// Blanket implementation for any type that is `Any + Debug + Eq + Hash`
impl<T: Any + Debug + Eq + Hash> Atom for T {
    fn atom_eq(&self, other: &dyn Atom) -> bool {
        // Upcast to Any for downcasting
        let other_any: &dyn Any = other;
        other_any
            .downcast_ref::<T>()
            .map_or(false, |other_t| self == other_t)
    }

    fn atom_hash(&self) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        let mut hasher = DefaultHasher::new();
        // Include type ID to distinguish between different types with same value
        TypeId::of::<T>().hash(&mut hasher);
        self.hash(&mut hasher);
        hasher.finish()
    }
}

/// Wrapper for using Atom trait objects as HashMap keys
#[derive(Clone)]
struct AtomKey(Rc<dyn Atom>);

impl Hash for AtomKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.atom_hash().hash(state);
    }
}

impl PartialEq for AtomKey {
    fn eq(&self, other: &Self) -> bool {
        self.0.atom_eq(&*other.0)
    }
}

impl Eq for AtomKey {}

impl Debug for AtomKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

/// An ordered set of unique atoms
///
/// A universe provides the domain for all tuples and relations in a problem.
/// Atoms are stored in a specific order which is used for indexing.
#[derive(Clone)]
pub struct Universe {
    inner: Rc<UniverseInner>,
}

struct UniverseInner {
    atoms: Vec<Rc<dyn Atom>>,
    indices: FxHashMap<AtomKey, AtomIndex>,
}

impl Universe {
    /// Creates a new universe from a slice of atom names (strings)
    ///
    /// This is a convenience method for creating universes with string atoms.
    ///
    /// # Errors
    /// Returns an error if the slice is empty or contains duplicates
    ///
    /// TODO: Switch API - make `new()` take `Vec<Rc<dyn Atom>>` and add `from_str()` for backward compat
    pub fn new(atoms: &[&str]) -> Result<Self> {
        let atom_objs: Vec<Rc<dyn Atom>> = atoms
            .iter()
            .map(|&s| Rc::new(s.to_string()) as Rc<dyn Atom>)
            .collect();
        Self::from_atoms(atom_objs)
    }

    /// Creates a new universe from a vector of atoms
    ///
    /// # Errors
    /// Returns an error if the vector is empty or contains duplicates
    pub fn from_atoms(atoms: Vec<Rc<dyn Atom>>) -> Result<Self> {
        if atoms.is_empty() {
            return Err(KodkodError::InvalidArgument(
                "Cannot create an empty universe".to_string(),
            ));
        }

        let mut indices = FxHashMap::default();

        for (i, atom) in atoms.iter().enumerate() {
            let key = AtomKey(Rc::clone(atom));
            if indices.contains_key(&key) {
                return Err(KodkodError::InvalidArgument(format!(
                    "{:?} appears multiple times",
                    atom
                )));
            }
            indices.insert(key, AtomIndex::new(i));
        }

        Ok(Self {
            inner: Rc::new(UniverseInner { atoms, indices }),
        })
    }

    /// Returns the number of atoms in this universe
    pub fn size(&self) -> usize {
        self.inner.atoms.len()
    }

    /// Returns a reference to the atom at the given index
    pub fn atom(&self, index: AtomIndex) -> Option<&dyn Atom> {
        self.inner.atoms.get(index.get()).map(|rc| &**rc as &dyn Atom)
    }

    /// Returns the index of the given atom
    pub(crate) fn index_of(&self, atom: &dyn Atom) -> Option<AtomIndex> {
        // Find by equality
        for (key, &idx) in &self.inner.indices {
            if atom.atom_eq(&*key.0) {
                return Some(idx);
            }
        }
        None
    }

    /// Returns true if this universe contains the given atom
    pub fn contains(&self, atom: &dyn Atom) -> bool {
        self.index_of(atom).is_some()
    }

    /// Returns an iterator over all atoms with their indices
    pub fn iter_atoms(&self) -> impl Iterator<Item = (AtomIndex, &dyn Atom)> + '_ {
        self.inner
            .atoms
            .iter()
            .enumerate()
            .map(|(i, rc)| (AtomIndex::new(i), &**rc as &dyn Atom))
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
        Rc::ptr_eq(&self.inner, &other.inner)
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
    atom_indices: Vec<AtomIndex>,
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

    /// Creates a tuple from a flat index
    /// Following Java pattern: reconstructing tuple from index
    ///
    /// The index represents the tuple in base-n enumeration where n is the universe size.
    /// For arity k, index = sum(atom[i] * base^(k-1-i) for i in 0..k)
    pub fn from_index(universe: Universe, arity: usize, index: usize) -> Self {
        let base = universe.size();
        let mut atom_indices = Vec::with_capacity(arity);
        let mut remaining = index;

        // Extract each position from MSB to LSB
        for i in 0..arity {
            let power = arity - 1 - i;
            let divisor = base.pow(power as u32);
            let atom_idx = remaining / divisor;
            atom_indices.push(AtomIndex::new(atom_idx));
            remaining %= divisor;
        }

        Tuple {
            universe,
            atom_indices,
            index,
        }
    }

    /// Returns the atom at the given position
    pub fn atom(&self, i: usize) -> Option<&dyn Atom> {
        self.atom_indices
            .get(i)
            .and_then(|&idx| self.universe.atom(idx))
    }

    /// Returns the index of the atom at position i
    pub(crate) fn atom_index(&self, i: usize) -> Option<AtomIndex> {
        self.atom_indices.get(i).copied()
    }

    /// Returns an iterator over the atoms in this tuple
    pub fn atoms(&self) -> impl Iterator<Item = &dyn Atom> + '_ {
        (0..self.arity()).filter_map(move |i| self.atom(i))
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
        Rc::as_ptr(&self.universe.inner).hash(state);
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

    /// Returns a set of the indices of all tuples in this set
    ///
    /// Used for symmetry detection. The indices represent positions
    /// in the n-dimensional tuple space of the universe.
    pub fn index_view(&self) -> BTreeSet<usize> {
        self.tuples.iter().map(|t| t.index()).collect()
    }

    /// Adds all tuples from another set to this set
    pub fn add_all(&mut self, other: &TupleSet) -> Result<()> {
        if other.universe() != &self.universe {
            return Err(KodkodError::InvalidArgument(
                "Tuple sets from different universes".to_string(),
            ));
        }
        if other.arity() != self.arity {
            return Err(KodkodError::InvalidArgument(format!(
                "Expected arity {}, got {}",
                self.arity,
                other.arity()
            )));
        }
        for tuple in &other.tuples {
            if !self.tuples.contains(tuple) {
                self.tuples.push(tuple.clone());
            }
        }
        Ok(())
    }

    /// Removes a tuple from this set
    /// Following Java: TupleSet.remove(Tuple)
    pub fn remove(&mut self, tuple: &Tuple) -> bool {
        if tuple.universe() != &self.universe || tuple.arity() != self.arity {
            return false;
        }
        if let Some(pos) = self.tuples.iter().position(|t| t == tuple) {
            self.tuples.remove(pos);
            true
        } else {
            false
        }
    }

    /// Returns a new tuple set containing tuples in this set but not in other
    /// Following Java: Set difference operation
    pub fn difference(&self, other: &TupleSet) -> Result<TupleSet> {
        if other.universe() != &self.universe {
            return Err(KodkodError::InvalidArgument(
                "Tuple sets from different universes".to_string(),
            ));
        }
        if other.arity() != self.arity {
            return Err(KodkodError::InvalidArgument(format!(
                "Expected arity {}, got {}",
                self.arity,
                other.arity()
            )));
        }

        let mut result = TupleSet::empty(self.universe.clone(), self.arity);
        for tuple in &self.tuples {
            if !other.tuples.contains(tuple) {
                result.tuples.push(tuple.clone());
            }
        }
        Ok(result)
    }

    /// Returns the Cartesian product of this set with another
    pub fn product(&self, other: &TupleSet) -> Result<TupleSet> {
        if other.universe() != &self.universe {
            return Err(KodkodError::InvalidArgument(
                "Tuple sets from different universes".to_string(),
            ));
        }

        let new_arity = self.arity + other.arity;
        let mut result = TupleSet::empty(self.universe.clone(), new_arity);

        for t1 in &self.tuples {
            for t2 in &other.tuples {
                let mut atoms = Vec::with_capacity(new_arity);
                atoms.extend_from_slice(&t1.atom_indices);
                atoms.extend_from_slice(&t2.atom_indices);

                // Calculate new index
                let base = self.universe.size();
                let mut index = 0;
                for (i, &atom_idx) in atoms.iter().enumerate() {
                    index += atom_idx.get() * base.pow((new_arity - 1 - i) as u32);
                }

                let product_tuple = Tuple {
                    universe: self.universe.clone(),
                    atom_indices: atoms,
                    index,
                };
                result.tuples.push(product_tuple);
            }
        }

        Ok(result)
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

    /// Creates a tuple from the given string atoms
    ///
    /// This is a convenience method for working with string-based universes.
    pub fn tuple(&self, atoms: &[&str]) -> Result<Tuple> {
        if atoms.is_empty() {
            return Err(KodkodError::InvalidArgument(
                "Cannot create empty tuple".to_string(),
            ));
        }

        let mut atom_indices = Vec::with_capacity(atoms.len());
        for &atom_str in atoms {
            // Need to find the index by comparing with universe atoms
            let mut found_idx = None;
            for (idx, universe_atom) in self.universe.inner.atoms.iter().enumerate() {
                // Try to downcast to String to compare with str
                if let Some(s) = atom_as_string(&**universe_atom) {
                    if s == atom_str {
                        found_idx = Some(AtomIndex::new(idx));
                        break;
                    }
                }
            }
            let idx = found_idx.ok_or_else(|| {
                KodkodError::InvalidArgument(format!("Atom {} not in universe", atom_str))
            })?;
            atom_indices.push(idx);
        }

        // Calculate index in n-dimensional space
        let base = self.universe.size();
        let mut index = 0;
        for (i, &atom_idx) in atom_indices.iter().enumerate() {
            index += atom_idx.get() * base.pow((atoms.len() - 1 - i) as u32);
        }

        Ok(Tuple {
            universe: self.universe.clone(),
            atom_indices,
            index,
        })
    }

    /// Creates a tuple from atom values by searching for them in the universe
    ///
    /// This is more flexible than `tuple()` as it works with any Atom type.
    pub fn tuple_from_atoms(&self, atoms: &[&dyn Atom]) -> Result<Tuple> {
        if atoms.is_empty() {
            return Err(KodkodError::InvalidArgument(
                "Cannot create empty tuple".to_string(),
            ));
        }

        let mut atom_indices = Vec::with_capacity(atoms.len());
        for &atom in atoms {
            let idx = self.universe.index_of(atom).ok_or_else(|| {
                KodkodError::InvalidArgument(format!("Atom {:?} not in universe", atom))
            })?;
            atom_indices.push(idx);
        }

        // Calculate index in n-dimensional space
        let base = self.universe.size();
        let mut index = 0;
        for (i, &atom_idx) in atom_indices.iter().enumerate() {
            index += atom_idx.get() * base.pow((atoms.len() - 1 - i) as u32);
        }

        Ok(Tuple {
            universe: self.universe.clone(),
            atom_indices,
            index,
        })
    }

    /// Creates a tuple from atom indices
    ///
    /// This is useful when you already know the indices of atoms in the universe.
    fn tuple_from_atom_indices(&self, indices: Vec<AtomIndex>) -> Result<Tuple> {
        if indices.is_empty() {
            return Err(KodkodError::InvalidArgument(
                "Cannot create empty tuple".to_string(),
            ));
        }

        for &idx in &indices {
            if idx.get() >= self.universe.size() {
                return Err(KodkodError::InvalidArgument(format!(
                    "Index {} out of bounds for universe of size {}",
                    idx.get(),
                    self.universe.size()
                )));
            }
        }

        // Calculate index in n-dimensional space
        let base = self.universe.size();
        let mut index = 0;
        for (i, &atom_idx) in indices.iter().enumerate() {
            index += atom_idx.get() * base.pow((indices.len() - 1 - i) as u32);
        }

        Ok(Tuple {
            universe: self.universe.clone(),
            atom_indices: indices,
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

    /// Creates a tuple set containing all tuples from start to end (inclusive)
    pub fn range(&self, start: Tuple, end: Tuple) -> Result<TupleSet> {
        if start.arity() != end.arity() {
            return Err(KodkodError::InvalidArgument(
                "Start and end tuples must have the same arity".to_string(),
            ));
        }

        let arity = start.arity();
        let mut set = TupleSet::empty(self.universe.clone(), arity);

        let start_index = start.index;
        let end_index = end.index;

        if start_index > end_index {
            return Err(KodkodError::InvalidArgument(
                "Start index must be <= end index".to_string(),
            ));
        }

        for i in start_index..=end_index {
            if let Ok(tuple) = self.tuple_from_index(arity, i) {
                let _ = set.add(tuple);
            }
        }

        Ok(set)
    }

    /// Creates a singleton tuple set containing a single atom
    /// Helper method for convenience
    pub fn set_of_atom(&self, atom: &str) -> Result<TupleSet> {
        let tuple = self.tuple(&[atom])?;
        let mut set = TupleSet::empty(self.universe.clone(), 1);
        set.add(tuple)?;
        Ok(set)
    }

    /// Creates a tuple set from flat tuple indices
    /// Following Java: TupleFactory.setOf(int arity, IntSet tupleIndices)
    ///
    /// Each index represents a tuple in the standard enumeration order
    pub fn set_of(&self, arity: usize, indices: &[usize]) -> TupleSet {
        let mut set = TupleSet::empty(self.universe.clone(), arity);
        for &index in indices {
            let tuple = Tuple::from_index(self.universe.clone(), arity, index);
            set.add(tuple).expect("Tuple from valid index should be valid");
        }
        set
    }

    /// Creates an n-dimensional rectangular region
    /// Following Java: TupleFactory.area(Tuple, Tuple)
    ///
    /// Returns the Cartesian product of ranges [upperLeft[i]..lowerRight[i]] for each dimension i
    pub fn area(&self, upper_left: Tuple, lower_right: Tuple) -> Result<TupleSet> {
        if upper_left.universe() != &self.universe || lower_right.universe() != &self.universe {
            return Err(KodkodError::InvalidArgument(
                "tuples must be from this universe".to_string(),
            ));
        }
        if upper_left.arity() != lower_right.arity() {
            return Err(KodkodError::InvalidArgument(
                "tuples must have the same arity".to_string(),
            ));
        }

        // Start with the first dimension's range
        let start_idx = upper_left.atom_index(0).unwrap();
        let end_idx = lower_right.atom_index(0).unwrap();

        let start_tuple = self.tuple_from_atom_indices(vec![start_idx])?;
        let end_tuple = self.tuple_from_atom_indices(vec![end_idx])?;
        let mut result = self.range(start_tuple, end_tuple)?;

        // Product with each subsequent dimension's range
        for i in 1..upper_left.arity() {
            let start_idx = upper_left.atom_index(i).unwrap();
            let end_idx = lower_right.atom_index(i).unwrap();

            let start_tuple = self.tuple_from_atom_indices(vec![start_idx])?;
            let end_tuple = self.tuple_from_atom_indices(vec![end_idx])?;
            let dim_range = self.range(start_tuple, end_tuple)?;

            result = result.product(&dim_range)?;
        }

        Ok(result)
    }

    /// Creates a tuple from an index in n-dimensional space
    pub fn tuple_from_index(&self, arity: usize, index: usize) -> Result<Tuple> {
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

        // Extract atoms in row-major order (first atom is most significant)
        // This must match the calculation in tuple()
        for pos in (0..arity).rev() {
            let divisor = base.pow(pos as u32);
            let atom_idx = remaining / divisor;
            atom_indices.push(AtomIndex::new(atom_idx));
            remaining %= divisor;
        }

        // Don't reverse - we built them in the correct order

        Ok(Tuple {
            universe: self.universe.clone(),
            atom_indices,
            index,
        })
    }

    /// Creates a TupleSet from a set of tuple indices
    /// Following Java: TupleFactory.setOf(arity, IntSet)
    pub fn tuple_set_from_indices(&self, arity: usize, indices: &std::collections::BTreeSet<usize>) -> Result<TupleSet> {
        let mut set = TupleSet::empty(self.universe.clone(), arity);
        for &index in indices {
            let tuple = self.tuple_from_index(arity, index)?;
            set.add(tuple)?;
        }
        Ok(set)
    }
}

/// Bounds map relations to lower and upper bounds on their contents
///
/// The lower bound specifies tuples that must be in the relation,
/// while the upper bound specifies tuples that may be in the relation.
#[derive(Clone)]
pub struct Bounds {
    universe: Universe,
    lower_bounds: FxHashMap<Relation, TupleSet>,
    upper_bounds: FxHashMap<Relation, TupleSet>,
    int_bounds: FxHashMap<i32, TupleSet>,
}

impl Bounds {
    /// Creates new bounds over the given universe
    pub fn new(universe: Universe) -> Self {
        Self {
            universe,
            lower_bounds: FxHashMap::default(),
            upper_bounds: FxHashMap::default(),
            int_bounds: FxHashMap::default(),
        }
    }

    /// Returns the universe
    pub fn universe(&self) -> &Universe {
        &self.universe
    }

    /// Returns the tuple factory for this bounds
    pub fn factory(&self) -> TupleFactory {
        self.universe.factory()
    }

    /// Sets both lower and upper bounds for a relation
    pub fn bound(&mut self, relation: &Relation, lower: TupleSet, upper: TupleSet) -> Result<()> {
        // Validate that bounds are compatible
        if lower.universe() != &self.universe || upper.universe() != &self.universe {
            return Err(KodkodError::InvalidArgument(
                "Tuple sets must be from the same universe".to_string(),
            ));
        }

        if lower.arity() != relation.arity() || upper.arity() != relation.arity() {
            return Err(KodkodError::InvalidArgument(format!(
                "Tuple set arity {} does not match relation arity {}",
                lower.arity(),
                relation.arity()
            )));
        }

        self.lower_bounds.insert(relation.clone(), lower);
        self.upper_bounds.insert(relation.clone(), upper);
        Ok(())
    }

    /// Sets exact bound for a relation (lower == upper)
    pub fn bound_exactly(&mut self, relation: &Relation, tuples: TupleSet) -> Result<()> {
        let upper = tuples.clone();
        self.bound(relation, tuples, upper)
    }

    /// Returns the lower bound for a relation
    pub fn lower_bound(&self, relation: &Relation) -> Option<&TupleSet> {
        self.lower_bounds.get(relation)
    }

    /// Returns the upper bound for a relation
    pub fn upper_bound(&self, relation: &Relation) -> Option<&TupleSet> {
        self.upper_bounds.get(relation)
    }

    /// Returns all relations with bounds
    pub fn relations(&self) -> impl Iterator<Item = &Relation> {
        self.upper_bounds.keys()
    }

    /// Sets integer bounds (min and max)
    pub fn bound_int(&mut self, min: i32, max: i32) {
        // Store integer atoms for the bounded range
        for i in min..=max {
            if let Ok(tuple) = self.universe.factory().tuple(&[&i.to_string()]) {
                let mut set = TupleSet::empty(self.universe.clone(), 1);
                let _ = set.add(tuple);
                self.int_bounds.insert(i, set);
            }
        }
    }

    /// Sets the exact bound for an integer
    /// Following Java: Bounds.boundExactly(int i, TupleSet ibound)
    pub fn bound_exactly_int(&mut self, i: i32, tuples: TupleSet) -> Result<()> {
        if tuples.universe() != &self.universe {
            return Err(KodkodError::InvalidArgument(
                "Tuple set must be from the same universe".to_string(),
            ));
        }
        if tuples.arity() != 1 {
            return Err(KodkodError::InvalidArgument(
                "Integer bound must have arity 1".to_string(),
            ));
        }
        if tuples.size() != 1 {
            return Err(KodkodError::InvalidArgument(
                "Integer bound must contain exactly one tuple".to_string(),
            ));
        }
        self.int_bounds.insert(i, tuples);
        Ok(())
    }

    /// Returns the tuple set for an integer
    pub fn int_bound(&self, i: i32) -> Option<&TupleSet> {
        self.int_bounds.get(&i)
    }

    /// Returns the min and max integers if integer bounds are set
    pub fn ints(&self) -> Option<(i32, i32)> {
        if self.int_bounds.is_empty() {
            return None;
        }
        let min = *self.int_bounds.keys().min()?;
        let max = *self.int_bounds.keys().max()?;
        Some((min, max))
    }

    /// Returns an iterator over all integers with bounds
    pub fn int_keys(&self) -> impl Iterator<Item = i32> + '_ {
        self.int_bounds.keys().copied()
    }

    /// Returns the exact bound for an integer (for symmetry detection)
    pub fn exact_int_bound(&self, i: i32) -> Option<&TupleSet> {
        self.int_bounds.get(&i)
    }
}

/// An instance maps relations to tuple sets (a solution)
#[derive(Debug)]
pub struct Instance {
    universe: Universe,
    relations: FxHashMap<Relation, TupleSet>,
}

impl Instance {
    /// Creates a new empty instance
    pub fn new(universe: Universe) -> Self {
        Self {
            universe,
            relations: FxHashMap::default(),
        }
    }

    /// Returns the universe
    pub fn universe(&self) -> &Universe {
        &self.universe
    }

    /// Adds a relation binding
    pub fn add(&mut self, relation: Relation, tuples: TupleSet) -> Result<()> {
        if tuples.universe() != &self.universe {
            return Err(KodkodError::InvalidArgument(
                "Tuple set from different universe".to_string(),
            ));
        }

        if tuples.arity() != relation.arity() {
            return Err(KodkodError::InvalidArgument(format!(
                "Tuple set arity {} does not match relation arity {}",
                tuples.arity(),
                relation.arity()
            )));
        }

        self.relations.insert(relation, tuples);
        Ok(())
    }

    /// Returns the tuples for a relation
    pub fn tuples(&self, relation: &Relation) -> Option<&TupleSet> {
        self.relations.get(relation)
    }

    /// Gets the tuple set for a relation (alias for tuples)
    pub fn get(&self, relation: &Relation) -> Option<&TupleSet> {
        self.relations.get(relation)
    }

    /// Returns all relations in this instance
    pub fn relations(&self) -> impl Iterator<Item = &Relation> {
        self.relations.keys()
    }

    /// Returns the relation-to-tupleset mappings
    /// Following Java: Instance.relationTuples()
    pub fn relation_tuples(&self) -> &FxHashMap<Relation, TupleSet> {
        &self.relations
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn create_universe() -> Result<()> {
        let universe = Universe::new(&["A", "B", "C"])?;
        assert_eq!(universe.size(), 3);

        // Test iter_atoms helper
        let atoms: Vec<_> = universe
            .iter_atoms()
            .map(|(_, atom)| atom_as_string(atom).unwrap().as_str())
            .collect();
        assert_eq!(atoms, vec!["A", "B", "C"]);

        // Can check via contains
        assert!(universe.contains(&"A".to_string() as &dyn Atom));
        assert!(universe.contains(&"B".to_string() as &dyn Atom));
        assert!(!universe.contains(&"D".to_string() as &dyn Atom));
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
        assert_eq!(atom_as_string(tuple.atom(0).unwrap()).unwrap(), "A");

        let tuple2 = factory.tuple(&["B", "C"])?;
        assert_eq!(tuple2.arity(), 2);
        assert_eq!(atom_as_string(tuple2.atom(0).unwrap()).unwrap(), "B");
        assert_eq!(atom_as_string(tuple2.atom(1).unwrap()).unwrap(), "C");

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

    #[test]
    fn bounds_basic() -> Result<()> {
        use crate::ast::Relation;

        let universe = Universe::new(&["A", "B", "C"])?;
        let mut bounds = Bounds::new(universe.clone());

        let person = Relation::unary("Person");
        let factory = universe.factory();

        let lower = factory.tuple_set(&[&["A"]])?;
        let upper = factory.tuple_set(&[&["A"], &["B"], &["C"]])?;

        bounds.bound(&person, lower, upper)?;

        assert!(bounds.lower_bound(&person).is_some());
        assert!(bounds.upper_bound(&person).is_some());

        Ok(())
    }

    #[test]
    fn bounds_exact() -> Result<()> {
        use crate::ast::Relation;

        let universe = Universe::new(&["A", "B"])?;
        let mut bounds = Bounds::new(universe.clone());

        let r = Relation::unary("R");
        let factory = universe.factory();
        let exact = factory.tuple_set(&[&["A"]])?;

        bounds.bound_exactly(&r, exact)?;

        let lower = bounds.lower_bound(&r).unwrap();
        let upper = bounds.upper_bound(&r).unwrap();

        assert_eq!(lower.size(), 1);
        assert_eq!(upper.size(), 1);

        Ok(())
    }

    #[test]
    fn bounds_integers() -> Result<()> {
        let universe = Universe::new(&["-1", "0", "1", "2"])?;
        let mut bounds = Bounds::new(universe);

        bounds.bound_int(-1, 2);

        assert_eq!(bounds.ints(), Some((-1, 2)));
        assert!(bounds.int_bound(0).is_some());
        assert!(bounds.int_bound(3).is_none());

        Ok(())
    }

    #[test]
    fn instance_basic() -> Result<()> {
        use crate::ast::Relation;

        let universe = Universe::new(&["A", "B"])?;
        let mut instance = Instance::new(universe.clone());

        let person = Relation::unary("Person");
        let factory = universe.factory();
        let tuples = factory.tuple_set(&[&["A"], &["B"]])?;

        instance.add(person.clone(), tuples)?;

        let result = instance.tuples(&person);
        assert!(result.is_some());
        assert_eq!(result.unwrap().size(), 2);

        Ok(())
    }

    #[test]
    fn tuple_from_index_unary() -> Result<()> {
        let universe = Universe::new(&["A", "B", "C"])?;

        // For unary tuples:
        // Index 0 = (A), index 1 = (B), index 2 = (C)
        let t0 = Tuple::from_index(universe.clone(), 1, 0);
        assert_eq!(t0.arity(), 1);
        assert_eq!(t0.index(), 0);
        assert_eq!(atom_as_string(t0.atom(0).unwrap()).unwrap(), "A");

        let t1 = Tuple::from_index(universe.clone(), 1, 1);
        assert_eq!(atom_as_string(t1.atom(0).unwrap()).unwrap(), "B");

        let t2 = Tuple::from_index(universe.clone(), 1, 2);
        assert_eq!(atom_as_string(t2.atom(0).unwrap()).unwrap(), "C");

        Ok(())
    }

    #[test]
    fn tuple_from_index_binary() -> Result<()> {
        let universe = Universe::new(&["A", "B", "C"])?;

        // For binary tuples with 3-atom universe:
        // Index 0 = (A,A), 1 = (A,B), 2 = (A,C), 3 = (B,A), 4 = (B,B), ...
        let t0 = Tuple::from_index(universe.clone(), 2, 0);
        assert_eq!(t0.arity(), 2);
        assert_eq!(t0.index(), 0);
        assert_eq!(atom_as_string(t0.atom(0).unwrap()).unwrap(), "A");
        assert_eq!(atom_as_string(t0.atom(1).unwrap()).unwrap(), "A");

        let t1 = Tuple::from_index(universe.clone(), 2, 1);
        assert_eq!(atom_as_string(t1.atom(0).unwrap()).unwrap(), "A");
        assert_eq!(atom_as_string(t1.atom(1).unwrap()).unwrap(), "B");

        let t4 = Tuple::from_index(universe.clone(), 2, 4);
        assert_eq!(atom_as_string(t4.atom(0).unwrap()).unwrap(), "B");
        assert_eq!(atom_as_string(t4.atom(1).unwrap()).unwrap(), "B");

        Ok(())
    }

    #[test]
    fn tuple_from_index_roundtrip() -> Result<()> {
        let universe = Universe::new(&["A", "B"])?;
        let factory = universe.factory();

        // Create a tuple normally and verify from_index reconstructs it
        let original = factory.tuple(&["B", "A"])?;
        let index = original.index();

        let reconstructed = Tuple::from_index(universe.clone(), 2, index);

        assert_eq!(reconstructed.arity(), original.arity());
        assert_eq!(reconstructed.index(), original.index());
        // Compare atoms via their hash/equality
        assert_eq!(
            atom_as_string(reconstructed.atom(0).unwrap()).unwrap(),
            atom_as_string(original.atom(0).unwrap()).unwrap()
        );
        assert_eq!(
            atom_as_string(reconstructed.atom(1).unwrap()).unwrap(),
            atom_as_string(original.atom(1).unwrap()).unwrap()
        );

        Ok(())
    }

    #[test]
    fn factory_set_of_from_indices() -> Result<()> {
        let universe = Universe::new(&["A", "B", "C"])?;
        let factory = universe.factory();

        // Create a set from indices: 0=(A), 2=(C)
        let set = factory.set_of(1, &[0, 2]);

        assert_eq!(set.arity(), 1);
        assert_eq!(set.size(), 2);

        let atoms: Vec<_> = set
            .iter()
            .map(|t| atom_as_string(t.atom(0).unwrap()).unwrap().clone())
            .collect();
        assert!(atoms.contains(&"A".to_string()));
        assert!(atoms.contains(&"C".to_string()));

        Ok(())
    }

    #[test]
    fn factory_set_of_binary_from_indices() -> Result<()> {
        let universe = Universe::new(&["A", "B"])?;
        let factory = universe.factory();

        // For 2-atom universe, binary tuples:
        // Index 0 = (A,A), 1 = (A,B), 2 = (B,A), 3 = (B,B)
        let set = factory.set_of(2, &[1, 2]);

        assert_eq!(set.arity(), 2);
        assert_eq!(set.size(), 2);

        let mut found_ab = false;
        let mut found_ba = false;
        for tuple in set.iter() {
            let a0 = atom_as_string(tuple.atom(0).unwrap()).unwrap();
            let a1 = atom_as_string(tuple.atom(1).unwrap()).unwrap();
            if a0 == "A" && a1 == "B" {
                found_ab = true;
            }
            if a0 == "B" && a1 == "A" {
                found_ba = true;
            }
        }
        assert!(found_ab);
        assert!(found_ba);

        Ok(())
    }

    #[test]
    fn factory_set_of_empty_indices() -> Result<()> {
        let universe = Universe::new(&["A", "B"])?;
        let factory = universe.factory();

        let set = factory.set_of(1, &[]);
        assert_eq!(set.size(), 0);
        assert!(set.is_empty());

        Ok(())
    }
}
