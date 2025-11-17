//! Symmetry detection for bounds
//!
//! Partitions a universe into equivalence classes based on the bounding constraints.
//! Given a Bounds object, computes the coarsest partition of the universe such that
//! every tupleset can be expressed as a union of cross-products of sets from the partition.

use std::collections::{BTreeSet, HashMap};
use crate::instance::Bounds;

/// Type alias for IntSet (ordered set of atom indices)
pub type IntSet = BTreeSet<usize>;

/// Symmetry detector for partitioning universe atoms
pub struct SymmetryDetector {
    /// The bounds being analyzed
    bounds: Bounds,
    /// Partitions of the universe (invariant: always holds a partition of bounds.universe)
    parts: Vec<IntSet>,
    /// Universe size
    usize: usize,
}

impl SymmetryDetector {
    /// Constructs a new SymmetryDetector for the given bounds
    fn new(bounds: Bounds) -> Self {
        let usize = bounds.universe().size();

        // Start with the maximum partition -- the whole universe
        let mut set = IntSet::new();
        for i in 0..usize {
            set.insert(i);
        }

        Self {
            bounds,
            parts: vec![set],
            usize,
        }
    }

    /// Returns the coarsest sound partition of the universe into symmetry classes
    ///
    /// The returned set of IntSets partitions the universe such that:
    /// - All IntSets are disjoint and non-empty
    /// - Their union covers all atoms
    /// - Every tupleset in bounds can be expressed as a union of cross-products
    ///   from the partition
    pub fn partition(bounds: Bounds) -> Vec<IntSet> {
        let mut detector = SymmetryDetector::new(bounds);
        detector.compute_partitions();
        detector.parts
    }

    /// Partitions the universe into sets of equivalent atoms
    fn compute_partitions(&mut self) {
        if self.usize == 1 {
            return; // nothing more to do
        }

        let mut range2domain: HashMap<IntSet, IntSet> = HashMap::new();

        // Refine the partitions based on the bounds for each integer
        // Collect keys first to avoid borrowing issues
        let int_keys: Vec<i32> = self.bounds.int_keys().collect();
        for i in int_keys {
            if let Some(exact) = self.bounds.exact_int_bound(i) {
                let index_view = exact.index_view();
                self.refine_partitions_simple(&index_view);
            }
        }

        // Refine the partitions based on the upper/lower bounds for each relation
        let sorted_sets = self.sort_bounds();
        for (index_view, arity) in sorted_sets {
            if self.parts.len() == self.usize {
                return;
            }
            self.refine_partitions_multi(&index_view, arity, &mut range2domain);
        }
    }

    /// Returns tuple sets from bounds sorted by size
    fn sort_bounds(&self) -> Vec<(IntSet, usize)> {
        let mut sets = Vec::new();

        for relation in self.bounds.relations() {
            let lower = self.bounds.lower_bound(relation);
            let upper = self.bounds.upper_bound(relation);

            if let (Some(lower), Some(upper)) = (lower, upper) {
                if !lower.is_empty() && lower.size() < upper.size() {
                    sets.push((lower.index_view(), lower.arity()));
                }
                if !upper.is_empty() {
                    sets.push((upper.index_view(), upper.arity()));
                }
            }
        }

        // Sort by number of tuples (size of index view)
        sets.sort_by_key(|(index_view, _)| index_view.len());
        sets
    }

    /// Refines partitions based on a multi-column tuple set
    fn refine_partitions_multi(
        &mut self,
        set: &IntSet,
        arity: usize,
        range2domain: &mut HashMap<IntSet, IntSet>,
    ) {
        if arity == 1 {
            self.refine_partitions_simple(set);
            return;
        }

        let mut other_columns = Vec::new();
        let first_col_factor = self.usize.pow((arity - 1) as u32);

        // Extract first column
        let mut first_col = IntSet::new();
        for &tuple_idx in set {
            first_col.insert(tuple_idx / first_col_factor);
        }

        self.refine_partitions_simple(&first_col);

        let iden_factor = if self.usize > 1 {
            (1_i64 - first_col_factor as i64) / (1 - self.usize as i64)
        } else {
            0
        };

        // Process each partition that intersects with first column
        let mut new_parts = Vec::new();
        let mut i = 0;
        while i < self.parts.len() {
            let part = &self.parts[i];

            // Check if this partition intersects with first column
            if let Some(&min_atom) = part.iter().next() {
                if first_col.contains(&min_atom) {
                    // Remove this partition and split it
                    let part = self.parts.remove(i);
                    range2domain.clear();

                    for &atom in &part {
                        let mut atom_range = IntSet::new();
                        let start = atom * first_col_factor;
                        let end = (atom + 1) * first_col_factor;

                        for &tuple_idx in set {
                            if tuple_idx >= start && tuple_idx < end {
                                atom_range.insert(tuple_idx % first_col_factor);
                            }
                        }

                        range2domain
                            .entry(atom_range)
                            .or_insert_with(IntSet::new)
                            .insert(atom);
                    }

                    let mut iden_partition = IntSet::new();
                    for (atom_range, atom_domain) in range2domain.iter() {
                        if atom_domain.len() == 1 && atom_range.len() == 1 {
                            let atom = *atom_domain.iter().next().unwrap();
                            let range_val = *atom_range.iter().next().unwrap();
                            if range_val as i64 == atom as i64 * iden_factor {
                                iden_partition.insert(atom);
                            } else {
                                new_parts.push(atom_domain.clone());
                                other_columns.push(atom_range.clone());
                            }
                        } else {
                            new_parts.push(atom_domain.clone());
                            other_columns.push(atom_range.clone());
                        }
                    }

                    if !iden_partition.is_empty() {
                        new_parts.push(iden_partition);
                    }
                    continue;
                }
            }
            i += 1;
        }

        self.parts.extend(new_parts);

        // Refine based on remaining columns
        for other_col in other_columns {
            self.refine_partitions_multi(&other_col, arity - 1, range2domain);
        }
    }

    /// Refines partitions based on a simple set (single column)
    fn refine_partitions_simple(&mut self, set: &IntSet) {
        let mut i = 0;
        while i < self.parts.len() {
            let part = &self.parts[i];

            // Compute intersection of part and set
            let intersection: IntSet = part.intersection(set).copied().collect();

            if !intersection.is_empty() && intersection.len() < part.len() {
                // Split this partition
                let mut part = self.parts.remove(i);
                for &elem in &intersection {
                    part.remove(&elem);
                }

                self.parts.insert(i, part);
                self.parts.insert(i + 1, intersection);
                i += 2;
            } else {
                i += 1;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::instance::Universe;
    use crate::ast::Relation;

    #[test]
    fn test_empty_bounds() {
        let universe = Universe::new(&["a", "b", "c"]).unwrap();
        let bounds = Bounds::new(universe);
        let parts = SymmetryDetector::partition(bounds);

        // With no constraints, all atoms should be in one partition
        assert_eq!(parts.len(), 1);
        assert_eq!(parts[0].len(), 3);
    }

    #[test]
    fn test_exact_relation_splitting() {
        let universe = Universe::new(&["a", "b", "c"]).unwrap();
        let mut bounds = Bounds::new(universe.clone());
        let factory = universe.factory();

        let r = Relation::unary("r");
        let tuple_a = factory.tuple(&["a"]).unwrap();
        let mut set = crate::instance::TupleSet::empty(universe.clone(), 1);
        set.add(tuple_a).unwrap();

        bounds.bound_exactly(&r, set).unwrap();

        let parts = SymmetryDetector::partition(bounds);

        // Should have two partitions: {a} and {b, c}
        assert_eq!(parts.len(), 2);

        let has_singleton = parts.iter().any(|p| p.len() == 1);
        let has_pair = parts.iter().any(|p| p.len() == 2);

        assert!(has_singleton);
        assert!(has_pair);
    }
}
