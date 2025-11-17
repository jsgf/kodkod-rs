//! Symmetry breaking for formulas
//!
//! Breaks symmetries detected in bounds by generating lex-leader predicates.

use crate::bool::{BoolValue, BooleanFactory, BooleanConstant};
use crate::engine::symmetry_detector::{SymmetryDetector, IntSet};
use crate::instance::Bounds;
use crate::translator::LeafInterpreter;

/// Breaks symmetries for a given problem
pub struct SymmetryBreaker {
    bounds: Bounds,
    symmetries: Vec<IntSet>,
    usize: usize,
}

impl SymmetryBreaker {
    /// Constructs a new symmetry breaker for the given bounds
    pub fn new(bounds: Bounds) -> Self {
        let symmetries = SymmetryDetector::partition(bounds.clone());
        let usize = bounds.universe().size();

        Self {
            bounds,
            symmetries,
            usize,
        }
    }

    /// Generates a symmetry breaking predicate (SBP)
    ///
    /// Creates a lex-leader circuit that enforces canonical ordering
    /// on symmetric partitions, preventing exploration of equivalent
    /// solutions.
    pub fn generate_sbp<'a>(
        &mut self,
        interpreter: &'a LeafInterpreter,
        pred_length: i32,
    ) -> BoolValue<'a> {
        if self.symmetries.is_empty() || pred_length == 0 {
            return BoolValue::Constant(BooleanConstant::TRUE);
        }

        let factory = interpreter.factory();
        let mut sbp_gates = Vec::new();

        // For each symmetric partition
        for sym in &self.symmetries {
            let atoms: Vec<usize> = sym.iter().copied().collect();

            // For each pair of atoms in the partition
            for i in 0..atoms.len() - 1 {
                let prev_index = atoms[i];
                let cur_index = atoms[i + 1];

                // Collect original and permuted values
                let mut original = Vec::new();
                let mut permuted = Vec::new();

                // For each relation in bounds
                for relation in self.bounds.relations() {
                    if original.len() >= pred_length as usize {
                        break;
                    }

                    // Get the boolean matrix for this relation
                    let matrix = interpreter.interpret_relation(relation);

                    // For each entry in the matrix
                    for row in 0..matrix.dimensions().rows() {
                        for col in 0..matrix.dimensions().cols() {
                            if original.len() >= pred_length as usize {
                                break;
                            }

                            let entry_value = matrix.get_row_col(row, col);

                            // Compute the permuted index by swapping prev_index and cur_index
                            let perm_idx = self.permute_index(
                                relation.arity(),
                                row * matrix.dimensions().cols() + col,
                                prev_index,
                                cur_index,
                            );

                            let perm_row = perm_idx / matrix.dimensions().cols();
                            let perm_col = perm_idx % matrix.dimensions().cols();

                            if perm_row < matrix.dimensions().rows()
                                && perm_col < matrix.dimensions().cols()
                            {
                                let perm_value = matrix.get_row_col(perm_row, perm_col);

                                // Only add if different positions or different values
                                if (row, col) != (perm_row, perm_col) {
                                    original.push(entry_value.clone());
                                    permuted.push(perm_value.clone());
                                }
                            }
                        }
                    }
                }

                // Generate lex-leader constraint: original <= permuted
                if !original.is_empty() {
                    sbp_gates.push(self.lex_leader(factory, &original, &permuted));
                }
            }
        }

        // Clear symmetries (conservatively mark as broken)
        self.symmetries.clear();

        // Conjoin all constraints
        if sbp_gates.is_empty() {
            BoolValue::Constant(BooleanConstant::TRUE)
        } else {
            let mut result = sbp_gates[0].clone();
            for gate in &sbp_gates[1..] {
                result = factory.and(result, gate.clone());
            }
            result
        }
    }

    /// Permutes a tuple index by swapping two atom indices
    fn permute_index(&self, arity: usize, tuple_idx: usize, from: usize, to: usize) -> usize {
        let mut result = 0;
        let mut remaining = tuple_idx;
        let base = self.usize;

        for i in (0..arity).rev() {
            let divisor = base.pow(i as u32);
            let mut atom_idx = remaining / divisor;

            // Swap atoms
            if atom_idx == from {
                atom_idx = to;
            } else if atom_idx == to {
                atom_idx = from;
            }

            result += atom_idx * divisor;
            remaining %= divisor;
        }

        result
    }

    /// Generates a lex-leader constraint: l0 <= l1
    ///
    /// Returns a circuit that is true iff the bit string l0
    /// is lexicographically less than or equal to l1.
    fn lex_leader<'a>(
        &self,
        factory: &'a BooleanFactory,
        l0: &[BoolValue<'a>],
        l1: &[BoolValue<'a>],
    ) -> BoolValue<'a> {
        assert_eq!(l0.len(), l1.len());

        let mut constraints = Vec::new();
        let mut prev_equals = BoolValue::Constant(BooleanConstant::TRUE);

        for i in 0..l0.len() {
            // prevEquals => (l0[i] => l1[i])
            let implies_bits = factory.implies(l0[i].clone(), l1[i].clone());
            constraints.push(factory.implies(prev_equals.clone(), implies_bits));

            // Update prevEquals = prevEquals AND (l0[i] <=> l1[i])
            let iff = factory.iff(l0[i].clone(), l1[i].clone());
            prev_equals = factory.and(prev_equals, iff);
        }

        // Conjoin all constraints
        let mut result = constraints[0].clone();
        for constraint in &constraints[1..] {
            result = factory.and(result, constraint.clone());
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::instance::Universe;

    #[test]
    fn test_symmetry_breaker_creation() {
        let universe = Universe::new(&["a", "b", "c"]).unwrap();
        let bounds = Bounds::new(universe);

        let breaker = SymmetryBreaker::new(bounds.clone());

        // Should detect one symmetric partition with all atoms
        assert_eq!(breaker.symmetries.len(), 1);
        assert_eq!(breaker.symmetries[0].len(), 3);
    }
}
