//! Variable allocation for SAT encoding
//!
//! Pre-allocates SAT variable IDs for relation tuples before translation begins.
//! Following Java: kodkod.engine.fol2sat.LeafInterpreter.allocateVars

use crate::ast::Relation;
use std::collections::HashMap;
use std::ops::Range;

/// Allocates SAT variables for relation tuples
///
/// Following Java: LeafInterpreter.allocateVars()
/// Variables are allocated for tuples in (upperBound - lowerBound)
pub struct VariableAllocator {
    next_var: u32,
    relation_vars: HashMap<Relation, Range<u32>>,
}

impl VariableAllocator {
    /// Creates a new variable allocator
    pub fn new() -> Self {
        Self {
            next_var: 1, // Variables start at 1 (following Java/DIMACS convention)
            relation_vars: HashMap::new(),
        }
    }

    /// Allocates variables for (upperBound - lowerBound) tuples
    /// Following Java: LeafInterpreter.allocateVars()
    ///
    /// # Arguments
    /// * `relation` - The relation to allocate variables for
    /// * `lower_bound_size` - Number of tuples definitely in the relation
    /// * `upper_bound_size` - Total number of possible tuples
    ///
    /// # Returns
    /// Range of variable IDs allocated (empty range if no variables needed)
    pub fn allocate_for_relation(
        &mut self,
        relation: &Relation,
        lower_bound_size: usize,
        upper_bound_size: usize,
    ) -> Range<u32> {
        let num_vars = upper_bound_size.saturating_sub(lower_bound_size);

        if num_vars == 0 {
            // No variables needed (relation fully determined)
            return 0..0;
        }

        let start = self.next_var;
        let end = start + num_vars as u32;
        let range = start..end;

        self.relation_vars
            .insert(relation.clone(), range.clone());
        self.next_var = end;

        range
    }

    /// Returns the total number of variables allocated
    pub fn total_variables(&self) -> u32 {
        if self.next_var == 1 {
            0
        } else {
            self.next_var - 1
        }
    }

    /// Gets the variable range for a relation
    pub fn get_range(&self, relation: &Relation) -> Option<&Range<u32>> {
        self.relation_vars.get(relation)
    }
}

impl Default for VariableAllocator {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_variable_allocation() {
        let mut allocator = VariableAllocator::new();

        let r1 = Relation::unary("R1");
        let r2 = Relation::binary("R2");
        let r3 = Relation::unary("R3");

        // R1: 3 uncertain tuples (upper=3, lower=0)
        let range1 = allocator.allocate_for_relation(&r1, 0, 3);
        assert_eq!(range1, 1..4);
        assert_eq!(allocator.total_variables(), 3);

        // R2: 5 uncertain tuples (upper=6, lower=1)
        let range2 = allocator.allocate_for_relation(&r2, 1, 6);
        assert_eq!(range2, 4..9);
        assert_eq!(allocator.total_variables(), 8);

        // R3: 0 uncertain tuples (fully determined: upper=2, lower=2)
        let range3 = allocator.allocate_for_relation(&r3, 2, 2);
        assert_eq!(range3, 0..0);
        assert_eq!(allocator.total_variables(), 8); // No change

        // Verify ranges are stored
        assert_eq!(allocator.get_range(&r1), Some(&(1..4)));
        assert_eq!(allocator.get_range(&r2), Some(&(4..9)));
        assert_eq!(allocator.get_range(&r3), None); // No variables allocated
    }

    #[test]
    fn test_empty_allocator() {
        let allocator = VariableAllocator::new();
        assert_eq!(allocator.total_variables(), 0);
    }

    #[test]
    fn test_fully_determined_relations() {
        let mut allocator = VariableAllocator::new();
        let r = Relation::unary("R");

        // Fully determined (lower == upper)
        let range = allocator.allocate_for_relation(&r, 5, 5);
        assert_eq!(range, 0..0);
        assert_eq!(allocator.total_variables(), 0);
    }

    #[test]
    fn test_sequential_allocation() {
        let mut allocator = VariableAllocator::new();

        let r1 = Relation::unary("R1");
        let r2 = Relation::unary("R2");
        let r3 = Relation::unary("R3");

        allocator.allocate_for_relation(&r1, 0, 2); // vars 1-2
        allocator.allocate_for_relation(&r2, 0, 3); // vars 3-5
        allocator.allocate_for_relation(&r3, 0, 1); // var 6

        assert_eq!(allocator.total_variables(), 6);
        assert_eq!(allocator.get_range(&r1), Some(&(1..3)));
        assert_eq!(allocator.get_range(&r2), Some(&(3..6)));
        assert_eq!(allocator.get_range(&r3), Some(&(6..7)));
    }
}
