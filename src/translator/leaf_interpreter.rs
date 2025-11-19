//! LeafInterpreter for converting relations and constants to BooleanMatrices
//!
//! Following Java: kodkod.engine.fol2sat.LeafInterpreter

use crate::ast::{ConstantExpr, Relation};
use crate::bool::{
    BooleanFactory, BooleanMatrix, Dimensions, Options,
    VariableAllocator,
};
use crate::instance::{Bounds, TupleSet, Universe};
use rustc_hash::FxHashMap;
use std::ops::Range;

/// Interprets leaf expressions (Relations, Constants) as BooleanMatrices
///
/// Following Java: LeafInterpreter
pub struct LeafInterpreter {
    factory: BooleanFactory,
    universe: Universe,
    var_ranges: FxHashMap<Relation, Range<u32>>,
    lower_bounds: FxHashMap<Relation, TupleSet>,
    upper_bounds: FxHashMap<Relation, TupleSet>,
}

impl LeafInterpreter {
    /// Creates a LeafInterpreter from Bounds, allocating variables for all relations
    /// Following Java: LeafInterpreter constructor
    pub fn from_bounds(bounds: &Bounds, options: &Options) -> Self {
        let mut allocator = VariableAllocator::new();
        let mut var_ranges = FxHashMap::default();
        let mut lower_bounds = FxHashMap::default();
        let mut upper_bounds = FxHashMap::default();

        // Collect bounds and allocate variables for each relation
        for relation in bounds.relations() {
            let lower = bounds.lower_bound(relation).unwrap();
            let upper = bounds.upper_bound(relation).unwrap();

            let range = allocator.allocate_for_relation(relation, lower.size(), upper.size());

            if !range.is_empty() {
                var_ranges.insert(relation.clone(), range);
            }

            lower_bounds.insert(relation.clone(), lower.clone());
            upper_bounds.insert(relation.clone(), upper.clone());
        }

        // Create factory with total allocated variables
        let factory = BooleanFactory::new(allocator.total_variables(), options.clone());

        Self {
            factory,
            universe: bounds.universe().clone(),
            var_ranges,
            lower_bounds,
            upper_bounds,
        }
    }

    /// Returns a reference to the factory (has interior mutability)
    pub fn factory(&self) -> &BooleanFactory {
        &self.factory
    }

    /// Returns a reference to the arena (from the factory)
    pub fn arena(&self) -> &crate::bool::MatrixArena {
        self.factory.arena()
    }

    /// Returns a reference to the universe
    pub fn universe(&self) -> &Universe {
        &self.universe
    }

    /// Returns the variable ranges for all relations
    /// Used for solution extraction from SAT model
    pub fn variable_ranges(&self) -> &FxHashMap<Relation, Range<u32>> {
        &self.var_ranges
    }

    /// Returns the lower bounds for all relations
    /// Used for solution extraction
    pub fn lower_bounds(&self) -> &FxHashMap<Relation, TupleSet> {
        &self.lower_bounds
    }

    /// Returns the upper bounds for all relations
    /// Used for solution extraction
    pub fn upper_bounds(&self) -> &FxHashMap<Relation, TupleSet> {
        &self.upper_bounds
    }

    /// Interprets a relation as a BooleanMatrix
    /// Following Java: LeafInterpreter.interpret(Relation)
    pub fn interpret_relation(&self, rel: &Relation) -> BooleanMatrix<'_> {
        let lower = self
            .lower_bounds
            .get(rel)
            .expect("Relation not in bounds");
        let upper = self
            .upper_bounds
            .get(rel)
            .expect("Relation not in bounds");

        // Convert tuples to flat indices
        let lower_indices = Self::tuple_set_to_indices(lower, &self.universe);
        let upper_indices = Self::tuple_set_to_indices(upper, &self.universe);

        // Create matrix: upper indices define domain, lower indices are TRUE
        let dims = Dimensions::new(
            self.universe.size().pow(rel.arity() as u32),
            rel.arity(),
        );

        let mut matrix =
            BooleanMatrix::with_bounds(dims, &self.factory, &upper_indices, &lower_indices);

        // Assign variables to tuples in (upper - lower)
        if let Some(var_range) = self.var_ranges.get(rel) {
            let mut var_id = var_range.start;

            for &idx in &upper_indices {
                if !lower_indices.contains(&idx) {
                    // This tuple is uncertain - assign a variable
                    matrix.set(idx, self.factory.variable(var_id as i32));
                    var_id += 1;
                }
            }
        }

        matrix
    }

    /// Interprets a constant expression (UNIV, NONE, IDEN, INTS)
    /// Following Java: LeafInterpreter.interpret(ConstantExpression)
    pub fn interpret_constant(&self, c: ConstantExpr) -> BooleanMatrix<'_> {
        let univ_size = self.universe.size();

        match c {
            ConstantExpr::Univ => {
                // All unary tuples
                let dims = Dimensions::new(univ_size, 1);
                let all_indices: Vec<usize> = (0..univ_size).collect();
                BooleanMatrix::with_bounds(
                    dims,
                    &self.factory,
                    &all_indices,
                    &all_indices, // All TRUE
                )
            }

            ConstantExpr::None => {
                // Empty set
                let dims = Dimensions::new(univ_size, 1);
                BooleanMatrix::with_bounds(
                    dims,
                    &self.factory,
                    &[], // No indices
                    &[],
                )
            }

            ConstantExpr::Iden => {
                // Identity: {(i,i) | i in universe}
                // Binary relation, so capacity = univ_size²
                let dims = Dimensions::new(univ_size * univ_size, 2);
                let mut iden_indices = Vec::new();
                for i in 0..univ_size {
                    iden_indices.push(i * univ_size + i);
                }
                BooleanMatrix::with_bounds(
                    dims,
                    &self.factory,
                    &iden_indices,
                    &iden_indices, // All TRUE
                )
            }

            ConstantExpr::Ints => {
                // Integer atoms are an extension feature
                // Return empty set (correct for relational-only problems)
                let dims = Dimensions::new(univ_size, 1);
                BooleanMatrix::with_bounds(dims, &self.factory, &[], &[])
            }
        }
    }

    /// Converts a TupleSet to flat indices for BooleanMatrix
    /// Following Java pattern from LeafInterpreter
    pub fn tuple_set_to_indices(tuple_set: &TupleSet, _universe: &Universe) -> Vec<usize> {
        let mut indices = Vec::new();

        for tuple in tuple_set.iter() {
            // Use the stored index from the tuple
            indices.push(tuple.index());
        }

        indices
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Relation;
    use crate::bool::BooleanConstant;
    use crate::instance::{Bounds, Universe};

    #[test]
    fn test_leaf_interpreter_creation() {
        let universe = Universe::new(&["A", "B", "C"]).unwrap();
        let bounds = Bounds::new(universe.clone());

        let options = Options::default();
        let _interpreter = LeafInterpreter::from_bounds(&bounds, &options);
    }

    #[test]
    fn test_interpret_constant_univ() {
        let universe = Universe::new(&["A", "B", "C"]).unwrap();
        let bounds = Bounds::new(universe.clone());

        let options = Options::default();
        let mut interpreter = LeafInterpreter::from_bounds(&bounds, &options);

        let matrix = interpreter.interpret_constant(ConstantExpr::Univ);
        assert_eq!(matrix.dimensions().capacity(), 3);
        assert_eq!(matrix.density(), 3); // All TRUE
    }

    #[test]
    fn test_interpret_constant_none() {
        let universe = Universe::new(&["A", "B"]).unwrap();
        let bounds = Bounds::new(universe.clone());

        let options = Options::default();
        let mut interpreter = LeafInterpreter::from_bounds(&bounds, &options);

        let matrix = interpreter.interpret_constant(ConstantExpr::None);
        assert_eq!(matrix.density(), 0); // All FALSE (sparse)
    }

    #[test]
    fn test_interpret_constant_iden() {
        let universe = Universe::new(&["A", "B"]).unwrap();
        let bounds = Bounds::new(universe.clone());

        let options = Options::default();
        let mut interpreter = LeafInterpreter::from_bounds(&bounds, &options);

        let matrix = interpreter.interpret_constant(ConstantExpr::Iden);
        assert_eq!(matrix.dimensions().capacity(), 4); // 2x2
        assert_eq!(matrix.density(), 2); // Only diagonal: (A,A) and (B,B)

        // Check diagonal is TRUE
        assert_eq!(matrix.get(0).label(), BooleanConstant::TRUE.label()); // (A,A) at index 0
        assert_eq!(matrix.get(3).label(), BooleanConstant::TRUE.label()); // (B,B) at index 3
        // Off-diagonal should be FALSE
        assert_eq!(matrix.get(1).label(), BooleanConstant::FALSE.label());
        assert_eq!(matrix.get(2).label(), BooleanConstant::FALSE.label());
    }

    #[test]
    fn test_interpret_relation() {
        let universe = Universe::new(&["A", "B", "C"]).unwrap();
        let mut bounds = Bounds::new(universe.clone());

        let r = Relation::unary("R");
        let factory = bounds.universe().factory();

        // R: lower={(A)}, upper={(A), (B), (C)}
        bounds
            .bound(
                &r,
                factory.tuple_set(&[&["A"]]).unwrap(),
                factory.tuple_set(&[&["A"], &["B"], &["C"]]).unwrap(),
            )
            .unwrap();

        let options = Options::default();
        let mut interpreter = LeafInterpreter::from_bounds(&bounds, &options);
        let matrix = interpreter.interpret_relation(&r);

        // Index 0 (A) → TRUE (in lower bound)
        assert_eq!(matrix.get(0).label(), BooleanConstant::TRUE.label());

        // Index 1 (B) → variable 1 (uncertain)
        assert!(matrix.get(1).is_variable());
        assert_eq!(matrix.get(1).label(), 1);

        // Index 2 (C) → variable 2 (uncertain)
        assert!(matrix.get(2).is_variable());
        assert_eq!(matrix.get(2).label(), 2);
    }
}
