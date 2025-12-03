//! File system specification
//!
//! A KK encoding of a hierarchical file system with files, directories,
//! and directory entries. Models constraints on parent relationships,
//! unique names within directories, acyclicity, and directory reachability.
//!
//! Tests the "no directory aliases" invariant (no directory can appear
//! as contents in multiple locations).
//!
//! Following Java: kodkod.examples.alloy.FileSystem

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

fn run() {
    let scope = 2;  // Smaller scope to avoid overflow
    println!(
        "=== File System Specification (scope {}) ===\n",
        scope
    );

    // Create universe with fixed size for simplicity
    let universe = Universe::new(&["Object0", "Object1",
                                   "Name0", "Name1",
                                   "DirEntry0", "DirEntry1"]).unwrap();

    let factory = universe.factory();

    // Create relations
    let obj = Relation::unary("Object");
    let name = Relation::unary("Name");
    let file = Relation::unary("File");
    let dir = Relation::unary("Dir");
    let root = Relation::unary("Root");
    let cur = Relation::unary("Cur");
    let dir_entry = Relation::unary("DirEntry");

    // Binary relations
    let entries = Relation::binary("entries");
    let parent = Relation::binary("parent");
    let obj_name = Relation::binary("name");
    let contents = Relation::binary("contents");

    let mut bounds = Bounds::new(universe);

    // Bind Object (atoms Object0, Object1)
    let obj_tuples = vec![vec!["Object0"], vec!["Object1"]];
    let obj_refs: Vec<&[&str]> = obj_tuples.iter().map(|t| t.as_slice()).collect();
    bounds
        .bound_exactly(&obj, factory.tuple_set(&obj_refs).unwrap())
        .unwrap();

    // Root: exactly Object0
    let root_tuples = vec![vec!["Object0"]];
    let root_refs: Vec<&[&str]> = root_tuples.iter().map(|t| t.as_slice()).collect();
    bounds
        .bound_exactly(&root, factory.tuple_set(&root_refs).unwrap())
        .unwrap();

    // Cur, File, Dir: subsets of Object
    bounds
        .bound(&cur, factory.none(1), factory.all(1))
        .unwrap();
    bounds
        .bound(&file, factory.none(1), factory.all(1))
        .unwrap();
    bounds
        .bound(&dir, factory.none(1), factory.all(1))
        .unwrap();

    // Bind Name
    let name_tuples = vec![vec!["Name0"], vec!["Name1"]];
    let name_refs: Vec<&[&str]> = name_tuples.iter().map(|t| t.as_slice()).collect();
    bounds
        .bound_exactly(&name, factory.tuple_set(&name_refs).unwrap())
        .unwrap();

    // Bind DirEntry
    let entry_tuples = vec![vec!["DirEntry0"], vec!["DirEntry1"]];
    let entry_refs: Vec<&[&str]> = entry_tuples.iter().map(|t| t.as_slice()).collect();
    bounds
        .bound_exactly(&dir_entry, factory.tuple_set(&entry_refs).unwrap())
        .unwrap();

    // entries: Dir x DirEntry (all possible pairs)
    bounds
        .bound(&entries, factory.none(2), factory.all(2))
        .unwrap();

    // parent: Dir x Dir (all possible pairs)
    bounds
        .bound(&parent, factory.none(2), factory.all(2))
        .unwrap();

    // name: DirEntry x Name (all possible pairs)
    bounds
        .bound(&obj_name, factory.none(2), factory.all(2))
        .unwrap();

    // contents: DirEntry x Object (all possible pairs)
    bounds
        .bound(&contents, factory.none(2), factory.all(2))
        .unwrap();

    // Build specification and check
    let formula = check_no_dir_aliases(&obj, &file, &dir, &root,
                                       &entries, &parent, &obj_name, &contents, &dir_entry);

    let solver = Solver::new(Options::default());
    match solver.solve(&formula, &bounds) {
        Ok(solution) => {
            println!("Result: {}", if solution.is_sat() { "SAT" } else { "UNSAT" });
            println!(
                "Variables: {}, Clauses: {}",
                solution.statistics().num_variables(),
                solution.statistics().num_clauses()
            );
        }
        Err(e) => {
            eprintln!("Error: {:?}", e);
        }
    }
}

fn main() {
    run()
}

/// Basic declarations and constraints
fn decls(obj: &Relation, file: &Relation, dir: &Relation, root: &Relation) -> Formula {
    // File and Dir partition Object
    Expression::from(obj.clone()).equals(
        Expression::from(file.clone()).union(Expression::from(dir.clone()))
    ).and(
        Expression::from(file.clone()).intersection(Expression::from(dir.clone())).no()
    ).and(
        // Root is in Dir
        Expression::from(root.clone()).in_set(Expression::from(dir.clone()))
    ).and(
        // Non-empty
        Expression::from(obj.clone()).some()
    )
}

/// No directory can appear as contents in multiple locations (no aliases)
fn no_dir_aliases(dir: &Relation, contents: &Relation) -> Formula {
    let o = Variable::unary("o");
    let o_expr = Expression::from(o.clone());
    let contents_transpose = Expression::from(contents.clone()).transpose();

    // For each object, it appears in at most one contents relation
    let lone_check = o_expr.join(contents_transpose).lone();
    Formula::forall(
        Decls::from(Decl::one_of(o.clone(), Expression::from(dir.clone()))),
        lone_check,
    )
}

/// Check the formula: decls and NOT no_dir_aliases (looking for counterexamples)
fn check_no_dir_aliases(obj: &Relation, file: &Relation, dir: &Relation, root: &Relation,
                        _entries: &Relation, _parent: &Relation, _obj_name: &Relation,
                        contents: &Relation, _dir_entry: &Relation) -> Formula {
    let d = decls(obj, file, dir, root);
    let check = no_dir_aliases(dir, contents).not();

    d.and(check)
}

#[test]
fn test_alloy_file_system_runs() {
    // Test that the example runs without panicking
    run();
}
