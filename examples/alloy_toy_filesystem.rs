use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

/// A toy filesystem specification.
struct ToyFilesystem {
    file: Relation,
    dir: Relation,
    root: Relation,
    contents: Relation,
}

impl ToyFilesystem {
    fn new() -> Self {
        Self {
            file: Relation::unary("File"),
            dir: Relation::unary("Dir"),
            root: Relation::unary("Root"),
            contents: Relation::binary("contents"),
        }
    }

    /// Returns the toy filesystem constraints
    fn constraints(&self) -> Formula {
        // contents in dir -> (dir + file)
        let f0 = Expression::from(self.contents.clone()).in_set(
            Expression::from(self.dir.clone()).product(
                Expression::from(self.dir.clone()).union(Expression::from(self.file.clone()))
            )
        );

        // all d: dir | d not in d.^contents
        let d = Variable::unary("d");
        let f1 = Formula::forall(
            Decls::from(Decl::one_of(d.clone(), Expression::from(self.dir.clone()))),
            Expression::from(d.clone())
                .in_set(
                    Expression::from(d).join(
                        Expression::from(self.contents.clone()).closure()
                    )
                )
                .not()
        );

        // root in dir
        let f2 = Expression::from(self.root.clone()).in_set(Expression::from(self.dir.clone()));

        // file + dir in root.*contents
        let f3 = Expression::from(self.file.clone())
            .union(Expression::from(self.dir.clone()))
            .in_set(
                Expression::from(self.root.clone()).join(
                    Expression::from(self.contents.clone()).reflexive_closure()
                )
            );

        Formula::and_all(vec![f0, f1, f2, f3])
    }

    /// Returns the toy filesystem bounds.
    fn bounds(&self) -> Result<Bounds, kodkod_rs::error::KodkodError> {
        let universe = Universe::new(&["d0", "d1", "f0", "f1", "f2"])?;
        let factory = universe.factory();
        let mut bounds = Bounds::new(universe);

        // root = {d0}
        bounds.bound_exactly(&self.root, factory.set_of_atom("d0")?)?;

        // dir in {d0, d1}
        let dir_tuples = vec![vec!["d0"], vec!["d1"]];
        let dir_refs: Vec<&[&str]> = dir_tuples.iter().map(|t| t.as_slice()).collect();
        bounds.bound(&self.dir, factory.none(1), factory.tuple_set(&dir_refs)?)?;

        // file in {f0, f1, f2}
        let file_tuples = vec![vec!["f0"], vec!["f1"], vec!["f2"]];
        let file_refs: Vec<&[&str]> = file_tuples.iter().map(|t| t.as_slice()).collect();
        bounds.bound(&self.file, factory.none(1), factory.tuple_set(&file_refs)?)?;

        // contents lower bound: {(d0, d1)}
        let contents_lower = factory.tuple_set(&[&["d0", "d1"][..]])?;

        // contents upper bound: dir x allOf(1)
        let dir_upper = bounds.upper_bound(&self.dir).expect("dir should have upper bound").clone();
        let contents_upper = dir_upper.product(&factory.all(1))?;

        bounds.bound(&self.contents, contents_lower, contents_upper)?;

        Ok(bounds)
    }
}

fn main() -> Result<(), kodkod_rs::error::KodkodError> {
    let toy = ToyFilesystem::new();
    let formula = toy.constraints();

    println!("=== ToyFilesystem ===\n");

    let bounds = toy.bounds()?;
    let solver = Solver::new(Options::default());

    let solution = solver.solve(&formula, &bounds)?;
    println!("{solution:#?}");

    Ok(())
}
