use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

/// A simple access control policy framework
///
/// ```alloy
/// sig Subject {}
/// sig Resource {}
/// sig Action {}
/// one sig Request {s : Subject,  r : Resource, a : Action }
///
/// sig Conflicted {s : Subject, r : Resource}
///
/// pred RevPaperNoConflict (req : Request) {
///   no conf : Conflicted | req.s in conf.s && req.r in conf.r
/// }
///
/// pred pol (req: Request) {
///   RevPaperNoConflict(req)
/// }
///
/// run pol for 2
/// ```
struct DiffEg {
    subject: Relation,
    resource: Relation,
    action: Relation,
    request: Relation,
    conflicted: Relation,
    s_request: Relation,
    r_request: Relation,
    action_field: Relation,
    s_conflicted: Relation,
    r_conflicted: Relation,
}

impl DiffEg {
    fn new() -> Self {
        Self {
            subject: Relation::unary("Subject"),
            resource: Relation::unary("Resource"),
            action: Relation::unary("Action"),
            request: Relation::unary("Request"),
            conflicted: Relation::unary("Conflicted"),
            s_request: Relation::binary("s"),
            r_request: Relation::binary("r"),
            action_field: Relation::binary("a"),
            s_conflicted: Relation::binary("s"),
            r_conflicted: Relation::binary("r"),
        }
    }

    /// Returns the formulas implicit in the declarations.
    /// ```alloy
    /// sig Subject {}
    /// sig Resource {}
    /// sig Action {}
    /// one sig Request {s : Subject,  r : Resource, a : Action }
    /// sig Conflicted {s : Subject, r : Resource}
    /// ```
    fn decls(&self) -> Formula {
        let f0 = Expression::from(self.request.clone()).one(); // one Request

        // s is a function from Request to Subject
        let f1 = self.s_request.clone().function(
            Expression::from(self.request.clone()),
            Expression::from(self.subject.clone())
        );

        // r is a function from Request to Resource
        let f2 = self.r_request.clone().function(
            Expression::from(self.request.clone()),
            Expression::from(self.resource.clone())
        );

        // a is a function from Request to Action
        let f3 = self.action_field.clone().function(
            Expression::from(self.request.clone()),
            Expression::from(self.action.clone())
        );

        // s is a function from Conflicted to Subject
        let f4 = self.s_conflicted.clone().function(
            Expression::from(self.conflicted.clone()),
            Expression::from(self.subject.clone())
        );

        // r is a function from Conflicted to Resource
        let f5 = self.r_conflicted.clone().function(
            Expression::from(self.conflicted.clone()),
            Expression::from(self.resource.clone())
        );

        Formula::and_all(vec![f0, f1, f2, f3, f4, f5])
    }

    /// Returns the RevPaperNoConflict access rule.
    /// ```alloy
    /// pred RevPaperNoConflict (req : Request) {
    ///   no conf : Conflicted | req.s in conf.s && req.r in conf.r
    /// }
    /// ```
    fn rev_paper_no_conflict(&self, req: Expression) -> Formula {
        let conf = Variable::unary("conf");

        // req.s in conf.s
        let f0 = req.clone()
            .join(Expression::from(self.s_request.clone()))
            .in_set(Expression::from(conf.clone()).join(Expression::from(self.s_conflicted.clone())));

        // req.r in conf.r
        let f1 = req.join(Expression::from(self.r_request.clone()))
            .in_set(Expression::from(conf.clone()).join(Expression::from(self.r_conflicted.clone())));

        // (no conf : Conflicted | req.s in conf.s && req.r in conf.r) <=>
        // all conf : Conflicted | !(req.s in conf.s && req.r in conf.r)
        Formula::forall(
            Decls::from(Decl::one_of(conf, Expression::from(self.conflicted.clone()))),
            f0.and(f1).not()
        )
    }

    /// Returns the pol predicate
    /// ```alloy
    /// pred pol (req: Request) {
    ///   RevPaperNoConflict(req)
    /// }
    /// ```
    fn pol(&self, req: Expression) -> Formula {
        self.rev_paper_no_conflict(req)
    }

    /// Returns a formula that 'runs' the pol predicate.
    /// ```alloy
    /// some req: Request | pol(req)
    /// ```
    fn run_pol(&self) -> Formula {
        let req = Variable::unary("req");
        Formula::exists(
            Decls::from(Decl::one_of(req.clone(), Expression::from(self.request.clone()))),
            self.pol(Expression::from(req))
        )
    }

    /// Returns the bounds for the given alloy scope.
    fn bounds(&self, scope: usize) -> Result<Bounds, kodkod_rs::error::KodkodError> {
        assert!(scope > 0);

        let mut atoms = Vec::new();
        for i in 0..scope {
            atoms.push(format!("Subject{}", i));
        }
        for i in 0..scope {
            atoms.push(format!("Resource{}", i));
        }
        for i in 0..scope {
            atoms.push(format!("Action{}", i));
        }
        for i in 0..scope {
            atoms.push(format!("Conflicted{}", i));
        }
        for i in 0..scope {
            atoms.push(format!("Request{}", i));
        }

        let atom_strs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
        let u = Universe::new(&atom_strs)?;
        let f = u.factory();
        let mut b = Bounds::new(u);

        let max = scope - 1;

        b.bound(
            &self.subject,
            f.none(1),
            f.range(f.tuple(&["Subject0"])?, f.tuple(&[&format!("Subject{}", max)])?)?
        )?;
        b.bound(
            &self.resource,
            f.none(1),
            f.range(f.tuple(&["Resource0"])?, f.tuple(&[&format!("Resource{}", max)])?)?
        )?;
        b.bound(
            &self.action,
            f.none(1),
            f.range(f.tuple(&["Action0"])?, f.tuple(&[&format!("Action{}", max)])?)?
        )?;
        b.bound(
            &self.conflicted,
            f.none(1),
            f.range(f.tuple(&["Conflicted0"])?, f.tuple(&[&format!("Conflicted{}", max)])?)?
        )?;
        b.bound(
            &self.request,
            f.none(1),
            f.range(f.tuple(&["Request0"])?, f.tuple(&[&format!("Request{}", max)])?)?
        )?;

        // Bind field relations
        let request_upper = b.upper_bound(&self.request).expect("request upper").clone();
        let subject_upper = b.upper_bound(&self.subject).expect("subject upper").clone();
        let resource_upper = b.upper_bound(&self.resource).expect("resource upper").clone();
        let action_upper = b.upper_bound(&self.action).expect("action upper").clone();
        let conflicted_upper = b.upper_bound(&self.conflicted).expect("conflicted upper").clone();

        b.bound(&self.s_request, f.none(2), request_upper.clone().product(&subject_upper)?)?;
        b.bound(&self.r_request, f.none(2), request_upper.clone().product(&resource_upper)?)?;
        b.bound(&self.action_field, f.none(2), request_upper.product(&action_upper)?)?;
        b.bound(&self.s_conflicted, f.none(2), conflicted_upper.clone().product(&subject_upper)?)?;
        b.bound(&self.r_conflicted, f.none(2), conflicted_upper.product(&resource_upper)?)?;

        Ok(b)
    }
}

fn usage() -> ! {
    eprintln!("Usage: diff_eg <scope>");
    std::process::exit(1);
}

fn main() -> Result<(), kodkod_rs::error::KodkodError> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        usage();
    }

    let n: usize = args[1].parse().unwrap_or_else(|_| usage());
    if n < 1 {
        usage();
    }

    let model = DiffEg::new();
    let solver = Solver::new(Options::default());

    let formula = model.decls().and(model.run_pol());
    let bounds = model.bounds(n)?;

    println!("\n=== DiffEg (scope={}) ===\n", n);

    let solution = solver.solve(&formula, &bounds)?;
    println!("{solution:#?}");

    Ok(())
}
