use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

/// A kodkod encoding of bigconfig.als:
///
/// ```alloy
/// module internal/bigconfig
///
/// abstract sig Site {}
/// sig HQ, Sub extends Site {}
///
/// sig Router {
///   site: Site,
///   link: set Router
/// }
///
/// pred invariants() {
///   -- every site has at least one router
///   Site in Router.site
///
///   -- links are symmetric and non-reflexive
///   link = ~link
///   no link & iden
/// }
///
/// pred subsConnectedToHQ() {
///   -- every sub location is connected to an HQ location
///   site.Sub in (site.HQ).link
/// }
///
/// pred connectedSites(sites: set Site) {
///   -- all sites in the given set are connected to each other
///   all s: sites | sites - s in ((site.s).^link).site
/// }
///
/// pred show() {
///   invariants() && subsConnectedToHQ() && connectedSites(Site)
/// }
/// ```
struct Bigconfig {
    // sigs
    router: Relation,
    site_sig: Relation,
    hq: Relation,
    sub: Relation,
    // fields
    site: Relation,
    link: Relation,

    closure_approx: usize,
}

impl Bigconfig {
    fn new(closure_approx: usize) -> Self {
        Self {
            router: Relation::unary("Router"),
            site_sig: Relation::unary("Site"),
            hq: Relation::unary("HQ"),
            sub: Relation::unary("Sub"),
            site: Relation::binary("site"),
            link: Relation::binary("link"),
            closure_approx,
        }
    }

    /// Returns the constraints implicit in signature and field declarations.
    /// ```alloy
    /// abstract sig Site {}
    /// sig HQ, Sub extends Site {}
    ///
    /// sig Router {
    ///   site: Site,
    ///   link: set Router
    /// }
    /// ```
    fn declarations(&self) -> Formula {
        // HQ + Sub in Site && no HQ & Sub
        let hq_sub = Expression::from(self.hq.clone())
            .union(Expression::from(self.sub.clone()))
            .in_set(Expression::from(self.site_sig.clone()))
            .and(
                Expression::from(self.hq.clone())
                    .intersection(Expression::from(self.sub.clone()))
                    .no()
            );

        // site is a function from Router to Site
        let site_fun = self.site.clone().function(
            Expression::from(self.router.clone()),
            Expression::from(self.site_sig.clone())
        );

        // link in Router->Router
        let links = Expression::from(self.link.clone()).in_set(
            Expression::from(self.router.clone()).product(Expression::from(self.router.clone()))
        );

        hq_sub.and(site_fun).and(links)
    }

    /// Returns the invariants predicate.
    /// ```alloy
    /// pred invariants() {
    ///   -- every site has at least one router
    ///   Site in Router.site
    ///
    ///   -- links are symmetric and non-reflexive
    ///   link = ~link
    ///   no link & iden
    /// }
    /// ```
    fn invariants(&self) -> Formula {
        let at_least_a_router = Expression::from(self.site_sig.clone()).in_set(
            Expression::from(self.router.clone()).join(Expression::from(self.site.clone()))
        );

        let links_symmetric = Expression::from(self.link.clone())
            .equals(Expression::from(self.link.clone()).transpose());

        let links_not_reflexive = Expression::from(self.link.clone())
            .intersection(Expression::IDEN)
            .no();

        at_least_a_router.and(links_symmetric).and(links_not_reflexive)
    }

    /// Returns the subsConnectedToHQ predicate.
    /// ```alloy
    /// pred subsConnectedToHQ() {
    ///   -- every sub location is connected to an HQ location
    ///   site.Sub in (site.HQ).link
    /// }
    /// ```
    fn subs_connected_to_hq(&self) -> Formula {
        Expression::from(self.site.clone())
            .join(Expression::from(self.sub.clone()))
            .in_set(
                Expression::from(self.site.clone())
                    .join(Expression::from(self.hq.clone()))
                    .join(Expression::from(self.link.clone()))
            )
    }

    /// Returns the connectedSites predicate.
    /// ```alloy
    /// pred connectedSites(sites: set Site) {
    ///   -- all sites in the given set are connected to each other
    ///   all s: sites | sites - s in ((site.s).^link).site
    /// }
    /// ```
    fn connected_sites(&self, sites: Expression) -> Formula {
        let s = Variable::unary("s");

        // Compute link closure (transitive or approximation)
        let closed = if self.closure_approx > 0 {
            // Approximation by repeated squaring
            let mut result = Expression::from(self.link.clone());
            let mut i = 1;
            while i < self.closure_approx {
                result = result.clone().union(result.clone().join(result.clone()));
                i *= 2;
            }
            result
        } else {
            // True transitive closure
            Expression::from(self.link.clone()).closure()
        };

        let s_reachable = Expression::from(self.site.clone())
            .join(Expression::from(s.clone()))
            .join(closed)
            .join(Expression::from(self.site.clone()));

        let f = sites.clone().difference(Expression::from(s.clone())).in_set(s_reachable);

        Formula::forall(Decls::from(Decl::one_of(s, sites)), f)
    }

    /// Returns the show predicate.
    /// ```alloy
    /// pred show() {
    ///   invariants() && subsConnectedToHQ() && connectedSites(Site)
    /// }
    /// ```
    fn show(&self) -> Formula {
        self.declarations()
            .and(self.invariants())
            .and(self.subs_connected_to_hq())
            .and(self.connected_sites(Expression::from(self.site_sig.clone())))
    }

    /// Creates a universe with n routers and n sites.
    /// The first n atoms are sites.
    fn universe(&self, n: usize) -> Result<Universe, kodkod_rs::error::KodkodError> {
        let mut atoms = Vec::new();
        for i in 0..n {
            atoms.push(format!("Site{}", i));
        }
        for i in 0..n {
            atoms.push(format!("Router{}", i));
        }
        let atom_strs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
        Universe::new(&atom_strs)
    }

    /// Returns bounds with the given number of hqs and subs.
    fn bounds(&self, hq_num: usize, sub_num: usize, router_num: usize)
        -> Result<Bounds, kodkod_rs::error::KodkodError>
    {
        let u = self.universe(router_num)?;
        self.bounds_with_universe(hq_num, sub_num, u)
    }

    /// Returns bounds with the given number of hqs and subs using the specified universe.
    fn bounds_with_universe(&self, hq_num: usize, sub_num: usize, u: Universe)
        -> Result<Bounds, kodkod_rs::error::KodkodError>
    {
        assert!(hq_num > 0 && sub_num > 0);

        let f = u.factory();
        let mut b = Bounds::new(u);

        let site_max = hq_num + sub_num - 1;
        let site0 = "Site0";
        let site_n = format!("Site{}", site_max);
        let site_hq = format!("Site{}", hq_num - 1);
        let site_sub = format!("Site{}", hq_num);
        let router0 = "Router0";
        let router_n = format!("Router{}", site_max);

        // Bind Site
        let sites = f.range(f.tuple(&[site0])?, f.tuple(&[&site_n])?)?;
        b.bound_exactly(&self.site_sig, sites.clone())?;

        // Bind HQ
        b.bound_exactly(&self.hq, f.range(f.tuple(&[site0])?, f.tuple(&[&site_hq])?)?)?;

        // Bind Sub
        b.bound_exactly(&self.sub, f.range(f.tuple(&[&site_sub])?, f.tuple(&[&site_n])?)?)?;

        // Bind Router
        let routers = f.range(f.tuple(&[router0])?, f.tuple(&[&router_n])?)?;
        b.bound_exactly(&self.router, routers.clone())?;

        // Bind link
        b.bound(&self.link, f.none(2), routers.clone().product(&routers)?)?;

        // Bind site field - each Router i is at Site i
        let mut router_location_tuples = Vec::new();
        for i in 0..=site_max {
            router_location_tuples.push(vec![format!("Router{}", i), format!("Site{}", i)]);
        }
        let router_location_refs: Vec<Vec<&str>> = router_location_tuples
            .iter()
            .map(|v| v.iter().map(|s| s.as_str()).collect())
            .collect();
        let router_location_slice_refs: Vec<&[&str]> = router_location_refs
            .iter()
            .map(|v| v.as_slice())
            .collect();
        b.bound_exactly(&self.site, f.tuple_set(&router_location_slice_refs)?)?;

        Ok(b)
    }
}

fn usage() -> ! {
    eprintln!("Usage: bigconfig <hq_num> <sub_num> <closure_approx> [partial_size]");
    eprintln!("  hq_num: number of HQ sites (> 0)");
    eprintln!("  sub_num: number of Sub sites (> 0)");
    eprintln!("  closure_approx: closure unwindings (0 for true closure)");
    eprintln!("  partial_size: size of partial instance (optional, 0 = none)");
    std::process::exit(1);
}

fn main() -> Result<(), kodkod_rs::error::KodkodError> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 4 {
        usage();
    }

    let hq: usize = args[1].parse().unwrap_or_else(|_| usage());
    let sub: usize = args[2].parse().unwrap_or_else(|_| usage());
    let closure_approx: usize = args[3].parse().unwrap_or_else(|_| usage());
    let partial: usize = if args.len() > 4 {
        args[4].parse().unwrap_or_else(|_| usage())
    } else {
        0
    };

    let model = Bigconfig::new(closure_approx);
    let solver = Solver::new(Options::default());
    let show = model.show();

    println!("\n=== Bigconfig (hq={}, sub={}, closure_approx={}, partial={}) ===\n",
             hq, sub, closure_approx, partial);

    if partial > 0 {
        // First solve with fewer subs
        let bounds = model.bounds(hq, sub - partial, hq + sub)?;
        let u = bounds.universe().clone();
        let sol = solver.solve(&show, &bounds)?;
        println!("Solved for {} hq and {} subs.", hq, sub - partial);
        println!("{sol:#?}");
        println!();

        // Then solve again with partial instance, reusing the universe
        println!("Solving again with a partial instance: {} hq and {} subs.", hq, sub);
        let mut bounds2 = model.bounds_with_universe(hq, sub, u)?;

        // Bind link using solution from first solve
        if let kodkod_rs::solver::Solution::Sat { instance, .. } = sol {
            if let Some(link_tuples) = instance.tuples(&model.link) {
                let link_upper = bounds2.upper_bound(&model.link).expect("link upper").clone();
                bounds2.bound(&model.link, link_tuples.clone(), link_upper)?;
            }
        }

        let sol2 = solver.solve(&show, &bounds2)?;
        println!("{sol2:#?}");
    } else {
        let bounds = model.bounds(hq, sub, hq + sub)?;
        let sol = solver.solve(&show, &bounds)?;
        println!("{sol:#?}");
    }

    Ok(())
}
