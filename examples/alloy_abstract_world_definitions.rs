use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::Solver;

/// KK encoding of mondex/a.als together with mondex/common.als.
struct AbstractWorldDefinitions {
    // relations declared in common.als
    coin: Relation,
    purse: Relation,
    transfer_details: Relation,
    from: Relation,
    to: Relation,
    value: Relation,

    // relations declared in a.als
    ab_world: Relation,
    ab_purse: Relation,
    a_null_in: Relation,
    ain: Relation,
    aout: Relation,
    a_null_out: Relation,
    ab_auth_purse: Relation,
    ab_balance: Relation,
    ab_lost: Relation,
}

impl AbstractWorldDefinitions {
    fn new() -> Self {
        Self {
            coin: Relation::unary("Coin"),
            purse: Relation::unary("Purse"),
            transfer_details: Relation::unary("TransferDetails"),
            from: Relation::binary("from"),
            to: Relation::binary("to"),
            value: Relation::binary("value"),

            ab_world: Relation::unary("AbWorld"),
            ab_purse: Relation::unary("AbPurse"),
            a_null_in: Relation::unary("aNullIn"),
            ain: Relation::unary("AIN"),
            aout: Relation::unary("AOUT"),
            a_null_out: Relation::unary("aNullOut"),
            ab_auth_purse: Relation::binary("abAuthPurse"),
            ab_balance: Relation::ternary("abBalance"),
            ab_lost: Relation::ternary("abLost"),
        }
    }

    /// Returns the declaration constraints for mondex/common.als
    fn decls(&self) -> Formula {
        let f0 = self.from.clone().function(
            Expression::from(self.transfer_details.clone()),
            Expression::from(self.purse.clone()),
        );
        let f1 = self.to.clone().function(
            Expression::from(self.transfer_details.clone()),
            Expression::from(self.purse.clone()),
        );
        let f2 = Expression::from(self.value.clone()).in_set(
            Expression::from(self.transfer_details.clone())
                .product(Expression::from(self.coin.clone())),
        );

        let f3 = Expression::from(self.ab_purse.clone()).in_set(Expression::from(self.purse.clone()));
        let f4 = Expression::from(self.ab_auth_purse.clone()).in_set(
            Expression::from(self.ab_world.clone()).product(Expression::from(self.ab_purse.clone())),
        );
        let f5 = Expression::from(self.ab_balance.clone()).in_set(
            Expression::from(self.ab_purse.clone())
                .product(Expression::from(self.coin.clone()))
                .product(Expression::from(self.ab_world.clone())),
        );
        let f6 = Expression::from(self.ab_lost.clone()).in_set(
            Expression::from(self.ab_purse.clone())
                .product(Expression::from(self.coin.clone()))
                .product(Expression::from(self.ab_world.clone())),
        );
        let f7 = Expression::from(self.ain.clone()).in_set(
            Expression::from(self.a_null_in.clone())
                .union(Expression::from(self.transfer_details.clone())),
        );
        let f8 = Expression::from(self.a_null_out.clone()).in_set(Expression::from(self.aout.clone()));

        Formula::and_all(vec![f0, f1, f2, f3, f4, f5, f6, f7, f8])
    }

    /// Returns the application of the Abstract predicate.
    fn abstract_pred(&self, s: Expression) -> Formula {
        let e0 = s.clone()
            .join(Expression::from(self.ab_auth_purse.clone()))
            .join(Expression::from(self.ab_balance.clone()))
            .join(s.clone())
            .intersection(
                s.clone()
                    .join(Expression::from(self.ab_auth_purse.clone()))
                    .join(Expression::from(self.ab_lost.clone()))
                    .join(s.clone()),
            );
        let f0 = e0.no();

        let e1 = s.clone()
            .join(Expression::from(self.ab_auth_purse.clone()))
            .product(Expression::UNIV);
        let e2 = e1.intersection(
            Expression::from(self.ab_balance.clone())
                .union(Expression::from(self.ab_lost.clone()))
                .join(s.clone()),
        );
        let f1 = e2.clone().in_set(
            Expression::from(self.ab_purse.clone()).product(Expression::from(self.coin.clone())),
        );

        let c = Variable::unary("c");
        let f2 = Formula::forall(
            Decls::from(Decl::one_of(c.clone(), Expression::from(self.coin.clone()))),
            e2.join(Expression::from(c)).lone(),
        );

        Formula::and_all(vec![f0, f1, f2])
    }

    /// Returns the application of the XiAbPurse predicate.
    fn xi_ab_purse(&self, s: Expression, sprime: Expression, a: Expression) -> Formula {
        let a_restrict = a.product(Expression::UNIV);
        let f0 = a_restrict
            .clone()
            .intersection(Expression::from(self.ab_balance.clone()).join(s.clone()))
            .equals(a_restrict.clone().intersection(
                Expression::from(self.ab_balance.clone()).join(sprime.clone()),
            ));
        let f1 = a_restrict
            .clone()
            .intersection(Expression::from(self.ab_lost.clone()).join(s))
            .equals(a_restrict
                .intersection(Expression::from(self.ab_lost.clone()).join(sprime)));
        f0.and(f1)
    }

    /// Returns the application of the totalBalance function.
    fn total_balance(&self, s: Expression) -> Expression {
        s.clone()
            .join(Expression::from(self.ab_auth_purse.clone()))
            .join(Expression::from(self.ab_balance.clone()))
            .join(s)
    }

    /// Returns the application of the totalLost function.
    fn total_lost(&self, s: Expression) -> Expression {
        s.clone()
            .join(Expression::from(self.ab_auth_purse.clone()))
            .join(Expression::from(self.ab_lost.clone()))
            .join(s)
    }

    /// Returns the application of the NoValueCreation predicate.
    fn no_value_creation(&self, s: Expression, sprime: Expression) -> Formula {
        self.total_balance(sprime).in_set(self.total_balance(s))
    }

    /// Returns the application of the AllValueAccounted predicate.
    fn all_value_accounted(&self, s: Expression, sprime: Expression) -> Formula {
        self.total_balance(sprime.clone())
            .union(self.total_lost(sprime))
            .in_set(self.total_balance(s.clone()).union(self.total_lost(s)))
    }

    /// Returns the application of the Authentic predicate.
    fn authentic(&self, s: Expression, p: Expression) -> Formula {
        p.in_set(s.join(Expression::from(self.ab_auth_purse.clone())))
    }

    /// Returns the application of the SufficientFundsProperty predicate.
    fn sufficient_funds_property(&self, s: Expression, t: Expression) -> Formula {
        t.clone()
            .join(Expression::from(self.value.clone()))
            .in_set(
                t.join(Expression::from(self.from.clone()))
                    .join(Expression::from(self.ab_balance.clone()))
                    .join(s),
            )
    }

    /// Returns the application of the AbOp predicate.
    fn ab_op(&self, a_out: Expression) -> Formula {
        a_out.equals(Expression::from(self.a_null_out.clone()))
    }

    /// Returns the application of the AbIgnore predicate.
    fn ab_ignore(&self, s: Expression, sprime: Expression, a_out: Expression) -> Formula {
        let f0 = self.ab_op(a_out);
        let f1 = s.clone()
            .join(Expression::from(self.ab_auth_purse.clone()))
            .equals(sprime.clone().join(Expression::from(self.ab_auth_purse.clone())));
        let f2 = self.xi_ab_purse(
            s.clone(),
            sprime,
            s.join(Expression::from(self.ab_auth_purse.clone())),
        );
        Formula::and_all(vec![f0, f1, f2])
    }

    /// Returns the application of the AbWorldSecureOp predicate.
    fn ab_world_secure_op(
        &self,
        s: Expression,
        sprime: Expression,
        a_in: Expression,
        a_out: Expression,
    ) -> Formula {
        let f0 = self.ab_op(a_out);
        let f1 = a_in.clone().in_set(Expression::from(self.transfer_details.clone()));

        let e0 = a_in.clone().join(Expression::from(self.from.clone()));
        let e1 = a_in.join(Expression::from(self.to.clone()));
        let e2 = s.clone()
            .join(Expression::from(self.ab_auth_purse.clone()))
            .difference(e0.clone())
            .difference(e1.clone());
        let e3 = sprime
            .clone()
            .join(Expression::from(self.ab_auth_purse.clone()))
            .difference(e0)
            .difference(e1);
        let f2 = e2.clone().equals(e3);

        let f3 = self.xi_ab_purse(s, sprime, e2);

        Formula::and_all(vec![f0, f1, f2, f3])
    }

    /// Returns the application of the AbTransferOkay predicate.
    fn ab_transfer_okay(
        &self,
        s: Expression,
        sprime: Expression,
        a_in: Expression,
        a_out: Expression,
    ) -> Formula {
        let e0 = a_in.clone().join(Expression::from(self.from.clone()));
        let e1 = a_in.clone().join(Expression::from(self.to.clone()));

        let f0 = self.ab_world_secure_op(s.clone(), sprime.clone(), a_in.clone(), a_out);
        let f1 = self.authentic(s.clone(), e0.clone());
        let f2 = self.authentic(s.clone(), e1.clone());
        let f3 = self.sufficient_funds_property(s.clone(), a_in.clone());
        let f4 = e0.clone().intersection(e1.clone()).no();

        let f5 = e0.clone()
            .join(Expression::from(self.ab_balance.clone()))
            .join(sprime.clone())
            .equals(e0.clone()
                .join(Expression::from(self.ab_balance.clone()))
                .join(s.clone())
                .difference(a_in.clone().join(Expression::from(self.value.clone()))));
        let f6 = e0.clone()
            .join(Expression::from(self.ab_lost.clone()))
            .join(sprime.clone())
            .equals(e0.clone().join(Expression::from(self.ab_lost.clone())).join(s.clone()));
        let f7 = e1.clone()
            .join(Expression::from(self.ab_balance.clone()))
            .join(sprime.clone())
            .equals(e1.clone()
                .join(Expression::from(self.ab_balance.clone()))
                .join(s.clone())
                .union(a_in.join(Expression::from(self.value.clone()))));
        let f8 = e1.clone()
            .join(Expression::from(self.ab_lost.clone()))
            .join(sprime.clone())
            .equals(e1.clone().join(Expression::from(self.ab_lost.clone())).join(s));

        let f9 = self.authentic(sprime.clone(), e0);
        let f10 = self.authentic(sprime, e1);

        Formula::and_all(vec![f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10])
    }

    /// Returns the application of the AbTransferLost predicate.
    fn ab_transfer_lost(
        &self,
        s: Expression,
        sprime: Expression,
        a_in: Expression,
        a_out: Expression,
    ) -> Formula {
        let e0 = a_in.clone().join(Expression::from(self.from.clone()));
        let e1 = a_in.clone().join(Expression::from(self.to.clone()));

        let f0 = self.ab_world_secure_op(s.clone(), sprime.clone(), a_in.clone(), a_out);
        let f1 = self.authentic(s.clone(), e0.clone());
        let f2 = self.authentic(s.clone(), e1.clone());
        let f3 = self.sufficient_funds_property(s.clone(), a_in.clone());
        let f4 = e0.clone().intersection(e1.clone()).no();

        let f5 = e0.clone()
            .join(Expression::from(self.ab_balance.clone()))
            .join(sprime.clone())
            .equals(e0.clone()
                .join(Expression::from(self.ab_balance.clone()))
                .join(s.clone())
                .difference(a_in.clone().join(Expression::from(self.value.clone()))));
        let f6 = e0.clone()
            .join(Expression::from(self.ab_lost.clone()))
            .join(sprime.clone())
            .equals(e0.clone()
                .join(Expression::from(self.ab_lost.clone()))
                .join(s.clone())
                .union(a_in.join(Expression::from(self.value.clone()))));

        let f7 = self.xi_ab_purse(s, sprime.clone(), e1.clone());

        let f8 = self.authentic(sprime.clone(), e0);
        let f9 = self.authentic(sprime, e1);

        Formula::and_all(vec![f0, f1, f2, f3, f4, f5, f6, f7, f8, f9])
    }

    /// Returns the application of the AbTransfer predicate.
    fn ab_transfer(
        &self,
        s: Expression,
        sprime: Expression,
        a_in: Expression,
        a_out: Expression,
    ) -> Formula {
        self.ab_transfer_okay(s.clone(), sprime.clone(), a_in.clone(), a_out.clone())
            .or(self.ab_transfer_lost(s.clone(), sprime.clone(), a_in.clone(), a_out.clone()))
            .or(self.ab_ignore(s, sprime, a_out))
    }

    /// Returns the A241 assertion.
    fn a241(&self) -> Formula {
        let s = Variable::unary("s");
        let sprime = Variable::unary("s'");
        let a_in = Variable::unary("a_in");
        let a_out = Variable::unary("a_out");

        let f0 = self
            .abstract_pred(Expression::from(s.clone()))
            .and(self.abstract_pred(Expression::from(sprime.clone())))
            .and(self.ab_transfer(
                Expression::from(s.clone()),
                Expression::from(sprime.clone()),
                Expression::from(a_in.clone()),
                Expression::from(a_out.clone()),
            ));
        let f1 = self
            .no_value_creation(Expression::from(s.clone()), Expression::from(sprime.clone()))
            .and(self.all_value_accounted(
                Expression::from(s.clone()),
                Expression::from(sprime.clone()),
            ));
        let f2 = Formula::forall(
            Decls::from(Decl::one_of(s.clone(), Expression::from(self.ab_world.clone())))
                .and(Decl::one_of(sprime.clone(), Expression::from(self.ab_world.clone())))
                .and(Decl::one_of(a_in, Expression::from(self.ain.clone())))
                .and(Decl::one_of(a_out, Expression::from(self.aout.clone()))),
            f0.implies(f1),
        );

        f2
    }

    /// Returns the AbOp_total assertion.
    fn ab_op_total(&self) -> Formula {
        let a = Variable::unary("a");
        let a_in = Variable::unary("a_in");

        let f0 = self.abstract_pred(Expression::from(a.clone())).implies(
            self.ab_ignore(
                Expression::from(a.clone()),
                Expression::from(a.clone()),
                Expression::from(self.a_null_out.clone()),
            )
            .and(self.ab_transfer(
                Expression::from(a.clone()),
                Expression::from(a.clone()),
                Expression::from(a_in.clone()),
                Expression::from(self.a_null_out.clone()),
            )),
        );
        let f1 = Formula::forall(
            Decls::from(Decl::one_of(a, Expression::from(self.ab_world.clone())))
                .and(Decl::one_of(a_in, Expression::from(self.ain.clone()))),
            f0,
        );

        f1
    }

    /// Returns the AbIgnore_inv assertion.
    fn ab_ignore_inv(&self) -> Formula {
        let a = Variable::unary("a");
        let aprime = Variable::unary("a'");
        let a_out = Variable::unary("a_out");

        let f0 = self
            .abstract_pred(Expression::from(a.clone()))
            .and(self.ab_ignore(
                Expression::from(a.clone()),
                Expression::from(aprime.clone()),
                Expression::from(a_out.clone()),
            ))
            .implies(self.abstract_pred(Expression::from(aprime.clone())));
        let f1 = Formula::forall(
            Decls::from(Decl::one_of(a, Expression::from(self.ab_world.clone())))
                .and(Decl::one_of(aprime, Expression::from(self.ab_world.clone())))
                .and(Decl::one_of(a_out, Expression::from(self.aout.clone()))),
            f0,
        );

        f1
    }

    /// Returns the AbTransfer_inv assertion.
    fn ab_transfer_inv(&self) -> Formula {
        let a = Variable::unary("a");
        let aprime = Variable::unary("a'");
        let a_in = Variable::unary("a_in");
        let a_out = Variable::unary("a_out");

        let f0 = self
            .abstract_pred(Expression::from(a.clone()))
            .and(self.ab_transfer(
                Expression::from(a.clone()),
                Expression::from(aprime.clone()),
                Expression::from(a_in.clone()),
                Expression::from(a_out.clone()),
            ))
            .implies(self.abstract_pred(Expression::from(aprime.clone())));
        let f1 = Formula::forall(
            Decls::from(Decl::one_of(a, Expression::from(self.ab_world.clone())))
                .and(Decl::one_of(aprime, Expression::from(self.ab_world.clone())))
                .and(Decl::one_of(a_in, Expression::from(self.ain.clone())))
                .and(Decl::one_of(a_out, Expression::from(self.aout.clone()))),
            f0,
        );

        f1
    }

    /// Returns decls() && !A241()
    fn check_a241(&self) -> Formula {
        self.decls().and(self.a241().not())
    }

    /// Returns decls() && !AbOp_total()
    fn check_ab_op_total(&self) -> Formula {
        self.decls().and(self.ab_op_total().not())
    }

    /// Returns decls() && !AbIgnore_inv()
    fn check_ab_ignore_inv(&self) -> Formula {
        self.decls().and(self.ab_ignore_inv().not())
    }

    /// Returns decls() && !AbTransfer_inv()
    fn check_ab_transfer_inv(&self) -> Formula {
        self.decls().and(self.ab_transfer_inv().not())
    }

    /// Returns the bounds for the given scope.
    fn bounds(&self, scope: usize) -> Result<Bounds, kodkod_rs::error::KodkodError> {
        let mut atoms = Vec::new();

        let max = scope - 1;
        for i in 0..scope {
            atoms.push(format!("Coin{}", i));
        }
        for i in 0..scope {
            atoms.push(format!("Purse{}", i));
        }
        for i in 0..scope {
            atoms.push(format!("TransferDetails{}", i));
        }
        atoms.push("aNullIn".to_string());
        for i in 0..scope {
            atoms.push(format!("AbWorld{}", i));
        }
        for i in 0..max {
            atoms.push(format!("AOUT{}", i));
        }
        atoms.push("aNullOut".to_string());

        let atom_strs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
        let universe = Universe::new(&atom_strs)?;
        let factory = universe.factory();
        let mut bounds = Bounds::new(universe);

        let coin_bound = factory.range(
            factory.tuple(&["Coin0"])?,
            factory.tuple(&[&format!("Coin{}", max)])?
        )?;
        bounds.bound(&self.coin, factory.none(1), coin_bound.clone())?;

        let purse_bound = factory.range(
            factory.tuple(&["Purse0"])?,
            factory.tuple(&[&format!("Purse{}", max)])?
        )?;
        bounds.bound(&self.purse, factory.none(1), purse_bound.clone())?;

        let transfer_details_bound = factory.range(
            factory.tuple(&["TransferDetails0"])?,
            factory.tuple(&[&format!("TransferDetails{}", max)])?
        )?;
        bounds.bound(&self.transfer_details, factory.none(1), transfer_details_bound.clone())?;

        let ab_world_bound = factory.range(
            factory.tuple(&["AbWorld0"])?,
            factory.tuple(&[&format!("AbWorld{}", max)])?
        )?;
        bounds.bound(&self.ab_world, factory.none(1), ab_world_bound.clone())?;

        bounds.bound(&self.ab_purse, factory.none(1), purse_bound.clone())?;

        let aout_bound = factory.range(
            factory.tuple(&["AOUT0"])?,
            factory.tuple(&["aNullOut"])?
        )?;
        bounds.bound(&self.aout, factory.none(1), aout_bound)?;

        let ain_bound = factory.range(
            factory.tuple(&["TransferDetails0"])?,
            factory.tuple(&["aNullIn"])?
        )?;
        bounds.bound(&self.ain, factory.none(1), ain_bound)?;

        bounds.bound_exactly(&self.a_null_in, factory.set_of("aNullIn")?)?;
        bounds.bound_exactly(&self.a_null_out, factory.set_of("aNullOut")?)?;

        bounds.bound(
            &self.from,
            factory.none(2),
            transfer_details_bound.clone().product(&purse_bound)?
        )?;
        bounds.bound(
            &self.to,
            factory.none(2),
            transfer_details_bound.clone().product(&purse_bound)?
        )?;
        bounds.bound(
            &self.value,
            factory.none(2),
            transfer_details_bound.product(&coin_bound)?
        )?;

        let ab_purse_upper = bounds.upper_bound(&self.ab_purse)
            .expect("ab_purse should have upper bound")
            .clone();
        bounds.bound(
            &self.ab_auth_purse,
            factory.none(2),
            ab_world_bound.clone().product(&ab_purse_upper)?
        )?;

        bounds.bound(
            &self.ab_balance,
            factory.none(3),
            ab_purse_upper.clone().product(&coin_bound)?.product(&ab_world_bound)?
        )?;
        bounds.bound(
            &self.ab_lost,
            factory.none(3),
            ab_purse_upper.product(&coin_bound)?.product(&ab_world_bound)?
        )?;

        Ok(bounds)
    }
}

fn usage() -> ! {
    eprintln!("Usage: abstract_world_definitions <assertion> <scope>");
    eprintln!("  assertion: A241 | AbOp_total | AbIgnore_inv | AbTransfer_inv");
    eprintln!("  scope: universe size (>= 1)");
    std::process::exit(1);
}

fn main() -> Result<(), kodkod_rs::error::KodkodError> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        usage();
    }

    let assertion = &args[1];
    let scope: usize = args[2].parse().unwrap_or_else(|_| {
        eprintln!("Invalid scope");
        usage()
    });
    if scope < 1 {
        usage();
    }

    let model = AbstractWorldDefinitions::new();
    let solver = Solver::new(kodkod_rs::solver::Options::default());

    let formula = match assertion.as_str() {
        "A241" => model.check_a241(),
        "AbOp_total" => model.check_ab_op_total(),
        "AbIgnore_inv" => model.check_ab_ignore_inv(),
        "AbTransfer_inv" => model.check_ab_transfer_inv(),
        _ => {
            eprintln!("Invalid assertion: {}", assertion);
            usage()
        }
    };

    let bounds = model.bounds(scope)?;

    println!("\n=== AbstractWorldDefinitions (assertion={}, scope={}) ===\n", assertion, scope);
    println!("checking {}", assertion);

    let solution = solver.solve(&formula, &bounds)?;
    println!("{solution:#?}");

    Ok(())
}
