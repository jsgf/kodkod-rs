/*
 * Kodkod -- Copyright (c) 2005-2012, Emina Torlak
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */

#![allow(dead_code)]

// Encoding skeleton for bounded model checking of list operations.
// Some parts will change depending on whether we are performing
// verification, repair or synthesis.
//
// Following Java: kodkod.examples.bmc.ListEncoding

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{atom_as_str, Bounds, Universe};

pub struct ListEncoding {
    pub list: Relation,
    pub node: Relation,
    pub string: Relation,
    pub this_list: Relation,
    pub nil: Relation,
    pub head: Relation,
    pub next: Relation,
    pub data: Relation,
}

impl ListEncoding {
    pub fn new() -> Self {
        ListEncoding {
            list: Relation::unary("List"),
            node: Relation::unary("Node"),
            string: Relation::unary("String"),
            this_list: Relation::unary("this"),
            nil: Relation::unary("null"),
            head: Relation::binary("head"),
            next: Relation::binary("next"),
            data: Relation::binary("data"),
        }
    }

    pub fn invariants(
        &self,
        this_list: &Expression,
        next: &Expression,
        data: &Expression,
        head: &Expression,
    ) -> Formula {
        let node_expr: Expression = self.node.clone().into();
        let nil_expr: Expression = self.nil.clone().into();
        let string_expr: Expression = self.string.clone().into();
        let list_expr: Expression = self.list.clone().into();

        Formula::and_all(vec![
            this_list.clone().in_set(list_expr.clone()),                              // this in List
            this_list.clone().one(),                                                   // one this
            self.function(next, &node_expr, &node_expr.clone().union(nil_expr.clone())), // next in Node ->one Node + nil
            self.acyclic(next),                                                // no iden & ^next
            self.function(data, &node_expr, &string_expr.union(nil_expr.clone())), // data in Node ->one String + nil
            self.function(head, &list_expr, &node_expr.union(nil_expr)),      // head in List ->one Node + nil
        ])
    }

    pub fn pre(&self) -> Formula {
        let this_list_expr: Expression = self.this_list.clone().into();
        let head_expr: Expression = self.head.clone().into();
        let next_expr: Expression = self.next.clone().into();
        let data_expr: Expression = self.data.clone().into();
        let nil_expr: Expression = self.nil.clone().into();

        let this_head = this_list_expr.clone().join(head_expr.clone());
        Formula::and_all(vec![
            self.invariants(&this_list_expr, &next_expr, &data_expr, &head_expr),
            this_head.clone().equals(nil_expr.clone()).not(),           // this.head != null
            this_head.join(next_expr).equals(nil_expr).not(),   // this.head.next != null
        ])
    }

    pub fn near_node0(&self) -> Expression {
        let this_list_expr: Expression = self.this_list.clone().into();
        let head_expr: Expression = self.head.clone().into();
        this_list_expr.join(head_expr) // nearNode0 := this.head
    }

    pub fn mid_node0(&self) -> Expression {
        let next_expr: Expression = self.next.clone().into();
        self.near_node0().join(next_expr) // midNode0 := nearNode0.next
    }

    pub fn far_node0(&self) -> Expression {
        let next_expr: Expression = self.next.clone().into();
        self.mid_node0().join(next_expr) // farNode0 := midNode0.next
    }

    pub fn next0(&self) -> Expression {
        let next_expr: Expression = self.next.clone().into();
        // next0 := update(next, nearNode0 -> farNode0)
        // [fix] next0 := update(next, nearNode0 -> nil)
        next_expr.override_with(self.near_node0().product(self.far_node0()))
    }

    pub fn guard0(&self) -> Formula {
        let nil_expr: Expression = self.nil.clone().into();
        self.far_node0().equals(nil_expr).not() // guard0 := farNode0 != null
    }

    pub fn next1(&self) -> Expression {
        // next1 := update(next0, midNode0 -> nearNode0)
        self.next0().override_with(self.mid_node0().product(self.near_node0()))
    }

    pub fn near_node1(&self) -> Expression {
        self.mid_node0() // nearNode1 := midNode0
    }

    pub fn mid_node1(&self) -> Expression {
        self.far_node0() // midNode1 := farNode0
    }

    pub fn far_node1(&self) -> Expression {
        self.far_node0().join(self.next1()) // farNode1 := farNode0.next1
    }

    pub fn next2(&self) -> Expression {
        // next2 := phi(guard0, next1, next0)
        self.guard0().then_else(self.next1(), self.next0())
    }

    pub fn near_node2(&self) -> Expression {
        // nearNode2 := phi(guard0, nearNode1, nearNode0)
        self.guard0().then_else(self.near_node1(), self.near_node0())
    }

    pub fn mid_node2(&self) -> Expression {
        // midNode2 := phi(guard0, midNode1, midNode0)
        self.guard0().then_else(self.mid_node1(), self.mid_node0())
    }

    pub fn far_node2(&self) -> Expression {
        // farNode2 := phi(guard0, farNode1, farNode0)
        self.guard0().then_else(self.far_node1(), self.far_node0())
    }

    pub fn loop_guard(&self) -> Formula {
        let nil_expr: Expression = self.nil.clone().into();
        self.far_node2().equals(nil_expr) // assume farNode2 = null
    }

    pub fn next3(&self) -> Expression {
        // next3 = update(next2, midNode2 -> nearNode2)
        self.next2().override_with(self.mid_node2().product(self.near_node2()))
    }

    pub fn head0(&self) -> Expression {
        let this_list_expr: Expression = self.this_list.clone().into();
        let head_expr: Expression = self.head.clone().into();
        // head0 = update(head, this -> midNode2)
        head_expr.override_with(this_list_expr.product(self.mid_node2()))
    }

    pub fn post(&self) -> Formula {
        self.post_with(self.next3(), self.head0())
    }

    /// Post-condition with explicit next3 and head0 expressions
    /// This allows subclasses/compositions to override what next3 and head0 are
    pub fn post_with(&self, next3: Expression, head0: Expression) -> Formula {
        let this_list_expr: Expression = self.this_list.clone().into();
        let head_expr: Expression = self.head.clone().into();
        let next_expr: Expression = self.next.clone().into();
        let data_expr: Expression = self.data.clone().into();
        let nil_expr: Expression = self.nil.clone().into();

        // assert let nodes = this.head.*next,
        let nodes = this_list_expr.clone().join(head_expr.clone()).join(next_expr.clone().reflexive_closure());
        // nodes' = this.head0.*next3,
        let nodes_prime = this_list_expr.clone().join(head0.clone()).join(next3.clone().reflexive_closure());
        // ns = nodes - nil |
        let ns = nodes.clone().difference(nil_expr);
        let ns2 = ns.clone().product(ns);

        Formula::and_all(vec![
            // invariants(this, next3, data, head0) &&
            self.invariants(&this_list_expr, &next3, &data_expr, &head0),
            // nodes' = nodes &&
            nodes_prime.equals(nodes.clone()),
            // next3 & (ns -> ns) = ~(next & (ns -> ns))
            next3.intersection(ns2.clone()).equals(next_expr.intersection(ns2).transpose()),
        ])
    }

    pub fn bounds(&self, size: usize) -> Bounds {
        let u = self.universe(size).expect("Failed to create universe");
        let mut b = Bounds::new(u);
        let t = b.universe().factory();
        let max = size - 1;

        // In Java, b.bound(rel, set) means lower=empty, upper=set
        let list_set = t.tuple_set(&[&["l0"]]).unwrap();
        b.bound(&self.list, t.none(1), list_set).unwrap();

        let node_set = t.range(t.tuple(&["n0"]).unwrap(), t.tuple(&[&format!("n{max}")]).unwrap()).unwrap();
        b.bound(&self.node, t.none(1), node_set).unwrap();

        let string_set = t.range(t.tuple(&["s0"]).unwrap(), t.tuple(&[&format!("s{max}")]).unwrap()).unwrap();
        b.bound(&self.string, t.none(1), string_set).unwrap();

        let this_list_set = b.upper_bound(&self.list).unwrap().clone();
        b.bound(&self.this_list, t.none(1), this_list_set).unwrap();

        b.bound_exactly(&self.nil, t.tuple_set(&[&["nil"]]).unwrap()).unwrap();

        // Java uses one-arg b.bound() which sets lower=empty, upper=set
        let mut ran = t.range(t.tuple(&["n0"]).unwrap(), t.tuple(&[&format!("n{max}")]).unwrap()).unwrap();
        ran.add(t.tuple(&["nil"]).unwrap()).unwrap();
        let head_bound = b.upper_bound(&self.list).unwrap().product(&ran).unwrap();
        b.bound(&self.head, t.none(2), head_bound).unwrap();

        let mut ran = t.range(t.tuple(&["n0"]).unwrap(), t.tuple(&[&format!("n{max}")]).unwrap()).unwrap();
        ran.add(t.tuple(&["nil"]).unwrap()).unwrap();
        let next_bound = b.upper_bound(&self.node).unwrap().product(&ran).unwrap();
        b.bound(&self.next, t.none(2), next_bound).unwrap();

        let mut ran = t.range(t.tuple(&["s0"]).unwrap(), t.tuple(&[&format!("s{max}")]).unwrap()).unwrap();
        ran.add(t.tuple(&["nil"]).unwrap()).unwrap();
        let data_bound = b.upper_bound(&self.node).unwrap().product(&ran).unwrap();
        b.bound(&self.data, t.none(2), data_bound).unwrap();

        b
    }

    pub fn universe(&self, size: usize) -> Result<Universe, kodkod_rs::KodkodError> {
        let mut elts = Vec::with_capacity(2 + size * 2);
        elts.push("l0");
        let mut nodes = Vec::with_capacity(size);
        for i in 0..size {
            nodes.push(format!("n{i}"));
        }
        let mut strings = Vec::with_capacity(size);
        for i in 0..size {
            strings.push(format!("s{i}"));
        }
        elts.extend(nodes.iter().map(|s| s.as_str()));
        elts.extend(strings.iter().map(|s| s.as_str()));
        elts.push("nil");
        Universe::new(&elts)
    }

    /**
     * Returns a formula stating that the given expression is acyclic.
     * @return {f: Formula | f <=> no ^expr & iden}
     */
    pub fn acyclic(&self, expr: &Expression) -> Formula {
        // Special handling for relations that enables better symmetry breaking
        use kodkod_rs::ast::ExpressionInner;
        match &*expr.inner() {
            ExpressionInner::Relation(r) => r.clone().acyclic(),
            _ => {
                assert_eq!(expr.arity(), 2, "Acyclic requires binary expression");
                expr.clone().closure().intersection(Expression::IDEN).no()
            }
        }
    }

    /**
     * Returns a formula stating that the given relation is a total function
     * with the specified domain and range.
     * @return {f: Formula | f <=> expr in domain->range && all v: domain | one v.expr }
     */
    pub fn function(&self, expr: &Expression, domain: &Expression, range: &Expression) -> Formula {
        // Special handling for relations that enables better symmetry breaking
        use kodkod_rs::ast::ExpressionInner;
        match &*expr.inner() {
            ExpressionInner::Relation(r) => r.clone().function(domain.clone(), range.clone()),
            _ => {
                assert_eq!(domain.arity(), 1, "Domain must be unary");
                assert_eq!(range.arity(), 1, "Range must be unary");
                assert_eq!(expr.arity(), 2, "Function requires binary expression");

                // expr in domain->range
                let domain_constraint = expr.clone().in_set(domain.clone().product(range.clone()));

                // all v: domain | one v.expr
                let v = Variable::unary("v");
                let v_expr = Expression::from(v.clone());
                let decls = Decls::from(Decl::one_of(v, domain.clone()));
                let fun_constraint = Formula::forall(decls, v_expr.join(expr.clone()).one());

                // expr in domain->range && all v: domain | one v.expr
                domain_constraint.and(fun_constraint)
            }
        }
    }

    /// Copy tuples from one TupleSet to another (for different TupleFactories)
    /// Following Java: ListEncoding.copyFrom
    pub fn copy_from(&self, tf: &kodkod_rs::instance::TupleFactory, other: &kodkod_rs::instance::TupleSet) -> kodkod_rs::instance::TupleSet {
        let arity = other.arity();
        let mut out = tf.none(arity);
        for tuple in other.iter() {
            let atoms: Vec<&str> = (0..arity)
                .filter_map(|i| tuple.atom(i).and_then(atom_as_str))
                .collect();
            if atoms.len() == arity {
                if let Ok(t) = tf.tuple(&atoms) {
                    let _ = out.add(t);
                }
            }
        }
        out
    }
}
