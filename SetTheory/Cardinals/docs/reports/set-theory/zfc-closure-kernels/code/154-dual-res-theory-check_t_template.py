#!/usr/bin/env python3
"""Exact finite Boolean check of the literal two-time K-template reduction.

This is not a finite model of the complete changed calculus.  It checks a
local algebraic lemma with every relevant atomic value left symbolic,
using reduced ordered binary decision diagrams and no external libraries.
The unbounded-domain countermodel proof is in t_countermodel.md.
"""

from functools import lru_cache
from itertools import product
import json
from pathlib import Path


class BDD:
    def __init__(self):
        self.nodes = [None, None]
        self.unique = {}
        self.names = []

    def mk(self, v, lo, hi):
        if lo == hi:
            return lo
        key = (v, lo, hi)
        if key not in self.unique:
            self.unique[key] = len(self.nodes)
            self.nodes.append(key)
        return self.unique[key]

    def variable(self, name):
        v = len(self.names)
        self.names.append(name)
        return self.mk(v, 0, 1)

    @lru_cache(None)
    def neg(self, a):
        if a < 2:
            return 1 - a
        v, lo, hi = self.nodes[a]
        return self.mk(v, self.neg(lo), self.neg(hi))

    @lru_cache(None)
    def conj(self, a, b):
        if a == 0 or b == 0:
            return 0
        if a == 1:
            return b
        if b == 1 or a == b:
            return a
        av, al, ah = self.nodes[a]
        bv, bl, bh = self.nodes[b]
        if av == bv:
            return self.mk(av, self.conj(al, bl), self.conj(ah, bh))
        if av < bv:
            return self.mk(av, self.conj(al, b), self.conj(ah, b))
        return self.mk(bv, self.conj(a, bl), self.conj(a, bh))

    def disj(self, a, b):
        return self.neg(self.conj(self.neg(a), self.neg(b)))

    def imp(self, a, b):
        return self.disj(self.neg(a), b)

    def all(self, xs):
        out = 1
        for x in xs:
            out = self.conj(out, x)
        return out

    def any(self, xs):
        return self.neg(self.all(self.neg(x) for x in xs))


def verify(coincident, flags):
    d = BDD()
    a, b, c = (0, 0, 1) if coincident else (0, 1, 2)
    ncoord = c + 1
    values = range(2)
    states = list(product(values, repeat=ncoord))
    q = {(t, x, y): d.variable(f'q{t}_{x}{y}')
         for t, x, y in product(range(2), values, values)}
    r = {(t, y, z): d.variable(f'r{t}_{y}{z}')
         for t, y, z in product(range(2), values, values)}
    s = {(t, x, y, z): d.variable(f's{t}_{x}{y}{z}')
         for t, x, y, z in product(range(2), values, values, values)}

    def subst(v, k, x):
        w = list(v)
        w[k] = x
        return tuple(w)

    def Q(k, t, v, body):
        times = range(t, 2) if flags[k] else (t,)
        return d.all(body(tt, subst(v, k, x)) for tt in times for x in values)

    def All(k, v, body):
        return d.all(body(subst(v, k, x)) for x in values)

    def Ex(k, v, body):
        return d.any(body(subst(v, k, x)) for x in values)

    def N(t, x):
        return d.imp(x, t)  # F is false initially and true terminally.

    def matrix(t, v):
        return q[t, v[a], v[b]]

    def rel(t, v):
        return r[t, v[b], v[c]]

    def subset(t, v):
        return 1 if coincident else s[t, v[a], v[b], v[c]]

    @lru_cache(None)
    def w(t, v):
        return Q(b, t, v, lambda tt, vv: d.imp(
            matrix(tt, vv), N(tt, Q(b, tt, vv, lambda t2, v2:
                d.imp(matrix(t2, v2), N(t2, rel(t2, v2)))))))

    @lru_cache(None)
    def u(t, v):
        return Q(a, t, v, lambda tt, vv: d.imp(subset(tt, vv), w(tt, vv)))

    @lru_cache(None)
    def h(t, v):
        return Q(b, t, v, lambda tt, vv: d.imp(rel(tt, vv),
            N(tt, Q(a, tt, vv, lambda t2, v2:
                d.imp(matrix(t2, v2), N(t2, u(t2, v2)))))))

    def seed(t, v):
        return N(t, Q(c, t, v, lambda tt, vv: d.imp(h(tt, vv), N(tt, w(tt, vv)))))

    @lru_cache(None)
    def W(v):
        return d.imp(Ex(b, v, lambda vv: matrix(0, vv)),
                     Ex(b, v, lambda vv: d.conj(matrix(0, vv), rel(0, vv))))

    @lru_cache(None)
    def U(v):
        return All(a, v, lambda vv: d.imp(subset(0, vv), W(vv)))

    @lru_cache(None)
    def H(v):
        return All(b, v, lambda vv: d.imp(rel(0, vv),
            Ex(a, vv, lambda v2: d.conj(matrix(0, v2), U(v2)))))

    checks = 0
    for v in states:
        assert w(1, v) == u(1, v) == h(1, v) == seed(1, v) == 1
        assert w(0, v) == W(v)
        assert u(0, v) == U(v)
        assert h(0, v) == H(v)
        assert seed(0, v) == Ex(c, v, lambda vv: d.conj(H(vv), W(vv)))
        checks += 8
        if coincident:
            assert U(v) == W(v)
            checks += 1
    return {
        'coincident_input_output_labels': coincident,
        'time_advancing_quantifiers': list(flags),
        'symbolic_boolean_variables': len(d.names),
        'all_valuations_represented': 2 ** len(d.names),
        'checked_BDD_equalities': checks,
        'BDD_nodes': len(d.nodes),
    }


def main():
    rows = []
    for coincident in (False, True):
        for flags in product((False, True), repeat=2 if coincident else 3):
            rows.append(verify(coincident, flags))
    dual_checks = 0
    for advances in (False, True):
        d = BDD()
        A = {(t, x): d.variable(f'A{t}_{x}') for t, x in product(range(2), repeat=2)}
        def Q(t, body):
            return d.all(body(tt, y) for tt in (range(t, 2) if advances else (t,))
                         for y in range(2))
        def X(t):
            return d.imp(Q(t, lambda tt, y: d.imp(A[tt, y], tt)), t)
        for t, x in product(range(2), repeat=2):
            assert d.imp(A[t, x], Q(t, lambda tt, y: X(tt))) == 1
            dual_checks += 1
    out = {
        'status': 'EXACT_BOOLEAN_TEMPLATE_PASS',
        'scope': 'Local literal-template identity over a two-element coordinate domain; '
                 'all matrix, relation, and abstract subset values symbolic. '
                 'This is not a finite model of the full theory. The unbounded '
                 'countermodel is proved in t_countermodel.md.',
        'cases': rows,
        'total_BDD_equalities': sum(r['checked_BDD_equalities'] for r in rows),
        'dual_rho6_BDD_equalities': dual_checks,
    }
    p = Path(__file__).with_name('t_template_receipt.json')
    p.write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps({k: v for k, v in out.items() if k != 'cases'}, indent=2))


if __name__ == '__main__':
    main()
