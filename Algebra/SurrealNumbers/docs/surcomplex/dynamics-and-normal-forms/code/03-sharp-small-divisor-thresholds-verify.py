#!/usr/bin/env python3
"""Exact finite-jet checks for Holomorphic Dynamics on Surcomplex Halos.

Requires Python 3.10+ and SymPy.  This is a sparse polynomial jet algebra,
not an implementation of arbitrary Hahn supports and not a proof assistant.
Parameters are truncated by TOTAL PARAMETER DEGREE, not by Hahn valuation.
All coefficients used in the checks lie in Q(i); no floating-point tests occur.
"""
from __future__ import annotations
from dataclasses import dataclass
from functools import cached_property
from pathlib import Path
import argparse
import json
import math
import sympy as sp


@dataclass(frozen=True)
class Ring:
    params: tuple[str, ...]
    coords: tuple[str, ...]
    depth: int

    def __post_init__(self):
        if self.depth < 1 or not self.coords or not self.params:
            raise ValueError("Use at least one parameter, one coordinate and depth >= 1")

    @cached_property
    def symbols(self):
        return tuple(sp.Symbol(s) for s in self.params + self.coords)

    def const(self, c):
        return Jet(self, {(0,) * len(self.symbols): sp.sympify(c)})

    def variable(self, i):
        m = [0] * len(self.symbols)
        m[i] = 1
        return Jet(self, {tuple(m): sp.S.One})

    @property
    def x(self):
        return [self.variable(len(self.params) + j) for j in range(len(self.coords))]

    @property
    def p(self):
        return [self.variable(j) for j in range(len(self.params))]


class Jet:
    def __init__(self, ring: Ring, terms: dict[tuple[int, ...], sp.Expr]):
        self.ring = ring
        n = len(ring.params)
        self.terms = {}
        for mon, coef in terms.items():
            if len(mon) != len(ring.symbols) or any(e < 0 for e in mon):
                raise ValueError("Bad monomial")
            if sum(mon[:n]) <= ring.depth:
                c = sp.expand(coef)
                if c != 0:
                    self.terms[mon] = c

    def coerce(self, other):
        if isinstance(other, Jet):
            if other.ring != self.ring:
                raise ValueError("Different jet rings")
            return other
        return self.ring.const(other)

    def __add__(self, other):
        other = self.coerce(other)
        out = self.terms.copy()
        for m, c in other.terms.items():
            out[m] = out.get(m, sp.S.Zero) + c
        return Jet(self.ring, out)

    __radd__ = __add__

    def __neg__(self):
        return Jet(self.ring, {m: -c for m, c in self.terms.items()})

    def __sub__(self, other):
        return self + (-self.coerce(other))

    def __rsub__(self, other):
        return self.coerce(other) + (-self)

    def __mul__(self, other):
        other = self.coerce(other)
        out = {}
        n = len(self.ring.params)
        for ma, ca in self.terms.items():
            for mb, cb in other.terms.items():
                mon = tuple(a + b for a, b in zip(ma, mb))
                if sum(mon[:n]) <= self.ring.depth:
                    out[mon] = out.get(mon, sp.S.Zero) + ca * cb
        return Jet(self.ring, out)

    __rmul__ = __mul__

    def __truediv__(self, scalar):
        c = sp.sympify(scalar)
        if c == 0:
            raise ZeroDivisionError
        return Jet(self.ring, {m: sp.cancel(v / c) for m, v in self.terms.items()})

    def __pow__(self, k: int):
        if not isinstance(k, int) or k < 0:
            raise ValueError("Only nonnegative integer powers")
        ans = self.ring.const(1)
        base = self
        while k:
            if k & 1:
                ans = ans * base
            k //= 2
            if k:
                base = base * base
        return ans

    def diff(self, j: int):
        pos = len(self.ring.params) + j
        out = {}
        for mon, c in self.terms.items():
            if mon[pos]:
                m = list(mon)
                m[pos] -= 1
                out[tuple(m)] = c * mon[pos]
        return Jet(self.ring, out)

    def compose(self, mapping: list[Jet]):
        if len(mapping) != len(self.ring.coords):
            raise ValueError("Wrong coordinate count")
        n = len(self.ring.params)
        powers = {(j, 0): self.ring.const(1) for j in range(len(mapping))}
        out = self.ring.const(0)
        for mon, c in self.terms.items():
            term = Jet(self.ring, {mon[:n] + (0,) * len(mapping): c})
            for j, k in enumerate(mon[n:]):
                if (j, k) not in powers:
                    powers[j, k] = mapping[j] ** k
                term = term * powers[j, k]
            out = out + term
        return out

    def expr(self):
        return sp.Add(*(c * sp.prod(s**e for s, e in zip(self.ring.symbols, mon))
                        for mon, c in self.terms.items()))

    def is_zero(self):
        return not self.terms


def compose_maps(outer: list[Jet], inner: list[Jet]):
    return [f.compose(inner) for f in outer]


def log_map(F: list[Jet]):
    r = F[0].ring
    out = []
    for x in r.x:
        term = x
        ans = r.const(0)
        for k in range(1, r.depth + 1):
            term = term.compose(F) - term
            ans = ans + term * sp.Rational((-1)**(k+1), k)
        out.append(ans)
    return out


def derivative(f: Jet, a: list[Jet]):
    return sum((aj * f.diff(j) for j, aj in enumerate(a)), f.ring.const(0))


def flow(a: list[Jet], time=1):
    r = a[0].ring
    out = []
    for x in r.x:
        term = x
        ans = x
        for k in range(1, r.depth + 1):
            term = derivative(term, a)
            ans = ans + term * sp.sympify(time)**k / math.factorial(k)
        out.append(ans)
    return out


def log_operator(f: Jet, F: list[Jet]):
    term = f
    ans = f.ring.const(0)
    for k in range(1, f.ring.depth + 1):
        term = term.compose(F) - term
        ans = ans + term * sp.Rational((-1)**(k+1), k)
    return ans


def homological_inverse(v: list[Jet], eigenvalues):
    out = []
    n = len(v[0].ring.params)
    for j, f in enumerate(v):
        terms = {}
        for mon, c in f.terms.items():
            alpha = mon[n:]
            if sum(alpha) < 2:
                raise ValueError("Expected terms of coordinate degree >= 2")
            denominator = sp.expand(sp.prod(lam**a for lam, a in zip(eigenvalues, alpha))
                                    - eigenvalues[j])
            if denominator == 0:
                raise ValueError("Resonant monomial")
            terms[mon] = sp.cancel(c / denominator)
        out.append(Jet(f.ring, terms))
    return out


def linearizer(F: list[Jet], eigenvalues):
    r = F[0].ring
    L = [lam * x for lam, x in zip(eigenvalues, r.x)]
    f = [Fj - Lj for Fj, Lj in zip(F, L)]
    term = homological_inverse(f, eigenvalues)
    h = [r.const(0) for _ in F]
    for k in range(r.depth):
        h = [hj + tj * (-1)**(k+1) for hj, tj in zip(h, term)]
        Nterm = [tj.compose(F) - tj.compose(L) for tj in term]
        term = homological_inverse(Nterm, eigenvalues)
    return [x + hj for x, hj in zip(r.x, h)]


def run_checks():
    checks = []
    examples = {}

    def check(name, differences):
        if isinstance(differences, Jet):
            differences = [differences]
        failed = [str(f.expr()) for f in differences if not f.is_zero()]
        if failed:
            raise AssertionError(f"{name}: {failed}")
        checks.append(name)

    r = Ring(('t',), ('z',), 6)
    t, = r.p
    z, = r.x
    F = [z + t * z**2]
    a = log_map(F)
    examples['quadratic_iterative_log_through_t6'] = str(a[0].expr())
    check('one-variable exp(log(F)) = F through degree 6', [flow(a)[0] - F[0]])
    half = flow(a, sp.Rational(1, 2))
    check('half-iterate composed twice = F through degree 6', [half[0].compose(half) - F[0]])
    third = flow(a, sp.Rational(1, 3))
    check('third-iterate composed three times = F through degree 6',
          [third[0].compose(third).compose(third) - F[0]])
    check('inverse flow is a two-sided inverse through degree 6',
          [F[0].compose(flow(a, -1)) - z, flow(a, -1)[0].compose(F) - z])
    check('flow times 2/3 and -3/5 add through degree 6',
          [flow(a, sp.Rational(2, 3))[0].compose(flow(a, -sp.Rational(3, 5)))
           - flow(a, sp.Rational(1, 15))[0]])
    p, q = z**3 + t*z, z**2 + t*z**4
    check('log pullback obeys Leibniz on polynomial test through degree 6',
          log_operator(p*q, F) - log_operator(p, F)*q - p*log_operator(q, F))
    check('log pullback equals its coordinate vector field through degree 6',
          log_operator(p, F) - derivative(p, a))

    r2 = Ring(('t', 'u'), ('x', 'y'), 3)
    t, u = r2.p
    x, y = r2.x
    G = [x + t*x**2 + u*y, y + t*x*y + u*x]
    b = log_map(G)
    check('two-variable exp(log(G)) = G at two-parameter depth 3',
          [v-w for v, w in zip(flow(b), G)])
    check('two-variable inverse flow at depth 3',
          [v-w for v, w in zip(compose_maps(flow(b, -1), G), r2.x)])
    p, q = x*y + t*x, x**2 + y**3
    check('two-variable log Leibniz at depth 3',
          log_operator(p*q, G) - log_operator(p, G)*q - p*log_operator(q, G))
    check('two-variable log is first-order at depth 3',
          log_operator(p, G) - derivative(p, b))
    B = [[r2.const(int(j == k)) for k in range(2)] for j in range(2)]
    for j, v in enumerate(r2.x):
        term = v
        for k in range(2, r2.depth+2):
            term = derivative(term, b)
            for ell in range(2):
                B[j][ell] = B[j][ell] + term.diff(ell)/math.factorial(k)
    check('fixed-point factorization exp(b)(z)-z = B b at depth 3',
          [flow(b)[j] - r2.x[j] - sum((B[j][k]*b[k] for k in range(2)), r2.const(0))
           for j in range(2)])

    r3 = Ring(('t', 'u'), ('z',), 3)
    t, u = r3.p
    z, = r3.x
    lam = sp.Rational(3,5) + sp.Rational(4,5)*sp.I
    F = [lam*z + t*z**2 + u*(z**3+z**2)]
    H = linearizer(F, [lam])
    check('nonresonant Schroeder equation at two-parameter depth 3',
          H[0].compose(F) - lam*H[0])
    check('linearizer positive inverse at depth 3',
          H[0].compose(flow(log_map(H), -1)) - z)
    degree_ok = all(sum(mon[len(r3.params):]) <= 1 + 2*sum(mon[:len(r3.params)])
                    for mon in (H[0] - z).terms)
    if not degree_ok:
        raise AssertionError('linearizer degree support bound')
    checks.append('linearizer bound deg h_gamma <= 1 + 2 word-depth at depth 3')

    # Resonant root-of-unity decomposition for lambda = -1, q = 2.
    F = [-z + t*z**2 + u*z**3]
    P = compose_maps(F, F)
    X = log_map(P)
    A = compose_maps(F, flow(X, -sp.Rational(1,2)))
    H = [(z - A[0])/2]
    Hinv = flow(log_map(H), -1)
    Y = [(H[0].diff(0) * X[0]).compose(Hinv)/2]
    normal = [-flow(Y)[0]]
    check('resonant finite factor A^2 = id at depth 3', A[0].compose(A)-z)
    check('resonant average H A = -H at depth 3', H[0].compose(A)+H[0])
    check('resonant vector field is odd at depth 3', Y[0].compose([-z])+Y[0])
    check('resonant conjugacy H F = (rotation exp(Y)) H at depth 3',
          H[0].compose(F)-normal[0].compose(H))
    check('resonant log commutes with its original map at depth 3',
          F[0].diff(0)*X[0]-X[0].compose(F))
    examples['resonant_vector_field_through_total_depth3'] = str(Y[0].expr())
    examples['resonant_averaging_coordinate_through_total_depth3'] = str(H[0].expr())

    # First coefficients of the ordinary normalized quadratic linearizer.
    l = sp.Symbol('lambda')
    w = sp.Symbol('w')
    poly = w
    bs = []
    for n in range(1, 5):
        bn = sp.Symbol(f'b{n}')
        trial = poly + bn*w**(n+1)
        eq = sp.expand(trial.subs(w, l*w+w*w) - l*trial).coeff(w, n+1)
        value = sp.factor(sp.solve(eq, bn)[0])
        bs.append(value)
        poly = trial.subs(bn, value)
        residue = sp.cancel(sp.expand(poly.subs(w, l*w+w*w)-l*poly).coeff(w, n+1))
        if residue != 0:
            raise AssertionError('symbolic quadratic linearizer coefficient')
    checks.append('four symbolic quadratic linearizer coefficients satisfy recursion')
    examples['quadratic_linearizer_b1_to_b4'] = [str(v) for v in bs]

    return {
        'status': 'PASS',
        'checks_passed': len(checks),
        'checks': checks,
        'examples': examples,
        'arithmetic': 'exact rational and Gaussian rational coefficients; symbolic lambda for four coefficients',
        'scope': 'finite polynomial jets only; total parameter degree is not a Hahn valuation cutoff',
        'not_verified': ['arbitrary well-ordered support lemmas', 'general analytic radius claims',
                         'universal necessity arguments', 'formal proof-assistant certification', 'priority']
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path(__file__).resolve().parents[1]/'data'/'verification.json')
    args = parser.parse_args()
    report = run_checks()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(f"PASS: {report['checks_passed']} exact finite-jet checks")
    print(f"Report: {args.output}")
    for key, value in report['examples'].items():
        print(f"{key}: {value}")


if __name__ == '__main__':
    main()
