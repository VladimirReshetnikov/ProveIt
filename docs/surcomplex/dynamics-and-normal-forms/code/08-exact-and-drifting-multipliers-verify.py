#!/usr/bin/env python3
"""Finite exact checks for the accompanying research manuscript.

Requires Python >= 3.10 and SymPy >= 1.14. All coefficients are Gaussian
rationals. These checks do NOT prove analytic radii, irrationality, infinite
Hahn summability, or any of the universal theorems in the article.

Run: python code/verify.py --output data/verification.json
An existing output is not overwritten unless --overwrite is supplied.
"""
from __future__ import annotations
import argparse
import itertools
import json
import math
import platform
from pathlib import Path
import time
from typing import TypeAlias
import sympy
from sympy.polys.domains import QQ_I

Exponent: TypeAlias = tuple[int, ...]
Poly: TypeAlias = dict[Exponent, object]
ZERO, ONE = QQ_I.zero, QQ_I.one
LAM = QQ_I(3, 4) / QQ_I(5)

class Truncation:
    """Two formal parameters followed by d coordinate variables."""
    def __init__(self, dimension: int, parameter_degree: int, coordinate_degree: int):
        self.d, self.m, self.n = dimension, parameter_degree, coordinate_degree
        self.z = tuple(self.monomial((0, 0) + tuple(int(i == j) for i in range(self.d)))
                       for j in range(self.d))
        self.den = {j: LAM ** j - LAM for j in range(2, self.n + 1)}
        assert all(self.den.values())

    def monomial(self, exponent: Exponent, coefficient=ONE) -> Poly:
        if len(exponent) != 2 + self.d:
            raise ValueError('Wrong exponent length')
        return {exponent: coefficient} if coefficient else {}

    def add(self, *polys: Poly) -> Poly:
        out: Poly = {}
        for poly in polys:
            for exp, val in poly.items():
                new = out.get(exp, ZERO) + val
                if new:
                    out[exp] = new
                else:
                    out.pop(exp, None)
        return out

    def scale(self, poly: Poly, c) -> Poly:
        return {e: c * a for e, a in poly.items() if c * a}

    def mul(self, left: Poly, right: Poly) -> Poly:
        out: Poly = {}
        for e, a in left.items():
            for f, b in right.items():
                if e[0] + e[1] + f[0] + f[1] > self.m:
                    continue
                if sum(e[2:]) + sum(f[2:]) > self.n:
                    continue
                g = tuple(x + y for x, y in zip(e, f))
                new = out.get(g, ZERO) + a * b
                if new:
                    out[g] = new
                else:
                    out.pop(g, None)
        return out

    def compose(self, outer: Poly, inner: tuple[Poly, ...]) -> Poly:
        if len(inner) != self.d:
            raise ValueError('Wrong coordinate dimension')
        identity = self.monomial((0,) * (self.d + 2))
        powers: list[list[Poly]] = []
        for j in range(self.d):
            top = max((e[j + 2] for e in outer), default=0)
            row = [identity]
            for _ in range(top):
                row.append(self.mul(row[-1], inner[j]))
            powers.append(row)
        cached: dict[Exponent, Poly] = {}
        out: Poly = {}
        for e, a in outer.items():
            beta = e[2:]
            if beta not in cached:
                temp = identity
                for j, k in enumerate(beta):
                    temp = self.mul(temp, powers[j][k])
                cached[beta] = temp
            for f, b in cached[beta].items():
                if sum(e[:2]) + sum(f[:2]) > self.m:
                    continue
                g = (e[0] + f[0], e[1] + f[1]) + f[2:]
                new = out.get(g, ZERO) + a * b
                if new:
                    out[g] = new
                else:
                    out.pop(g, None)
        return out

    def rotate(self, poly: Poly) -> Poly:
        return {e: a * LAM ** sum(e[2:]) for e, a in poly.items()}

    def inverse_homological(self, poly: Poly) -> Poly:
        out = {}
        for e, a in poly.items():
            degree = sum(e[2:])
            if degree < 2:
                raise AssertionError('A forbidden constant or linear term appeared')
            out[e] = a / self.den[degree]
        return out

    def delta(self, poly: Poly, f: tuple[Poly, ...]) -> Poly:
        return self.add(self.compose(poly, f), self.scale(self.rotate(poly), -ONE))

    def linearizer(self, p: tuple[Poly, ...]) -> tuple[Poly, ...]:
        f = tuple(self.add(self.scale(z, LAM), q) for z, q in zip(self.z, p))
        u = tuple(self.scale(self.inverse_homological(q), -ONE) for q in p)
        term = u
        for _ in range(1, self.m):
            term = tuple(self.scale(self.inverse_homological(self.delta(q, f)), -ONE)
                         for q in term)
            u = tuple(self.add(a, b) for a, b in zip(u, term))
        return tuple(self.add(z, q) for z, q in zip(self.z, u))

    def inverse(self, h: tuple[Poly, ...]) -> tuple[Poly, ...]:
        u = tuple(self.add(q, self.scale(z, -ONE)) for q, z in zip(h, self.z))
        g = self.z
        for _ in range(self.m):
            g = tuple(self.add(z, self.scale(self.compose(q, g), -ONE))
                      for z, q in zip(self.z, u))
        return g


def assert_equal(a: Poly, b: Poly, label: str) -> None:
    if a != b:
        keys = set(a) | set(b)
        bad = [(e, str(a.get(e, ZERO)), str(b.get(e, ZERO))) for e in sorted(keys)
               if a.get(e, ZERO) != b.get(e, ZERO)]
        raise AssertionError(f'{label}: first mismatches {bad[:4]}')


def check_conjugacy(d: int, m: int, n: int) -> dict:
    t = Truncation(d, m, n)
    p = []
    for j in range(d):
        terms = []
        # Truncation of z_j^2/(1-z_j), carried by the first parameter.
        for k in range(2, n + 1):
            beta = tuple(k if l == j else 0 for l in range(d))
            terms.append(t.monomial((1, 0) + beta))
        # A separate polynomial layer, including cross-coordinate terms.
        beta = [0] * d
        beta[j] = 2
        terms.append(t.monomial((0, 1) + tuple(beta), QQ_I(2)))
        beta[j] = 3
        terms.append(t.monomial((0, 1) + tuple(beta), -ONE))
        if d == 2:
            terms.append(t.monomial((0, 1, 1, 1), QQ_I(j + 1, 1)))
        p.append(t.add(*terms))
    p = tuple(p)
    f = tuple(t.add(t.scale(z, LAM), q) for z, q in zip(t.z, p))
    h = t.linearizer(p)
    g = t.inverse(h)
    identities = 0
    for j in range(d):
        assert_equal(t.compose(h[j], f), t.scale(h[j], LAM), 'H(F)=lambda H')
        assert_equal(t.compose(h[j], g), t.z[j], 'H(G)=id')
        assert_equal(t.compose(g[j], h), t.z[j], 'G(H)=id')
        assert_equal(t.compose(f[j], g), t.compose(g[j], tuple(t.scale(z, LAM) for z in t.z)),
                     'F(G)=G(lambda z)')
        identities += 4
        # The first parameter coefficient is forced by the homological inverse.
        first = {e: a for e, a in h[j].items() if e[:2] == (1, 0)}
        expected = t.scale(t.inverse_homological({e: a for e, a in p[j].items()
                                                 if e[:2] == (1, 0)}), -ONE)
        assert_equal(first, expected, 'First layer formula')
        identities += 1
    # Independent triangular solution in total coordinate degree.
    h2 = list(t.z)
    for degree in range(2, n + 1):
        residual = [t.add(t.compose(q, f), t.scale(q, -LAM)) for q in h2]
        for j in range(d):
            corr = {e: -a / t.den[degree] for e, a in residual[j].items()
                    if sum(e[2:]) == degree}
            h2[j] = t.add(h2[j], corr)
    for j in range(d):
        assert_equal(h[j], h2[j], 'Operator expansion vs. degree recursion')
        identities += 1
    # u and v may be folded to the same cyclic Hahn scale. Total parameter
    # degree truncation is compatible with that identification.
    def fold(poly: Poly) -> Poly:
        ans: Poly = {}
        for e, a in poly.items():
            k = (sum(e[:2]), 0) + e[2:]
            new = ans.get(k, ZERO) + a
            if new:
                ans[k] = new
            else:
                ans.pop(k, None)
        return ans
    pf = tuple(fold(q) for q in p)
    hf = t.linearizer(pf)
    for j in range(d):
        assert_equal(fold(h[j]), hf[j], 'Cyclic support collisions')
        identities += 1
    return {'dimension': d, 'parameter_total_degree': m, 'coordinate_total_degree': n,
            'vector_component_identities': identities,
            'nonzero_coefficients_H': [len(q) for q in h],
            'nonzero_coefficients_inverse': [len(q) for q in g],
            'arithmetic': 'exact Gaussian rationals', 'status': 'passed'}


def check_drift(m: int = 5, n: int = 13) -> dict:
    """Check the cyclic drift equation, and the collision u=v=epsilon."""
    t = Truncation(1, m, n)
    par_u = t.monomial((1, 0, 0))
    par_v = t.monomial((0, 1, 0))
    ordinary_f = t.add(*(t.monomial((0, 0, k)) for k in range(2, n + 1)))

    def solve(drift: Poly, nonlinear: Poly) -> tuple[Poly, Poly]:
        total_p = t.add(t.mul(drift, t.z[0]), nonlinear)
        f = (t.add(t.scale(t.z[0], LAM), total_p),)
        term = t.scale(t.inverse_homological(nonlinear), -ONE)
        answer = term
        for _ in range(1, m):
            rhs = t.add(t.mul(drift, term), t.scale(t.delta(term, f), -ONE))
            term = t.inverse_homological(rhs)
            answer = t.add(answer, term)
        h = t.add(t.z[0], answer)
        multiplier_h = t.add(t.scale(h, LAM), t.mul(drift, h))
        assert_equal(t.compose(h, f), multiplier_h, 'Drifting multiplier equation')
        return h, f[0]

    independent, f_independent = solve(par_u, t.mul(par_v, ordinary_f))
    cyclic, f_cyclic = solve(par_u, t.mul(par_u, ordinary_f))

    def fold(poly: Poly) -> Poly:
        out: Poly = {}
        for e, a in poly.items():
            key = (e[0] + e[1], 0, e[2])
            new = out.get(key, ZERO) + a
            if new:
                out[key] = new
            else:
                out.pop(key, None)
        return out
    assert_equal(fold(independent), cyclic, 'All colliding drift contributions retained')
    assert_equal(fold(f_independent), f_cyclic, 'Input folding')
    inverse = t.inverse((cyclic,))[0]
    assert_equal(t.compose(cyclic, (inverse,)), t.z[0], 'Cyclic inverse, right')
    assert_equal(t.compose(inverse, (cyclic,)), t.z[0], 'Cyclic inverse, left')
    # Exact first-v block: -f_n/((lambda+u)^n-(lambda+u)).
    first_v_checks = 0
    for degree in range(2, n + 1):
        dcoef = [LAM ** degree - LAM]
        for j in range(1, m):
            coefficient = QQ_I(math.comb(degree, j)) * LAM ** (degree - j) if j <= degree else ZERO
            if j == 1:
                coefficient -= ONE
            dcoef.append(coefficient)
        invcoef = [ONE / dcoef[0]]
        for k in range(1, m):
            invcoef.append(-sum((dcoef[j] * invcoef[k-j] for j in range(1, k+1)), ZERO)
                           / dcoef[0])
        for k in range(m):
            assert independent.get((k, 1, degree), ZERO) == -invcoef[k]
            first_v_checks += 1
    return {'parameter_total_degree': m, 'coordinate_degree': n,
            'polynomial_identities': 6, 'first_nonlinear_block_scalar_equalities': first_v_checks,
            'nonzero_coefficients_cyclic_H': len(cyclic),
            'nonzero_coefficients_cyclic_inverse': len(inverse),
            'status': 'passed'}


def tree_packing() -> dict:
    configurations, inequalities = 0, 0
    for size in range(1, 7):
        for parents_tail in itertools.product(*(range(j) for j in range(1, size))):
            parents = (-1,) + parents_tail
            for weights in itertools.product((1, 2), repeat=size):
                totals = list(weights)
                for j in range(size - 1, 0, -1):
                    totals[parents[j]] += totals[j]
                configurations += 1
                for q in range(1, 11):
                    count = sum(s % q == 0 for s in totals)
                    assert q * count <= totals[0], (parents, weights, totals, q)
                    inequalities += 1
    return {'parent_increasing_rooted_tree_weight_configurations': configurations,
            'tested_divisibility_packing_inequalities': inequalities,
            'vertices': '1 through 6', 'local_weights': [1, 2],
            'divisors_q': '1 through 10', 'status': 'passed'}


def chain_bookkeeping() -> dict:
    configurations, inequalities = 0, 0
    for total in range(1, 17):
        for length in range(1, min(6, total) + 1):
            for cuts in itertools.combinations(range(1, total), length - 1):
                endpoints = cuts + (total,)
                increments = tuple(b - a for a, b in zip((0,) + cuts, endpoints))
                assert all(x > 0 for x in increments)
                assert all(a < b for a, b in zip(endpoints, endpoints[1:]))
                assert sum(x + 1 for x in increments) == total + length
                configurations += 1
                for q in range(1, 9):
                    assert q * sum(x % q == 0 for x in endpoints) <= total
                    inequalities += 1
    return {'positive_increment_chains': configurations,
            'packing_inequalities': inequalities, 'total_degree_increment': '1 through 16',
            'maximum_chain_length': 6, 'status': 'passed'}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--overwrite', action='store_true')
    args = parser.parse_args()
    if args.output and args.output.exists() and not args.overwrite:
        parser.error('Output exists; pass --overwrite to replace it')
    start = time.monotonic()
    result = {
        'scope': 'Finite exact identities only; not an infinite proof or novelty check.',
        'python': platform.python_version(), 'sympy': sympy.__version__,
        'multiplier': '3/5 + (4/5)i',
        'conjugacy_suites': [check_conjugacy(1, 4, 11), check_conjugacy(2, 3, 7)],
        'cyclic_drift': check_drift(),
        'tree_packing': tree_packing(), 'chain_bookkeeping': chain_bookkeeping(),
        'elapsed_seconds': round(time.monotonic() - start, 3), 'status': 'all passed'}
    text = json.dumps(result, indent=2)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text + '\n', encoding='utf-8')
    print(text)

if __name__ == '__main__':
    main()
