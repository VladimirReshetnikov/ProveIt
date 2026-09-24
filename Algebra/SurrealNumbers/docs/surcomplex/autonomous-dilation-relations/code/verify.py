#!/usr/bin/env python3
"""Finite exact checks accompanying dilation_rigidity.tex.

These checks do not prove the infinite Hahn-support, Newton--Puiseux,
or Böttcher theorems. Python 3.9+ and SymPy are required.
"""
from __future__ import annotations
from fractions import Fraction
from functools import reduce
from math import gcd, factorial
import json
import sys
from pathlib import Path
try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit('Install the optional check dependency with: python -m pip install sympy') from exc


def multiply(a: list[Fraction], b: list[Fraction], n: int) -> list[Fraction]:
    result = [Fraction(0) for _ in range(n + 1)]
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b[:n + 1 - i]):
                if y:
                    result[i + j] += x * y
    return result


def power(a: list[Fraction], exponent: int, n: int) -> list[Fraction]:
    result = [Fraction(1)] + [Fraction(0)] * n
    for _ in range(exponent):
        result = multiply(result, a, n)
    return result


def bottcher_l(q: dict[int, Fraction], n: int) -> list[Fraction]:
    """Return L(z)=z F(1/z) mod z^(n+1), F(T^d)=Q(F(T)).

    Q must be monic, centered, and of degree at least two.
    """
    d = max(q)
    if d < 2 or q[d] != 1 or q.get(d - 1, 0) != 0:
        raise ValueError('A monic centered polynomial of degree >= 2 is required.')
    l = [Fraction(1)] + [Fraction(0)] * n
    for m in range(1, n + 1):
        rhs = Fraction(0)
        for j, coefficient in q.items():
            shift = d - j
            if shift <= m:
                rhs += coefficient * power(l[:m + 1], j, m)[m - shift]
        lhs = l[m // d] if m % d == 0 else Fraction(0)
        # The as-yet-unset coefficient l[m] occurs as d*l[m] on the right.
        l[m] = (lhs - rhs) / d
    return l


def check_bottcher(q: dict[int, Fraction], l: list[Fraction]) -> None:
    n, d = len(l) - 1, max(q)
    rhs = [Fraction(0)] * (n + 1)
    for j, c in q.items():
        p = power(l, j, n)
        shift = d - j
        for m in range(shift, n + 1):
            rhs[m] += c * p[m - shift]
    lhs = [l[m // d] if m % d == 0 else Fraction(0) for m in range(n + 1)]
    assert lhs == rhs, ('Bottcher residual', q)
    lower = [j for j in q if j < d and q[j]]
    if lower:
        r = d - max(lower)
        assert all(l[m] == 0 for m in range(1, r))
        assert l[r] == -q[d - r] / d
    else:
        assert all(v == 0 for v in l[1:])


def main() -> dict:
    report: dict = {'scope': 'Finite exact checks only; not a formal or infinite-theorem verification.',
                    'python': sys.version.split()[0], 'sympy': sp.__version__, 'checks': {}}
    cases = {
        'T^2+1': {2: 1, 0: 1},
        'T^2-2': {2: 1, 0: -2},
        'T^3+T': {3: 1, 1: 1},
        'T^3+1': {3: 1, 0: 1},
        'T^4+2T^2-3T+5': {4: 1, 2: 2, 1: -3, 0: 5},
        'T^5': {5: 1},
    }
    expansions = {}
    for name, data in cases.items():
        q = {j: Fraction(c) for j, c in data.items()}
        l = bottcher_l(q, 32)
        check_bottcher(q, l)
        expansions[name] = {f'T^{1-m}': str(c) for m, c in enumerate(l[:13]) if c}
    report['checks']['bottcher'] = {'polynomials': len(cases), 'verified_L_degrees': '0 through 32',
                                    'initial_F_coefficients': expansions}

    t, x, y = sp.symbols('T X Y')
    polynomials = [t, t + 1, t**2 + t, t**3 + t, t**3 - 3*t,
                   t**3 + t**2 + 1, t**4 + t, t**4 + t**2,
                   (t + 1)**4, t*(t-1)**2]
    checked = []
    sample = None
    for p in polynomials:
        exponents = [a[0] for a, c in sp.Poly(p, t).terms() if a[0] > 0 and c]
        g = reduce(gcd, exponents)
        m = sp.degree(p, t)
        for d in (2, 3):
            res = sp.resultant(p - x, p.subs(t, t**d) - y, t)
            unit, factors = sp.factor_list(res, x, y)
            assert len(factors) == 1, (p, d, factors)
            factor, multiplicity = factors[0]
            assert multiplicity == g, (p, d, multiplicity, g)
            assert sp.degree(factor, y) == m // g
            assert sp.degree(factor, x) == d * m // g
            assert sp.expand(factor.subs({x: p, y: p.subs(t, t**d)}, simultaneous=True)) == 0
            checked.append({'P': str(p), 'd': d, 'g': g, 'degree_Y': int(m // g),
                            'degree_X': int(d*m // g)})
            if p == t**2 + t and d == 2:
                sample = str(factor)
    report['checks']['resultants'] = {'instances': len(checked), 'data': checked,
                                      'P=T^2+T_d=2_relation': sample}

    jac_checks = []
    for r in range(1, 6):
        variables = sp.symbols(f'T1:{r+1}')
        for d in (2, 3):
            rows = [sum((j+1)*variables[j]**(d**i) for j in range(r)) for i in range(r)]
            jac = sp.Matrix([[sp.diff(row, var) for var in variables] for row in rows])
            at = {var: j+2 for j, var in enumerate(variables)}
            det = jac.subs(at).det()
            assert det != 0
            # Distinct permutation exponent vectors certify the alternant support.
            import itertools
            exponent_vectors = set()
            for perm in itertools.permutations(range(r)):
                vector = [0]*r
                for i, j in enumerate(perm):
                    vector[j] = d**i - 1
                exponent_vectors.add(tuple(vector))
            assert len(exponent_vectors) == factorial(r)
            jac_checks.append({'r': r, 'd': d, 'nonzero_exact_determinant': str(det)})
    report['checks']['jacobians'] = {'instances': len(jac_checks), 'data': jac_checks}

    telescope_count = 0
    for d in (2, 3, 5):
        for n in range(1, 16):
            u = {Fraction(1, d**j): 1 for j in range(n + 1)}
            diff = {}
            for e, c in u.items():
                diff[d*e] = diff.get(d*e, 0) + c
                diff[e] = diff.get(e, 0) - c
            diff = {e: c for e, c in diff.items() if c}
            assert diff == {Fraction(d): 1, Fraction(1, d**n): -1}
            telescope_count += 1
    report['checks']['telescoping'] = {'instances': telescope_count,
                                      'identity': 'S_d u_N - u_N = omega^d - omega^(d^(-N))'}

    for p in (2, 3, 5, 7):
        f = 1 + 2*t + 3*t**2 + t**5
        assert sp.Poly(sp.expand(f**p - f.subs(t, t**p)), t, modulus=p).is_zero
    report['checks']['frobenius'] = {'primes': [2, 3, 5, 7]}

    u, v = sp.symbols('U V')
    germ_cases = [(v-u**2, 2, True), (v-u-u**2, 2, False),
                  (v**2-u**4-u**5, 2, True), (v**2-u**3, 2, False),
                  (v-u**3, 3, True), (v-u**3, 2, False)]
    weights = []
    for f, d, expected in germ_cases:
        terms = [(ij, c, ij[0] + d*ij[1]) for ij, c in sp.Poly(f, u, v).terms()]
        low = min(w for _, _, w in terms)
        active = [(ij, c) for ij, c, w in terms if w == low]
        assert (len(active) >= 2) == expected
        weights.append({'G': str(f), 'd': d, 'active_monomials': len(active), 'admissible': expected})
    report['checks']['newton_weights'] = {'instances': len(weights), 'data': weights}
    report['status'] = 'PASS'
    return report


if __name__ == '__main__':
    result = main()
    target = Path(__file__).with_name('verification_results.json')
    target.write_text(json.dumps(result, indent=2), encoding='utf-8')
    print(json.dumps(result, indent=2))
