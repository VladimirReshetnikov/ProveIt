#!/usr/bin/env python3
"""Exact finite checks for Full Formal Orbit Fields of Surreal Arithmetic.

These are identity and finite-support checks, NOT proof-assistant verification
of the infinite or proper-class theorems. Requires Python >= 3.9 and SymPy.
"""
from __future__ import annotations

import argparse
import json
import math
import platform
from collections import Counter
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp

COUNTS: Counter[str] = Counter()


def check(name: str, condition: bool, detail: object = "") -> None:
    if not condition:
        raise AssertionError(f"{name} failed: {detail}")
    COUNTS[name] += 1


def binomial(a: Q, n: int) -> Q:
    if n < 0:
        return Q(0)
    ans = Q(1)
    for j in range(n):
        ans *= (a - j) / (j + 1)
    return ans


# A finite Hahn model: (high coordinate, low coordinate) with lexicographic order.
# D reads the low coordinate. This tests the coefficient calculus, not every
# support theorem for a full or class-sized Hahn field.
Exponent = Tuple[Q, Q]
Hahn = Dict[Exponent, Q]


def add(a: Hahn, b: Hahn) -> Hahn:
    out = dict(a)
    for g, c in b.items():
        out[g] = out.get(g, Q(0)) + c
        if out[g] == 0:
            del out[g]
    return out


def scale(a: Hahn, c: Q) -> Hahn:
    return {g: c * r for g, r in a.items() if c * r}


def mul(a: Hahn, b: Hahn) -> Hahn:
    out: Hahn = {}
    for (g1, g2), c in a.items():
        for (h1, h2), d in b.items():
            g = (g1 + h1, g2 + h2)
            out[g] = out.get(g, Q(0)) + c * d
    return {g: c for g, c in out.items() if c}


def derivative(a: Hahn, n: int = 1) -> Hahn:
    return {g: c * g[1] ** n for g, c in a.items() if c * g[1] ** n}


def taylor(a: Hahn, n: int) -> Hahn:
    return scale(derivative(a, n), Q(1, math.factorial(n)))


def multiplicative(a: Hahn, n: int) -> Hahn:
    return {g: c * binomial(g[1], n) for g, c in a.items()
            if c * binomial(g[1], n)}


def test_scalar_identities() -> None:
    weights = [Q(n, d) for d in range(1, 5) for n in range(-5, 6)]
    weights = sorted(set(weights))
    for a, b in product(weights, repeat=2):
        for n in range(9):
            rhs = sum((a ** j * b ** (n-j) /
                       (math.factorial(j) * math.factorial(n-j))
                       for j in range(n+1)), Q(0))
            check("exponential_convolution", rhs == (a+b)**n / math.factorial(n),
                  (str(a), str(b), n))
            rhs_b = sum((binomial(a, j) * binomial(b, n-j)
                         for j in range(n+1)), Q(0))
            check("binomial_convolution", rhs_b == binomial(a+b, n))
    for a in weights:
        for n in range(20):
            check("binomial_horizontal_recurrence",
                  (n+1)*binomial(a, n+1) == (a-n)*binomial(a, n))
            check("additive_horizontal_recurrence",
                  (n+1)*(a**(n+1)/math.factorial(n+1)) ==
                  a*(a**n/math.factorial(n)))


def test_finite_hahn() -> None:
    polys: List[Hahn] = []
    for k in range(1, 13):
        polys.append({(Q(k), Q(-k, 2)): Q(1, k),
                      (Q(0), Q(k, 3)): Q(-2),
                      (Q(-1), Q(0)): Q(k+1),
                      (Q(0), Q(0)): Q(k)})
    for a, b in product(polys, repeat=2):
        ab = mul(a, b)
        check("finite_hahn_leibniz",
              derivative(ab) == add(mul(derivative(a), b), mul(a, derivative(b))))
        for n in range(7):
            rhs_t: Hahn = {}
            rhs_u: Hahn = {}
            for j in range(n+1):
                rhs_t = add(rhs_t, mul(taylor(a, j), taylor(b, n-j)))
                rhs_u = add(rhs_u, mul(multiplicative(a, j), multiplicative(b, n-j)))
            check("finite_hahn_taylor_product", taylor(ab, n) == rhs_t)
            check("finite_hahn_binomial_product", multiplicative(ab, n) == rhs_u)
    for a in polys:
        for n in range(1, 12):
            check("zero_constant_derivative",
                  derivative(a, n).get((Q(0), Q(0)), Q(0)) == 0)
            check("zero_constant_binomial",
                  multiplicative(a, n).get((Q(0), Q(0)), Q(0)) == 0)


def test_witnesses() -> None:
    for n in range(60):
        for k in range(20):
            tk = Q((-n)**k, math.factorial(k)*math.factorial(n))
            tk_next = Q((-n)**(k+1), math.factorial(k+1)*math.factorial(n))
            check("witness_taylor_recurrence", (k+1)*tk_next == -n*tk)
            uk = binomial(Q(-n), k)/math.factorial(n)
            uk_next = binomial(Q(-n), k+1)/math.factorial(n)
            check("witness_binomial_recurrence", (k+1)*uk_next == (-n-k)*uk)
        if n:
            check("witness_exponential_derivative",
                  Q(-n, math.factorial(n)) == Q(-1, math.factorial(n-1)))
    # For finite alpha, model exponents as integer polynomials in a positive
    # infinite W. Positivity reads the sign of the highest nonzero coefficient.
    def sign(poly: Dict[int, int]) -> int:
        nonzero = {d: c for d, c in poly.items() if c}
        if not nonzero:
            return 0
        c = nonzero[max(nonzero)]
        return (c > 0) - (c < 0)
    for alpha in range(30):
        last = None
        for n in range(80):
            g = {alpha+2: 1, alpha+1: -n, 0: -n}
            check("finite_ordinal_polynomial_positive", sign(g) == 1)
            check("witness_exponent_constant", g[0] == -n)
            if last is not None:
                diff = {d: last.get(d, 0)-g.get(d, 0) for d in set(last)|set(g)}
                check("finite_ordinal_polynomial_decreasing", sign(diff) == 1)
            last = g


def test_symbolic_certificates() -> None:
    z, b, u, s, v, w = sp.symbols("z b u s v w")
    # D(b)=b, delta_m(u)=-u. Every rational function of b*u is horizontal.
    for j in range(1, 7):
        for k in range(1, 7):
            f = ((b*u)**j + 2)/(1+(b*u)**k)
            delta = b*sp.diff(f, b)-u*sp.diff(f, u)
            check("multiplicative_rational_invariant", sp.cancel(delta) == 0)
    check("multiplicative_parameter_recovery", sp.cancel((b*u)/b-u) == 0)
    check("rescaled_coordinate", sp.expand(-1/z*(-z)) == 1)
    # Scalar substitution exp(r*log(1+v)) has the stated binomial coefficients.
    for a in [sp.Rational(-3, 2), sp.Rational(1, 2), sp.Rational(2, 3),
              sp.Integer(-2), sp.Integer(0), sp.Integer(3)]:
        poly = sp.series(sp.exp(a*sp.log(1+v)), v, 0, 9).removeO().expand()
        for n in range(9):
            check("formal_clock_substitution", sp.simplify(poly.coeff(v, n)-sp.binomial(a,n)) == 0)
    # Coefficient form of the multiplicative formal group law, modulo total
    # degree 7. This uses exact symbolic polynomials, not numeric evaluation.
    for a in [Q(-3, 2), Q(1, 2), Q(2, 3), Q(2)]:
        def sq(q: Q) -> sp.Rational:
            return sp.Rational(q.numerator, q.denominator)
        lhs = sp.expand(sum(sq(binomial(a,n))*(v+w+v*w)**n for n in range(8)))
        rhs = sp.expand(sum(sq(binomial(a,j)*binomial(a,k))*v**j*w**k
                            for j in range(8) for k in range(8-j)))
        d = sp.Poly(lhs-rhs, v,w)
        for j in range(8):
            for k in range(8-j):
                check("multiplicative_formal_group", d.coeff_monomial(v**j*w**k) == 0)
    # Finite distinct-weight Vandermonde determinants. This checks the
    # determinant identity; distinct rational weights are NOT being claimed
    # Q-linearly independent as an infinite family.
    for n in range(1, 9):
        ws = [sp.Rational(j*j+2*j, j+1) for j in range(n)]
        mat = sp.Matrix([[a**k for a in ws] for k in range(n)])
        vand = sp.prod(ws[j]-ws[i] for i in range(n) for j in range(i+1,n))
        check("vandermonde_exact", mat.det() == vand)
        check("vandermonde_nonzero", vand != 0)
    for pdeg in range(7):
        for qdeg in range(7):
            p = z**pdeg+2
            q = z**qdeg+3
            left = sp.Poly(sp.diff(p,z)*q-p*sp.diff(q,z), z)
            right = sp.Poly(5*p*q,z)
            check("rational_log_derivative_degree", left.is_zero or left.degree() < right.degree())
    # Kummer family: algebraic equation for the truncated binomial branch.
    for q in range(1, 9):
        branch = sum(sp.Rational(binomial(Q(1,q), n).numerator,
                                binomial(Q(1,q), n).denominator)*v**n for n in range(9))
        power = sp.series(branch**q, v, 0, 9).removeO().expand()
        check("kummer_branch_equation", sp.expand(power-(1+v)) == 0)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification.json"))
    args = parser.parse_args()
    test_scalar_identities()
    test_finite_hahn()
    test_witnesses()
    test_symbolic_certificates()
    result = {
        "status": "passed",
        "total_assertions": sum(COUNTS.values()),
        "groups": dict(sorted(COUNTS.items())),
        "python_version": platform.python_version(),
        "sympy_version": sp.__version__,
        "arithmetic": "exact rational arithmetic and symbolic polynomial identities",
        "scope": "finite identity and finite support-model checks only",
        "not_verified": ["arbitrary Hahn summability", "all ordinal supports",
                         "class field theorems", "proof-assistant correctness", "novelty"]
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
