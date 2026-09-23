#!/usr/bin/env python3
"""Exact, finite regression checks accompanying the research manuscript.

These checks are NOT a model of all surreal numbers and are NOT a formal
verification of the class-sized theorems. They test the finite algebra used
in the proofs and a finite lexicographic analogue of separated support blocks.
Run: python verify.py
Requires Python >= 3.10 and SymPy. No network access is used.
"""
from __future__ import annotations

import itertools
import json
import platform
import random
from collections import Counter
from pathlib import Path

import sympy as sp

COUNTS: Counter[str] = Counter()
RNG = random.Random(23092026)
x, y, z, u, a, tau = sp.symbols("x y z u a tau")


def check(category: str, condition: object, detail: str = "") -> None:
    if not bool(condition):
        raise AssertionError(f"{category}: {detail}")
    COUNTS[category] += 1


def equal(category: str, lhs: sp.Expr, rhs: sp.Expr, detail: str = "") -> None:
    check(category, sp.cancel(sp.expand(lhs - rhs)) == 0, detail)


def binom_poly(var: sp.Symbol, degree: int) -> sp.Expr:
    return sp.prod(var - j for j in range(degree)) / sp.factorial(degree)


def newton_coeff(poly: sp.Expr, variables: tuple[sp.Symbol, ...],
                 indices: tuple[int, ...]) -> sp.Expr:
    """A finite forward-difference coefficient, using exact substitutions."""
    result = sp.S.Zero
    for point in itertools.product(*(range(n + 1) for n in indices)):
        weight = sp.prod((-1) ** (n - k) * sp.binomial(n, k)
                         for n, k in zip(indices, point))
        result += weight * poly.subs(dict(zip(variables, point)))
    return sp.expand(result)


def check_newton() -> None:
    for variables, bounds, samples in [((x,), (6,), 8),
                                        ((x, y), (3, 2), 6),
                                        ((x, y, z), (1, 1, 1), 4)]:
        indices = list(itertools.product(*(range(d + 1) for d in bounds)))
        for _ in range(samples):
            coeffs = [sp.Rational(RNG.randint(-8, 8), RNG.randint(1, 7))
                      for _ in indices]
            poly = sp.expand(sum(c * sp.prod(v ** k for v, k in zip(variables, nu))
                                 for c, nu in zip(coeffs, indices)))
            reconstructed = sp.S.Zero
            for nu in indices:
                c = newton_coeff(poly, variables, nu)
                reconstructed += c * sp.prod(binom_poly(v, k)
                                               for v, k in zip(variables, nu))
            equal("Newton reconstruction", reconstructed, poly)
    for n in range(10):
        b = binom_poly(x, n)
        for k in range(-12, 13):
            check("Integral binomial values", b.subs(x, k).is_Integer,
                  f"n={n}, k={k}")
    # Invertibility and dimension of the finite evaluation grid.
    for dx, dy in [(1, 1), (2, 1), (2, 2), (3, 2)]:
        nus = list(itertools.product(range(dx + 1), range(dy + 1)))
        matrix = sp.Matrix([[binom_poly(x, i).subs(x, p) *
                             binom_poly(y, j).subs(y, q)
                             for i, j in nus] for p, q in nus])
        check("Grid determinant", matrix.det() == 1)
        check("Grid inverse integral", all(t.is_Integer for t in matrix.inv()))


def check_resultants() -> None:
    examples = [
        (x + y, x * y + 1),
        (x**2 + y + 1, x + y**2 + 2),
        (x**2 + y**2 + 1, x**2 * y + x + 2),
        (y + 1, x**2 + y**2 + 1),
        (x**3 + y*x + y**2 + 1, x**2 + y**3 + 2),
        (x + y*z + 1, x**2 + y + z**2 + 3),
        (x**2 + y*z + 2, x*y + z + 1),
    ]
    for p, q in examples:
        variables = tuple(v for v in (x, y, z) if v in p.free_symbols | q.free_symbols)
        check("Reduced examples", sp.Poly(sp.gcd(p, q), *variables).total_degree() == 0)
        for main in variables:
            pj, qj = sp.degree(p, main), sp.degree(q, main)
            if qj == 0:
                continue
            rem = tuple(v for v in variables if v != main)
            lc_p, lc_q = sp.Poly(p, main).LC(), sp.Poly(q, main).LC()
            res = sp.resultant(p, q, main)
            bad = sp.expand(lc_p * lc_q * res)
            check("Nonzero bad-locus polynomial", bad != 0)
            bounds = []
            for v in rem:
                pi, qi = sp.degree(p, v), sp.degree(q, v)
                bound = (qj + 1) * pi + (pj + 1) * qi
                bounds.append(int(bound))
                check("Resultant coordinate bound", sp.degree(bad, v) <= bound)
            good = None
            for point in itertools.product(*(range(b + 1) for b in bounds)):
                values = dict(zip(rem, point))
                if bad.subs(values) != 0:
                    good = values
                    break
            check("Good specialization exists", good is not None)
            assert good is not None
            pp, qq = p.subs(good), q.subs(good)
            check("Specialized numerator degree", sp.degree(pp, main) == pj)
            check("Specialized denominator degree", sp.degree(qq, main) == qj)
            check("Specialized coprimality", sp.degree(sp.gcd(pp, qq), main) == 0)


def check_laurent() -> None:
    examples = [(x**2+1)/(x+1), 1/(x**2+1), (x+1)/(x**3+2),
                (x**4+x)/(x**2+1), (x**2+2*x+3)/(2*x+1)]
    for f in examples:
        p, q = sp.fraction(sp.cancel(f))
        quotient, remainder = sp.div(p, q, x)
        check("Nonpolynomial remainder", remainder != 0)
        start = int(sp.degree(q, x) - sp.degree(remainder, x))
        series = sp.series((f-quotient).subs(x, 1/u), u, 0, start+3).removeO()
        check("First negative Laurent power", series.coeff(u, start) != 0)
        expected = sp.LC(sp.Poly(remainder, x))/sp.LC(sp.Poly(q, x))
        equal("Laurent leading coefficient", series.coeff(u, start), expected)
    for n in range(1, 9):
        ratio = (x + sp.Rational(1, 2))/tau
        partial = a/tau * sum((-ratio)**j for j in range(n+1))
        equal("Geometric exact remainder", (x+tau+sp.Rational(1, 2))*partial,
              a*(1-(-ratio)**(n+1)))


def check_gaussian_and_maps() -> None:
    good = (x**2 - x)/(1+sp.I)
    bad = (x**2 - x)/2
    equal("Gaussian counterexample", bad.subs(x, sp.I), (-1-sp.I)/2)
    check("Gaussian counterexample", not sp.re(bad.subs(x, sp.I)).is_Integer)
    for re, im in itertools.product(range(-9, 10), repeat=2):
        value = sp.expand_complex(good.subs(x, re+sp.I*im))
        check("Gaussian integer-valued example", sp.re(value).is_Integer and sp.im(value).is_Integer)
    b = binom_poly(y, 2)
    # Explicit triangular maps, and their constant-term polynomial skeletons.
    equal("Triangular inverse", (x+b)-b, x)
    equal("Triangular inverse", (x-b)+b, x)
    for _ in range(10):
        c0, c1, c2 = (RNG.randint(-5, 5) for _ in range(3))
        f = c0 + c1*binom_poly(x, 1) + c2*binom_poly(x, 2)
        values = [f.subs(x, j) for j in range(3)]
        coeffs = [newton_coeff(f, (x,), (j,)) for j in range(3)]
        check("Ordinary fixed-divisor ideal",
              abs(int(sp.igcd(*values))) == abs(int(sp.igcd(*coeffs))))


def check_lexicographic_support() -> None:
    # Ordered exponent group Z^3 with lexicographic order. The coordinates
    # model eta (top), beta (middle), and a coefficient-group scale (bottom).
    # This is only a finite sanity check of the order inequalities.
    zero = (0, 0, 0)
    for n in range(60):
        for gamma in [-1000, -10, -1, 0, 1, 10, 1000]:
            check("Positive deceptive blocks", (1, -(n+1), gamma) > zero)
            check("Negative remote blocks", (-1, -n, gamma) < zero)
    for k in range(-8, 9):
        for gamma in [-1000, 0, 1000]:
            for delta in [-1000, 0, 1000]:
                check("Separated adjacent blocks", (0, k, gamma) < (0, k+1, delta))


def main() -> None:
    check_newton()
    check_resultants()
    check_laurent()
    check_gaussian_and_maps()
    check_lexicographic_support()
    report = {
        "status": "PASS",
        "assertions": sum(COUNTS.values()),
        "categories": dict(sorted(COUNTS.items())),
        "python": platform.python_version(),
        "sympy": sp.__version__,
        "seed": 23092026,
        "scope": "Finite exact algebra and sampled lexicographic inequalities only.",
        "not_verified": ["all surreal normal forms", "proper-class quantifiers",
                         "arbitrary infinite Hahn summability", "novelty or priority",
                         "Lean formal verification"],
    }
    destination = Path(__file__).resolve().parent
    (destination/"verification_report.json").write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    lines = ["FINITE EXACT VERIFICATION REPORT", "", f"Status: PASS",
             f"Assertions passed: {report['assertions']}",
             f"Python: {report['python']}; SymPy: {report['sympy']}",
             "Deterministic random seed: 23092026", ""]
    lines += [f"{k}: {v}" for k,v in sorted(COUNTS.items())]
    lines += ["", report["scope"], "NOT a formal or complete verification of the research theorems."]
    (destination/"verification_report.txt").write_text("\n".join(lines)+"\n", encoding="utf-8")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
