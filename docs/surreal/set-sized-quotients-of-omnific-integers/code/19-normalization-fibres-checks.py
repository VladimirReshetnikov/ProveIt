#!/usr/bin/env python3
"""Exact finite checks accompanying article.tex.

Requires Python 3.10+ and SymPy. These tests check polynomial identities and
rational endpoint signs; they do not implement or formally verify surreal
numbers, integral closure, or the class-sized results in the article.
Run: python checks.py
"""
from __future__ import annotations

import sys
from fractions import Fraction
from itertools import combinations
from typing import Sequence

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required; install it before running these checks.") from exc


def require(condition: bool, description: str) -> None:
    if not condition:
        raise AssertionError(description)


def check_integral_idempotents() -> int:
    ii, u, t = sp.symbols("ii u T")
    relations = sp.groebner([ii**2 + 1, u**2 - t*u + 1], ii, u, t,
                            domain=sp.QQ)
    plus, minus = (1 - ii*u)/2, (1 + ii*u)/2
    identities = [
        plus**2 - plus + t*u/4,
        minus**2 - minus + t*u/4,
        plus + minus - 1,
        plus*minus - t*u/4,
        u*(t-u) - 1,
    ]
    for identity in identities:
        remainder = relations.reduce(sp.expand(identity))[1]
        require(remainder == 0, f"Idempotent identity failed: {identity}")
    print(f"PASS: {len(identities)} normalization/idempotent identities")
    return len(identities)


def check_doubling() -> int:
    v, a, b, r, s = sp.symbols("v a b r s")
    relations = sp.groebner([v**2 + 1], v, a, b, r, s, domain=sp.QQ)
    left, right = a + v*b, a - v*b
    inverse_a, inverse_b = (r+s)/2, -v*(r-s)/2  # 1/v = -v
    identities = [
        inverse_a.subs({r: left, s: right}, simultaneous=True) - a,
        inverse_b.subs({r: left, s: right}, simultaneous=True) - b,
        inverse_a + v*inverse_b - r,
        inverse_a - v*inverse_b - s,
        (1-v*v)/2 - 1,  # w_+ maps to (1,0)
        (1+v*v)/2,
    ]
    for identity in identities:
        require(relations.reduce(sp.expand(identity))[1] == 0,
                f"Doubling identity failed: {identity}")
    print(f"PASS: {len(identities)} rational doubling identities")
    return len(identities)


def check_projectors() -> int:
    x = sp.Symbol("X")
    roots = [sp.Integer(-3), sp.Integer(-1), sp.Integer(2), sp.Integer(5)]
    p = sp.prod(x-root for root in roots)
    projectors = [sp.prod((x-other)/(root-other)
                         for other in roots if other != root)
                  for root in roots]
    identities = [sum(projectors) - 1,
                  x - sum(root*e for root, e in zip(roots, projectors))]
    identities += [e**2-e for e in projectors]
    identities += [e*f for e, f in combinations(projectors, 2)]
    for identity in identities:
        require(sp.rem(sp.expand(identity), p, x) == 0,
                f"Projector identity failed: {identity}")
    print(f"PASS: {len(identities)} finite spectral-projector identities")
    return len(identities)


def check_catalan() -> int:
    z = sp.Symbol("z")
    terms = 14
    series = sum(sp.catalan(n)*z**n for n in range(terms))
    defect = sp.Poly(sp.expand(series - 1 - z*series**2), z)
    for n in range(terms):
        require(defect.nth(n) == 0, f"Catalan recursion failed in degree {n}")
    print(f"PASS: Catalan expansion through degree {terms-1}")
    return terms


def polynomial(coefficients: Sequence[int], x: Fraction) -> Fraction:
    """Horner evaluation, coefficients in ascending degree order."""
    result = Fraction(0)
    for coefficient in reversed(coefficients):
        result = result*x + coefficient
    return result


def product(values: Sequence[Fraction]) -> Fraction:
    result = Fraction(1)
    for value in values:
        result *= value
    return result


def check_root_forcing() -> int:
    checked = 0
    for degree in range(1, 9):
        # Three deterministic, distinct coefficient patterns in each degree.
        patterns = [
            [(-1)**k * (k+1) for k in range(degree)],
            [(k+2)**2 for k in range(degree)],
            [0 if k % 2 else -(3*k+1) for k in range(degree)],
        ]
        eta = Fraction(1, 4)*Fraction(3, 4)**(degree-1)
        constant = degree*(degree+1)**(degree-1)
        for coefficients in patterns:
            bound = max(1, *(abs(a) for a in coefficients))
            lower = Fraction(constant*bound)/eta
            t = lower.numerator//lower.denominator + 2
            require(t > lower and t > 1, "The strict scale bound failed")
            for j in range(1, degree+1):
                endpoint_signs = []
                for side in (-1, 1):
                    x = (Fraction(j) + Fraction(side, 4))*t
                    baseline = product([x-k*t for k in range(1, degree+1)])
                    perturbation = polynomial(coefficients, x)
                    q_value = baseline + perturbation
                    require(abs(baseline) >= eta*t**degree,
                            "Baseline endpoint lower bound failed")
                    require(abs(perturbation) <= constant*bound*t**(degree-1),
                            "Perturbation upper bound failed")
                    require(abs(perturbation) < abs(baseline),
                            "Strict domination failed")
                    require(q_value*baseline > 0,
                            "Endpoint sign preservation failed")
                    endpoint_signs.append(q_value)
                    checked += 1
                require(endpoint_signs[0]*endpoint_signs[1] < 0,
                        "A root interval did not have opposite endpoint signs")
    print(f"PASS: {checked} exact endpoint tests (24 polynomials, degrees 1--8)")
    return checked


def main() -> None:
    print("Finite exact checks for Normalization and Arithmetic Fibres")
    print(f"Python {sys.version.split()[0]}; SymPy {sp.__version__}")
    total = sum(test() for test in (
        check_integral_idempotents, check_doubling, check_projectors,
        check_catalan, check_root_forcing,
    ))
    print(f"All {total} primary exact checks passed.")
    print("Scope: finite identities and rational inequalities only; no Lean verification.")


if __name__ == "__main__":
    main()
