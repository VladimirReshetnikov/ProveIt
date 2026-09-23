#!/usr/bin/env python3
"""Exact finite checks accompanying the omnific-automorphism manuscript.

These tests do not implement arbitrary surreal numbers or certify the
infinite-support, class-theoretic, or historical-novelty claims.
Python >= 3.10 and SymPy are required. No network access is used.
"""
from __future__ import annotations

import argparse
import json
import platform
import random
from fractions import Fraction as F
from math import factorial
from pathlib import Path
from typing import Callable

import sympy as sp

Exponent = tuple[F, F, F]
Series = dict[Exponent, F]
Functional = Callable[[Exponent], F]
ZERO: Exponent = (F(0), F(0), F(0))
DELTA: Exponent = (F(0), F(0), F(1))
EPSILON: Exponent = (F(0), F(1), F(0))


def plus(x: Exponent, y: Exponent) -> Exponent:
    return tuple(a + b for a, b in zip(x, y))  # type: ignore[return-value]


def times(n: int, x: Exponent) -> Exponent:
    return tuple(n * a for a in x)  # type: ignore[return-value]


def functional(v: Exponent) -> Functional:
    return lambda g: sum((x*y for x, y in zip(v, g)), F(0))


def shear_truncation(f: Series, s: F, a: Functional,
                     delta: Exponent, order: int) -> Series:
    """Expand through a specified shift count for each input monomial.

    This is not a global valuation truncation. The tests use it only for
    the exact first correction, which is present at every order >= 1.
    """
    result: Series = {}
    for g, c in f.items():
        for n in range(order + 1):
            exponent = plus(g, times(n, delta))
            coefficient = c * (s * a(g))**n / factorial(n)
            result[exponent] = result.get(exponent, F(0)) + coefficient
    return {g: c for g, c in result.items() if c}


class Checks:
    def __init__(self) -> None:
        self.groups: dict[str, int] = {}

    def equal(self, group: str, actual: object, expected: object) -> None:
        if actual != expected:
            raise AssertionError(f"{group}: {actual!r} != {expected!r}")
        self.groups[group] = self.groups.get(group, 0) + 1


def run() -> dict[str, object]:
    checks = Checks()
    rng = random.Random(20260923)
    a: Functional = lambda g: g[1]
    b: Functional = lambda g: g[0]

    # Exact scalar convolution, including inverse parameters.
    parameters = [F(-3, 2), F(-1), F(0), F(2, 3), F(2)]
    for c in parameters:
        for s in parameters:
            for u in parameters:
                for n in range(9):
                    lhs = sum(((s*c)**j * (u*c)**(n-j) /
                               (factorial(j)*factorial(n-j))
                               for j in range(n+1)), F(0))
                    rhs = ((s+u)*c)**n / factorial(n)
                    checks.equal("exponential_group_law", lhs, rhs)
        for s in parameters:
            for n in range(9):
                lhs = sum(((s*c)**j * (-s*c)**(n-j) /
                               (factorial(j)*factorial(n-j))
                               for j in range(n+1)), F(0))
                checks.equal("exponential_inverse", lhs, F(n == 0))

    grid: list[Exponent] = [(F(i), F(j), F(k))
                            for i in range(-2, 3)
                            for j in range(-2, 3)
                            for k in range(-2, 3)]
    for g in grid:
        for h in [grid[13], grid[41], grid[99]]:
            checks.equal("diagonal_derivation_leibniz", a(plus(g,h)), a(g)+a(h))
        for n in range(8):
            eps_n = plus(EPSILON, times(n, DELTA))
            coefficient = b(g)*a(plus(g, eps_n))-a(g)*b(plus(g, DELTA))
            checks.equal("iterated_bracket", coefficient, b(g))
            for m in [0, 2, 5]:
                eps_m = plus(EPSILON, times(m, DELTA))
                comm = b(g)*b(plus(g, eps_n))-b(g)*b(plus(g, eps_m))
                checks.equal("abelian_bracket_ideal", comm, F(0))
        if g < ZERO and a(g):
            for n in range(1, 17):
                checks.equal("negative_support_safety", plus(g,times(n,DELTA)) < ZERO, True)

    # Test the full bracket formula for unrelated rational maps/shifts.
    for _ in range(120):
        va = tuple(F(rng.randint(-3,3), rng.randint(1,3)) for _ in range(3))
        vb = tuple(F(rng.randint(-3,3), rng.randint(1,3)) for _ in range(3))
        af, bf = functional(va), functional(vb)  # type: ignore[arg-type]
        g, d, e = (rng.choice(grid) for _ in range(3))
        left = bf(g)*af(plus(g,e)) - af(g)*bf(plus(g,d))
        right = af(e)*bf(g)-bf(d)*af(g)
        checks.equal("general_bracket_formula", left, right)

    for _ in range(100):
        support = rng.sample(grid, 12)
        f = {g: F(rng.choice([-3,-2,-1,1,2,3]), rng.randint(1,4)) for g in support}
        s = F(rng.choice([-3,-1,1,2]), rng.randint(1,3))
        image = shear_truncation(f, s, a, DELTA, 8)
        for g, c in f.items():
            image[g] = image.get(g, F(0))-c
        difference = {g:c for g,c in image.items() if c}
        active = [g for g in support if a(g)]
        if not active:
            checks.equal("exact_first_displacement", difference, {})
        else:
            g0 = min(active)
            expected_exponent = plus(g0, DELTA)
            checks.equal("exact_first_displacement", min(difference), expected_exponent)
            checks.equal("exact_first_displacement", difference[expected_exponent], s*a(g0)*f[g0])
        inactive_f = {g:c for g,c in f.items() if not a(g)}
        checks.equal("kernel_fixed_examples", shear_truncation(inactive_f,s,a,DELTA,8), inactive_f)

    x, z = sp.symbols("x z")
    # Every coefficient below z^10 is computed from a finite expansion.
    for h in [z+2*z**2-z**3, 3*z**2-z**5, z**3+z**4]:
        expansion = sp.Poly(sum(x**n*h**n/sp.factorial(n) for n in range(10)), z)
        for d in range(1, 10):
            poly = sp.expand(expansion.coeff_monomial(z**d))
            checks.equal("coefficient_polynomial_linear_term",
                         sp.expand(poly).coeff(x,1), sp.expand(h).coeff(z,d))
            for q in [sp.Rational(1,2), sp.Rational(-2,3)]:
                direct = sp.expand(sum((q*h)**n/sp.factorial(n) for n in range(10))).coeff(z,d)
                checks.equal("coefficient_polynomial_evaluation", sp.expand(poly.subs(x,q)-direct), 0)

    s, u = sp.symbols("s u", nonzero=True)
    exp_s = sum((s*z)**n/sp.factorial(n) for n in range(9))
    # Leading coefficients of the nonzero iterated-commutator multipliers.
    for n in range(1, 7):
        polynomial = sp.Poly(sp.expand(u*(exp_s-1)**n), z)
        checks.equal("iterated_commutator_leading_term", polynomial.coeff_monomial(z**n), u*s**n)
        for j in range(n):
            checks.equal("iterated_commutator_lower_vanishing", polynomial.coeff_monomial(z**j), 0)

    X, Y, T = sp.symbols("X Y T")
    D = lambda f: T*X*sp.diff(f,X)
    E = lambda f: X*Y*sp.diff(f,Y)
    for f in [X, Y, X*Y, X**2*Y**3, X**-2*Y**-1]:
        checks.equal("symbolic_vector_field_bracket", sp.simplify(D(E(f))-E(D(f))-T*E(f)), 0)

    checks.equal("translation_square_root_obstruction", sp.binomial(sp.Rational(1,2),1), sp.Rational(1,2))
    checks.equal("translation_square_root_obstruction", sp.binomial(sp.Rational(1,2),2), sp.Rational(-1,8))
    checks.equal("gaussian_first_imaginary_coefficient", (-sp.I)**1/sp.factorial(1), -sp.I)
    checks.equal("gaussian_second_coefficient", (-sp.I)**2/sp.factorial(2), sp.Rational(-1,2))

    return {
        "status": "all_checks_passed",
        "python": platform.python_version(),
        "sympy": sp.__version__,
        "random_seed": 20260923,
        "assertions_executed": sum(checks.groups.values()),
        "groups": checks.groups,
        "scope": "Exact finite rational and symbolic identities; no arbitrary surreal implementation.",
        "not_verified": [
            "general Hahn summability by a proof assistant",
            "class-sized normal forms or class automorphisms",
            "the coefficient-functional separation lemma in a proof assistant",
            "historical novelty or independent peer review"
        ]
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification_report.json"))
    args = parser.parse_args()
    report = run()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
