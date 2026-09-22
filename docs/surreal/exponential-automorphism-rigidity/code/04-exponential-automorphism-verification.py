#!/usr/bin/env python3
"""Finite exact checks accompanying exponential_automorphism_rigidity.tex.

These checks are not a formal proof of any infinite/class-sized theorem.
Requirements: Python 3.10+ and SymPy. Run: python verification.py
"""
from __future__ import annotations

from fractions import Fraction
import random
import sys
import sympy as sp


def main() -> None:
    checks = 0

    def check(condition: bool, label: str) -> None:
        nonlocal checks
        if not condition:
            raise AssertionError(label)
        checks += 1

    print("FINITE EXACT CHECKS -- not theorem-prover verification")
    print(f"Python {sys.version.split()[0]}; SymPy {sp.__version__}")
    print("Random rational sample seed: 20260922")

    a, b, A, B = sp.symbols("a b A B")
    check(sp.expand(A * B - a * b - (A * (B - b) + b * (A - a))) == 0,
          "twisted Leibniz identity")
    H, q = sp.symbols("H q", positive=True)
    check(sp.expand(2 * H * (1 + q) - q * H - H - H * (1 + q)) == 0,
          "amplification inequality margin")
    print("PASS: twisted product identity and amplification margin")

    rng = random.Random(20260922)
    for j in range(250):
        image_a = Fraction(rng.randint(-100, 100), rng.randint(1, 30))
        h = Fraction(rng.randint(1, 100), rng.randint(1, 30))
        e = h * Fraction(rng.randint(-100, 100), 100)
        lower_expression = image_a * e + 2 * h * (1 + abs(image_a))
        check(abs(e) <= h and lower_expression > h, f"rational witness {j}")
    print("PASS: 250 exact rational amplification samples, including signed images")

    t = sp.Symbol("t")
    n = 13  # identities checked modulo t^13
    hseries = sp.series((sp.sqrt(1 + 4 * t) - 1) / 2, t, 0, n).removeO()

    def modulo(expr: sp.Expr) -> sp.Expr:
        poly = sp.Poly(sp.expand(expr), t)
        return sp.Add(*(coef * t**power[0] for power, coef in poly.terms()
                        if power[0] < n))

    p = t + t**2
    check(modulo(hseries + hseries**2 - t) == 0, "p after inverse")
    check(modulo(hseries.subs(t, p) - t) == 0, "inverse after p")
    print(f"PASS: both substitution-inverse identities modulo t^{n}")
    print("Inverse parameter through degree 8:", sp.series(hseries, t, 0, 9))

    for m in range(1, 13):
        expr = sp.series(((1 + t)**(-m) - 1) / t, t, 0, 3).removeO()
        check(expr.coeff(t, 0) == -m, f"Laurent leading coefficient m={m}")
    print("PASS: Laurent displacement coefficient -m at exponent 1-m, m=1,...,12")

    def N(poly: sp.Expr) -> sp.Expr:
        return sp.expand(poly).coeff(t, 1) * t**2

    def T(poly: sp.Expr) -> sp.Expr:
        return sp.expand(poly + N(poly))

    for j in range(20):
        f = sum(sp.Rational(rng.randint(-20, 20), rng.randint(1, 9)) * t**k
                for k in range(8))
        check(N(N(f)) == 0, f"nilpotence {j}")
        check(sp.expand(T(f - N(f)) - f) == 0, f"additive inverse {j}")
    check(sp.expand(T(t**2) - T(t)**2) == -2*t**3-t**4,
          "failure of multiplicativity")
    print("PASS: 40 additive inverse/nilpotence checks and nonmultiplicativity witness")

    c, d = sp.symbols("c d")
    check(sp.expand((a*c-b*d)**2 + (a*d+b*c)**2
                    - (a*a+b*b)*(c*c+d*d)) == 0,
          "quadratic norm multiplicativity")
    print("PASS: quadratic norm multiplicativity")

    # A sample of formal exp/substitution compatibility. Constant part is zero;
    # constants commute independently because substitution fixes the coefficient field.
    epsilon = t - 2*t**2 + 3*t**4
    exp_epsilon = modulo(sum(epsilon**k / sp.factorial(k) for k in range(n)))
    substituted_exp = modulo(exp_epsilon.subs(t, p))
    substituted_epsilon = epsilon.subs(t, p)
    exp_substituted = modulo(sum(substituted_epsilon**k / sp.factorial(k)
                                for k in range(n)))
    check(sp.expand(substituted_exp - exp_substituted) == 0,
          "partial exponential compatibility")
    print(f"PASS: partial exponential/substitution compatibility modulo t^{n}")
    print(f"TOTAL: {checks} exact checks passed.")
    print("No Lean proof was compiled. No computation enumerates surreal numbers.")


if __name__ == "__main__":
    main()
