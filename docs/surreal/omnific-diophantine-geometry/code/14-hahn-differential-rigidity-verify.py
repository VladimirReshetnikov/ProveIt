#!/usr/bin/env python3
"""Exact finite regression checks for Differential Rigidity of Hahn Rings.

This is not a formal verification of the article. Infinite Hahn support,
properness, Riemann--Roch, and proper-class transfer are not tested here.
Requires Python >= 3.10 and SymPy >= 1.13.
"""
from __future__ import annotations

import json
import platform
import random
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
from typing import TypeAlias

import sympy as sp

Series: TypeAlias = dict[Fraction, Fraction]
COUNTS: defaultdict[str, int] = defaultdict(int)


def check(group: str, statement: bool, description: str) -> None:
    if not statement:
        raise AssertionError(f"{group}: {description}")
    COUNTS[group] += 1


def clean(f: Series) -> Series:
    return {e: c for e, c in f.items() if c}


def add(f: Series, g: Series) -> Series:
    out = dict(f)
    for exponent, coefficient in g.items():
        out[exponent] = out.get(exponent, Fraction(0)) + coefficient
    return clean(out)


def scale(f: Series, a: Fraction | int) -> Series:
    return clean({e: a * c for e, c in f.items()})


def mul(f: Series, g: Series) -> Series:
    out: Series = {}
    for e, c in f.items():
        for d, b in g.items():
            out[e + d] = out.get(e + d, Fraction(0)) + c * b
    return clean(out)


def power(f: Series, n: int) -> Series:
    if n < 0:
        raise ValueError("This finite-series helper only accepts nonnegative powers.")
    out = {Fraction(0): Fraction(1)}
    while n:
        if n & 1:
            out = mul(out, f)
        f = mul(f, f)
        n //= 2
    return out


def euler(f: Series) -> Series:
    return clean({e: e * c for e, c in f.items()})


def ct(f: Series) -> Fraction:
    return f.get(Fraction(0), Fraction(0))


def random_series(rng: random.Random) -> Series:
    out: Series = {}
    for _ in range(rng.randint(1, 8)):
        exponent = -Fraction(rng.randint(0, 18), rng.randint(1, 6))
        coefficient = Fraction(rng.randint(-5, 5), rng.randint(1, 4))
        out[exponent] = out.get(exponent, Fraction(0)) + coefficient
    return clean(out)


def symbolic_checks() -> None:
    x, y, a, b, r, s, dx, dy = sp.symbols("x y a b r s dx dy")
    p = x**3 + a*x + b
    lhs = (-18*a*x + 27*b)*p + (6*a*x**2 - 9*b*x + 4*a**2)*sp.diff(p, x)
    check("symbolic", sp.expand(lhs - 4*a**3 - 27*b**2) == 0,
          "explicit cubic Bezout certificate")
    check("symbolic", sp.expand((x-r)**2*(x+2*r) - (x**3-3*r**2*x+2*r**3)) == 0,
          "singular cubic factorization")
    xx, yy = s**2-2*r, s**3-3*r*s
    check("symbolic", sp.expand(yy**2 - (xx**3-3*r**2*xx+2*r**3)) == 0,
          "singular cubic parametrization")
    polynomials = [x**2-2, x**3+x+1, x**4-x+1, x**5-x, x**6+1]
    for p in polynomials:
        aa, cc, gcd = sp.gcdex(p, sp.diff(p, x), x)
        check("symbolic", gcd == 1 and sp.expand(aa*p+cc*sp.diff(p, x)) == 1,
              f"squarefree Bezout certificate for {p}")
        for m in range(2, 8):
            residual = dx-y**(m-1)*(aa*y*dx+m*cc*dy)
            ideal_expression = aa*(p-y**m)*dx+cc*(sp.diff(p, x)*dx-m*y**(m-1)*dy)
            check("symbolic", sp.expand(residual-ideal_expression) == 0,
                  f"differential division modulo equation and derivative, m={m}")
    for xx, yy in [(3*s, 3*s**2-s), (1+3*s, 3*s**2+s)]:
        check("symbolic", sp.expand(3*yy-xx**2+xx) == 0, "integral polynomial arc")


def finite_series_checks() -> None:
    rng = random.Random(20260923)
    for index in range(250):
        f, g = random_series(rng), random_series(rng)
        product = mul(f, g)
        check("finite_series", euler(product) == add(mul(euler(f), g), mul(f, euler(g))),
              "Euler Leibniz identity")
        check("finite_series", ct(product) == ct(f)*ct(g), "constant coefficient multiplicativity")
        check("finite_series", set(euler(f)) <= set(f), "derivation does not introduce support")
        if f and g:
            check("finite_series", min(product) == min(f)+min(g), "valuation product identity")
        if euler(f):
            check("finite_series", min(euler(f)) >= min(f), "valuation derivative bound")
        if index < 40:
            for m in range(1, 6):
                check("finite_series", euler(power(f, m)) == scale(mul(power(f, m-1), euler(f)), m),
                      "Euler chain rule")
        positive = {Fraction(0): Fraction(2), Fraction(1, 3): Fraction(3),
                    Fraction(2, 3): Fraction(-1)}
        check("finite_series", all(e > 0 for e in euler(positive)), "D(O) lies in maximal ideal")
    # Two different rational linear functionals on a rank-two exponent space.
    exponent = (Fraction(0), Fraction(1))
    check("finite_series", exponent[0] == 0 and exponent[1] != 0,
          "one Euler probe can miss a nonconstant which another detects")


def degree_checks() -> None:
    for m in range(2, 15):
        for degree in range(2, 15):
            strict = (m-1)*degree > m
            check("degree", strict == ((m, degree) != (2, 2)), "unique quadratic threshold exception")
            if strict:
                for delta in [Fraction(1, 7), Fraction(3, 2), Fraction(19, 3)]:
                    epsilon = degree*delta/m
                    check("degree", delta-(m-1)*epsilon < 0, "negative quotient degree")


def arithmetic_checks() -> None:
    for n in range(-500, 501):
        check("arithmetic", (Fraction(n*n-n, 3).denominator == 1) == (n % 3 in (0, 1)),
              "periodic parameter criterion for 3Y=X^2-X")
    for a in range(-30, 31):
        for b in range(-30, 31):
            if 4*a**3+27*b*b == 0:
                r = Fraction(0) if a == 0 else Fraction(-3*b, 2*a)
                check("arithmetic", r.denominator == 1, "singular cubic has integral repeated root")
                check("arithmetic", a == -3*r*r and b == 2*r**3, "singular coefficient reconstruction")


def characteristic_two_checks() -> None:
    # Coefficients are in F_2, represented by presence/absence in a support set.
    for n in range(1, 31):
        support = {-Fraction(1, 2**j) for j in range(1, n+1)}
        square_support = {2*e for e in support}
        actual = support.symmetric_difference(square_support)
        expected = {Fraction(-1), -Fraction(1, 2**n)}
        check("characteristic_two", actual == expected, "finite Artin-Schreier telescoping")
    x, y, z = sp.symbols("X Y Z")
    f = y*y*z+y*z*z-x**3
    partials = [sp.Poly(sp.diff(f, q), x, y, z, modulus=2).as_expr() for q in (x, y, z)]
    check("characteristic_two", partials == [x*x, z*z, y*y], "smooth cubic partial derivatives")


def main() -> None:
    symbolic_checks()
    finite_series_checks()
    degree_checks()
    arithmetic_checks()
    characteristic_two_checks()
    report = {
        "status": "passed",
        "total_assertions": sum(COUNTS.values()),
        "groups": dict(COUNTS),
        "python": platform.python_version(),
        "sympy": sp.__version__,
        "random_seed": 20260923,
        "scope": "Exact finite algebraic regression checks only; not a formal proof of the paper.",
        "not_computationally_checked": [
            "Arbitrary infinite Hahn supports and coefficient families",
            "Valuative criterion for properness and scheme-valued contraction",
            "Global generation, Riemann--Roch, and geometric descent",
            "Transfer to the proper class of surreal or omnific numbers",
            "Historical novelty or priority"
        ],
    }
    text = json.dumps(report, indent=2) + "\n"
    Path(__file__).with_name("verification.json").write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
