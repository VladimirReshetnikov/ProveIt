#!/usr/bin/env python3
"""Exact finite checks for Geometric Rigidity over Omnific Integer Rings.

These checks validate polynomial identities and finite examples, not the
infinite-support or algebraic-geometric theorems. Requires Python >= 3.9
and SymPy. No network access is used. All tests remain active under -O.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path
import platform
import random
from typing import Dict, Tuple

import sympy as sp

Exponent = Tuple[int, int]
Series = Dict[Exponent, Fraction]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def normalize(a: Series) -> Series:
    return {g: c for g, c in a.items() if c}


def add(a: Series, b: Series) -> Series:
    out = dict(a)
    for g, c in b.items():
        out[g] = out.get(g, Fraction(0)) + c
    return normalize(out)


def multiply(a: Series, b: Series) -> Series:
    out: Series = {}
    for g, c in a.items():
        for h, d in b.items():
            e = (g[0] + h[0], g[1] + h[1])
            out[e] = out.get(e, Fraction(0)) + c * d
    return normalize(out)


def euler(a: Series, weights: Tuple[int, int]) -> Series:
    return normalize({g: c * (weights[0] * g[0] + weights[1] * g[1])
                      for g, c in a.items()})


def random_negative_series(rng: random.Random) -> Series:
    out: Series = {}
    for _ in range(rng.randint(2, 14)):
        first = rng.randint(-8, 0)
        second = rng.randint(-9, 9) if first else rng.randint(-9, 0)
        out[(first, second)] = Fraction(rng.randint(-9, 9), rng.randint(1, 7))
    out[(0, 0)] = Fraction(rng.randint(-7, 7))
    return normalize(out)


def run_checks() -> dict:
    X, Y, a, b, dx, dy, u = sp.symbols("X Y a b dx dy u")
    results = []

    def record(name: str, cases: int, detail: str) -> None:
        results.append({"name": name, "cases": cases, "status": "passed",
                        "detail": detail})

    cubic = X**3 + a*X + b
    Q = 4*a**3 + 27*b**2
    P = -18*a*X + 27*b
    R = 6*a*X**2 - 9*b*X + 4*a**2
    require(sp.expand(P*cubic + R*sp.diff(cubic, X) - Q) == 0,
            "Universal cubic Bezout identity failed")
    require(sp.expand((18*X+27)*(X**3-X+1)
                      + (-6*X**2-9*X+4)*(3*X**2-1) - 23) == 0,
            "Worked cubic identity failed")
    record("cubic_bezout_identities", 2,
           "Universal parametric identity and the a=-1,b=1 specialization.")

    polynomials = [X**2-2, X**3-X+1, X**3+1, X**4+X+1,
                   X**5+X+1, X**6+3*X+1, 2*X**4-3*X**2+5]
    cases = 0
    for f in polynomials:
        fp = sp.diff(f, X)
        require(sp.degree(sp.gcd(f, fp), X) == 0,
                f"Selected polynomial is not squarefree: {f}")
        U, V, gcd = sp.gcdex(f, fp, X)
        require(sp.expand(U*f+V*fp-1) == 0 and gcd == 1,
                f"Extended Euclidean identity failed for {f}")
        for m in range(2, 9):
            w = U*Y*dx/sp.Integer(m) + V*dy
            relation = Y**m-f
            d_relation = m*Y**(m-1)*dy-fp*dx
            certificate = (m*Y**(m-1)*w-dx
                           - U*relation*dx-V*d_relation)
            require(sp.expand(certificate) == 0,
                    f"Differential certificate failed, m={m}, f={f}")
            cases += 1
    record("superelliptic_differential_certificates", cases,
           "Seven squarefree polynomials, exponents m=2,...,8, exact QQ arithmetic.")

    cases = 0
    zeros = []
    for d in range(2, 51):
        for m in range(2, 51):
            margin = Fraction(d*(m-1)-m, m)
            require(margin >= 0, "Valuation margin was negative")
            if not margin:
                zeros.append((d, m))
            cases += 1
    require(zeros == [(2, 2)], "Unexpected zero-margin case")
    record("valuation_margin_examples", cases,
           "2<=degree,m<=50; the only zero margin is degree=m=2. The text proves all cases.")

    require(sp.expand((u**3)**2 - (u**2)**3) == 0,
            "Cuspidal parametrization failed")
    xx = u**2-2
    yy = u*(u**2-3)
    require(sp.expand(yy**2-(xx**3-3*xx+2)) == 0,
            "Nodal parametrization failed")
    record("singular_cubic_parametrizations", 2,
           "Cuspidal and nodal polynomial families, exact identities in Z[u].")

    rng = random.Random(934810)
    cases = 300
    for index in range(cases):
        s = random_negative_series(rng)
        t = random_negative_series(rng)
        weights = (rng.randint(-8, 8), rng.randint(-8, 8))
        ds = euler(s, weights)
        dt = euler(t, weights)
        product = multiply(s, t)
        require(euler(product, weights) == add(multiply(ds, t), multiply(s, dt)),
                f"Rank-two Leibniz test {index} failed")
        require(all(g < (0, 0) for g in ds), "Derivative has nonnegative exponent")
        require(not ds or not s or min(ds) >= min(s), "Derivative lowered valuation")
        require(product.get((0, 0), 0) == s.get((0, 0), 0)*t.get((0, 0), 0),
                "Constant-term multiplication failed")
        require(all(g <= (0, 0) for g in product), "Product support escaped A")
    record("finite_rank_two_hahn_examples", cases,
           "Seed 934810, lexicographic Z^2 exponents and rational coefficients. "
           "Checks Leibniz, support, valuation, and constant terms.")

    # F_2 coefficients are represented by exponent sets; addition is symmetric difference.
    for n in range(1, 65):
        support = {Fraction(-3, 2**j) for j in range(1, n+1)}
        actual_square = set()
        for g in support:
            for h in support:
                e = g+h
                if e in actual_square:
                    actual_square.remove(e)
                else:
                    actual_square.add(e)
        expected_square = {2*g for g in support}
        require(actual_square == expected_square, "Finite Frobenius identity failed")
        require(actual_square.symmetric_difference(support)
                == {Fraction(-3), Fraction(-3, 2**n)},
                "Artin-Schreier telescoping failed")
    Xh, Yh, Zh = sp.symbols("Xh Yh Zh")
    F = Xh**2*Zh + Xh*Zh**2 + Yh**3
    partials = [sp.Poly(sp.diff(F, z), Xh, Yh, Zh, modulus=2).as_expr()
                for z in (Xh, Yh, Zh)]
    require(partials == [Zh**2, Yh**2, Xh**2], "Characteristic-two partials failed")
    record("characteristic_two_frobenius", 65,
           "64 exact finite telescoping checks, plus the three projective partial derivatives.")

    # The contrasting valuation-ring point on y^2=x^3+1.
    truncated_root = sum(sp.binomial(sp.Rational(1, 2), j)*X**(3*j)
                         for j in range(15))
    require(sp.Poly(sp.expand(truncated_root**2-1-X**3), X).terms()[-1][0][0] >= 45,
            "Binomial example has an unexpected low-order residual")
    record("valuation_ring_contrast", 1,
           "Fifteen-term binomial series square agrees with 1+t^3 through degree 44.")

    return {
        "article": "Geometric Rigidity over Omnific Integer Rings",
        "repository_commit": "934810abdde4c6d74c08777b069445de43602934",
        "python_version": platform.python_version(),
        "sympy_version": sp.__version__,
        "status": "all finite checks passed",
        "test_groups": len(results),
        "total_cases": sum(r["cases"] for r in results),
        "checks": results,
        "scope": "Finite algebraic identities and examples only. "
                 "No Lean verification; no exhaustive Hahn-series or scheme-theoretic verification."
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        help="Optional JSON output path; omit to print only.")
    args = parser.parse_args()
    result = run_checks()
    text = json.dumps(result, indent=2, ensure_ascii=False)+"\n"
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
