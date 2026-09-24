#!/usr/bin/env python3
"""Exact finite checks supporting article.tex; NOT a theorem verifier.

Requires Python 3.10+ and SymPy. Does not implement No or infinite Hahn sums.
Run: python verify.py --output verification.json
"""
from __future__ import annotations

import argparse
from collections import Counter
from itertools import combinations
import json
from math import factorial, prod
from pathlib import Path
import random
import sys
from typing import Any

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required: install the dependency in requirements.txt") from exc

COUNTS: Counter[str] = Counter()
RNG = random.Random(20260923)
x, y, t = sp.symbols("x y t")


def check(category: str, condition: Any, detail: str = "") -> None:
    """Count a successful exact assertion; raise on the first failure."""
    if not bool(condition):
        raise AssertionError(f"{category}: {detail}")
    COUNTS[category] += 1


def equal(category: str, lhs: Any, rhs: Any, detail: str = "") -> None:
    check(category, sp.expand(lhs - rhs) == 0, detail)


def euler(p: Any) -> Any:
    return sp.expand(t * sp.diff(p, t))


def coefficient(p: Any, n: int) -> Any:
    return sp.expand(p).coeff(t, n)


def geometric_rank() -> None:
    for size in range(1, 15):
        coeffs = [x**j for j in range(size)]
        matrix = sp.Matrix([[p.coeff(x, j) for p in coeffs] for j in range(size)])
        check("finite_coefficient_rank", matrix.rank() == size, f"size={size}")
        series = sum(x**j * t**j for j in range(size))
        equal("geometric_denominator", (1-x*t)*series, 1-x**size*t**size)
        for j in range(size):
            equal("truncated_denominator_coefficients", coefficient((1-x*t)*series, j), int(j == 0))


def random_poly() -> Any:
    return sum(RNG.randint(-5, 5)*x**RNG.randrange(4)*y**RNG.randrange(3)*t**RNG.randrange(7)
               for _ in range(6))


def derivation_checks() -> None:
    for _ in range(18):
        p, q = random_poly(), random_poly()
        equal("euler_leibniz", euler(p*q), euler(p)*q+p*euler(q))
        equal("coefficient_derivation_leibniz", sp.diff(p*q, x), sp.diff(p, x)*q+p*sp.diff(q, x))
        equal("commuting_derivations", sp.diff(euler(p), x), euler(sp.diff(p, x)))
    a = sp.symbols("a1:9")
    series = sum(a[n-1]*t**n for n in range(1, 9))
    jets = [series]
    for _ in range(5):
        jets.append(euler(jets[-1]))
    for n in range(1, 9):
        for j, jet in enumerate(jets):
            equal("private_coefficient_response", sp.diff(jet, a[n-1]), n**j*t**n)


def vandermonde() -> None:
    for size in range(1, 8):
        for _ in range(3):
            nodes = sorted(RNG.sample(range(1, 65), size))
            matrix = sp.Matrix([[n**j for j in range(size)] for n in nodes])
            expected = prod(nodes[b]-nodes[a] for a in range(size) for b in range(a+1, size))
            check("vandermonde", matrix.det() == expected and expected != 0, repr(nodes))


def tree_labels() -> None:
    branches: set[tuple[int, ...]] = set()
    while len(branches) < 20:
        branches.add(tuple(RNG.randrange(3) for _ in range(8)))
    ordered = sorted(branches)
    prefixes = [{(branch+(0,)*4)[:n] for n in range(1, 13)} for branch in ordered]
    for i, j in combinations(range(len(ordered)), 2):
        common = 0
        for a, b in zip(ordered[i], ordered[j]):
            if a != b:
                break
            common += 1
        check("tree_common_prefix", len(prefixes[i] & prefixes[j]) == common)
    for _ in range(24):
        selected = RNG.sample(range(len(ordered)), RNG.randrange(2, 9))
        for i in selected:
            others = set().union(*(prefixes[j] for j in selected if j != i))
            private = prefixes[i] - others
            check("finite_tree_private_tails", all((ordered[i]+(0,)*4)[:n] in private for n in range(9, 13)))


def growth_checks() -> None:
    for D in range(13):
        for d in range(1, 13):
            n0 = next(n for n in range(2, 60) if factorial(n) > D+d*factorial(n-1))
            for n in range(n0, n0+5):
                check("factorial_degree_gap", factorial(n) > D+d*factorial(n-1), f"D={D},d={d},n={n}")
    for _ in range(160):
        n, d, D = RNG.randrange(3, 9), RNG.randrange(1, 9), RNG.randrange(15)
        coefficient_degree = RNG.randrange(D+1)
        selected_degrees = [factorial(RNG.randrange(1, n)) for _ in range(RNG.randrange(d+1))]
        check("finite_jet_degree_bound", coefficient_degree+sum(selected_degrees) <= D+d*factorial(n-1))


def taylor_checks() -> None:
    Y00, Y01, Y10, Y11 = sp.symbols("Y00 Y01 Y10 Y11")
    variables = (Y00, Y01, Y10, Y11)
    v0, v1 = x*t+x**2*t**2, x**2*t**2
    baseline = (v0, euler(v0), v1, euler(v1))
    for n in range(3, 7):
        dn = factorial(n)
        r0 = x**dn*t**n+x**(dn+1)*t**(n+1)
        r1 = x**3*t**(n+1)
        tails = (r0, euler(r0), r1, euler(r1))
        for ell in sorted({0, 1, n-1}):
            p = t**ell*(x*Y00+Y01+Y00**2+Y00*Y11+Y10**3)
            base = sp.expand(p.subs(dict(zip(variables, baseline)), simultaneous=True))
            full = sp.expand(p.subs(dict(zip(variables, [a+b for a,b in zip(baseline, tails)])), simultaneous=True))
            linear = sum(sp.diff(p, var).subs(dict(zip(variables, baseline)), simultaneous=True)*r
                         for var, r in zip(variables, tails))
            remainder = sp.Poly(sp.expand(full-base-linear), t)
            check("quadratic_tail_order", all(monom[0] >= 2*n for monom, _ in remainder.terms()))
            equal("critical_taylor_coefficient", coefficient(full, n+ell), coefficient(base, n+ell)+x**dn*(x+n))
            base_coefficient = coefficient(base, n+ell)
            degree = -1 if base_coefficient == 0 else sp.Poly(base_coefficient, x).degree()
            check("taylor_baseline_degree_bound", degree <= 1+3*factorial(n-1))


def lexicographic_model() -> None:
    # Tuple order models b >> h >> every coefficient-exponent basis vector.
    # It is a finite ordered-group model, NOT an implementation of surreal numbers.
    zero = (0, 0) + (0,)*40
    for block in range(5):
        exponents = []
        for n in range(1, 41):
            basis = [0]*40
            basis[(n-1+block) % 40] = 1
            exponent = (1, -n, *basis)
            exponents.append(exponent)
            check("omnific_positive_exponent_model", exponent > zero)
            check("omnific_euler_weight_model", -exponent[1] == n)
        for first, second in zip(exponents, exponents[1:]):
            check("omnific_support_descent_model", first > second)


def multiply(a: dict[tuple[int,int], int], b: dict[tuple[int,int], int]) -> dict[tuple[int,int], int]:
    result: dict[tuple[int,int], int] = {}
    for (i,j), c in a.items():
        for (k,l), d in b.items():
            result[(i+k,j+l)] = result.get((i+k,j+l), 0)+c*d
    return {key: value for key, value in result.items() if value}


def slice_shift(a: dict[tuple[int,int], int], coset: int) -> dict[tuple[int,int], int]:
    return {(i,0): c for (i,j), c in a.items() if j == coset}


def coset_convolution() -> None:
    for _ in range(24):
        u = {(i,0): RNG.randint(-4,4) for i in range(-2,4)}
        v = {(i,j): RNG.randint(-4,4) for i in range(-2,4) for j in range(-2,3)}
        u, v = ({key:c for key,c in a.items() if c} for a in (u,v))
        uv = multiply(u, v)
        for coset in range(-2,3):
            check("coset_slice_convolution", slice_shift(uv, coset) == multiply(u, slice_shift(v, coset)))


def boundary_and_complex() -> None:
    for p in (2,3,5,7,11):
        for n in range(-25,26):
            check("positive_characteristic_boundary", pow(n, p, p) == n % p)
    z0, z1, z2 = sp.symbols("z0 z1 z2")
    scale = 1+sp.I
    for _ in range(20):
        p = sum(RNG.randint(-5,5)*z0**RNG.randrange(3)*z1**RNG.randrange(3)*z2**RNG.randrange(3)
                for _ in range(6))
        shifted = p.subs({z:scale*z for z in (z0,z1,z2)}, simultaneous=True)
        restored = shifted.subs({z:z/scale for z in (z0,z1,z2)}, simultaneous=True)
        equal("complex_invertible_substitution", restored, p)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Optional destination JSON report")
    args = parser.parse_args()
    for group in (geometric_rank, derivation_checks, vandermonde, tree_labels, growth_checks,
                  taylor_checks, lexicographic_model, coset_convolution, boundary_and_complex):
        group()
    report = {
        "status": "all finite checks passed",
        "total_checks": sum(COUNTS.values()),
        "categories": dict(sorted(COUNTS.items())),
        "python_version": sys.version.split()[0],
        "sympy_version": sp.__version__,
        "random_seed": 20260923,
        "scope": "Exact finite polynomial, integer, and ordered-group-model checks only.",
        "nonclaims": ["No implementation of No or infinite Hahn summation.",
                      "No proof of algebraic or differential independence.",
                      "No verification of cardinal or proper-class assertions.",
                      "No Lean formalization or independent proof review."]
    }
    text = json.dumps(report, indent=2)
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text+"\n", encoding="utf-8")
    print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
