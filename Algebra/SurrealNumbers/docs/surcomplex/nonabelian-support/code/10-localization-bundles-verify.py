#!/usr/bin/env python3
"""Exact finite checks for localization-resistant Hahn bundles.

These checks verify finite matrix identities and sample exponent inequalities.
They do NOT verify essential-singularity arguments, infinite well-ordering,
sheaf descent, classification, or the undecidability theorem.

Requires Python >= 3.9 and SymPy >= 1.12. No network access is used.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
import json
from pathlib import Path
import platform
import sys
import sympy as sp

COUNTS: Counter[str] = Counter()


def check(group: str, condition: bool) -> None:
    if not condition:
        raise AssertionError(f"Failed exact check in {group}")
    COUNTS[group] += 1


def jordan(n: int) -> sp.Matrix:
    if n < 1:
        raise ValueError("Jordan size must be positive")
    return sp.Matrix(n, n, lambda i, j: int(j == i + 1))


def nil_exp(matrix: sp.Matrix, scalar: sp.Expr, bound: int) -> sp.Matrix:
    if matrix.rows != matrix.cols:
        raise ValueError("Matrix must be square")
    power = sp.eye(matrix.rows)
    result = power.copy()
    for k in range(1, bound):
        power = power * matrix
        result += scalar**k * power / sp.factorial(k)
    if power * matrix != sp.zeros(matrix.rows):
        raise ValueError("Supplied nilpotence bound is too small")
    return result.applyfunc(sp.expand)


def equal_matrix(a: sp.Matrix, b: sp.Matrix) -> bool:
    return all(sp.expand(x) == 0 for x in a - b)


def verify(max_rank: int) -> dict:
    COUNTS.clear()
    u, v, w = sp.symbols("u v w", nonzero=True)
    for r in range(1, max_rank + 1):
        j = jordan(r)
        eu = nil_exp(j, u, r)
        ev = nil_exp(j, v, r)
        check("nilpotent_exponentials", equal_matrix(eu * ev, nil_exp(j, u + v, r)))
        check("nilpotent_exponentials", equal_matrix(eu * nil_exp(j, -u, r), sp.eye(r)))
        check("nilpotent_exponentials", eu.det() == 1)
        d = sp.diag(*[w**(r - 1 - k) for k in range(r)])
        check("monomial_conjugation", equal_matrix(d * j * d.inv(), w * j))
        check("monomial_conjugation", equal_matrix(d * eu * d.inv(), nil_exp(j, w * u, r)))
        # This is the finite-puncture gauge identity with p = u + v, c = u.
        check("finite_puncture_gauges",
              equal_matrix(eu * nil_exp(j, -(u + v), r), nil_exp(j, -v, r)))
        for k in range(r):
            check("centralizer_basis", j * j**k == j**k * j)

    for r in range(1, max_rank + 1):
        for s in range(1, max_rank + 1):
            nr, ns = jordan(r), jordan(s)
            # Column-vectorization: vec(Ns B - B Nr).
            hom = sp.kronecker_product(sp.eye(r), ns) - sp.kronecker_product(nr.T, sp.eye(s))
            check("intertwiner_dimensions", r * s - hom.rank() == min(r, s))
            # Nilpotent tensor sum has the classical Clebsch-Gordan block sizes.
            tensor = sp.kronecker_product(nr, sp.eye(s)) + sp.kronecker_product(sp.eye(r), ns)
            blocks = [r + s - 1 - 2 * k for k in range(min(r, s))]
            power = sp.eye(r * s)
            for k in range(r + s):
                expected = sum(max(size - k, 0) for size in blocks)
                check("tensor_jordan_profiles", power.rank() == expected)
                power = power * tensor
            if r <= 3 and s <= 3:
                conjugation = sp.kronecker_product(nil_exp(nr.T, -u, r), nil_exp(ns, u, s))
                check("hom_bundle_exponentials", equal_matrix(conjugation, nil_exp(hom, u, r + s - 1)))

    a, b, d, ca, cb = sp.symbols("a b d ca cb")
    change = sp.Matrix([[a, b], [0, d]])
    ga = sp.Matrix([[1, ca], [0, 1]])
    gb = sp.Matrix([[1, cb], [0, 1]])
    check("rank_two_gauge_formula", equal_matrix(gb * change * ga.inv(), sp.Matrix([[a, b + d * cb - a * ca], [0, d]])))

    for n in range(1, 2001):
        for bit in (0, 1):
            for next_bit in (0, 1):
                alpha = Fraction(1, n) + Fraction(bit, 10 * n * (n + 1))
                nxt = Fraction(1, n + 1) + Fraction(next_bit, 10 * (n + 1) * (n + 2))
                check("rational_profile_samples", alpha > nxt > 0)
        # Lexicographic Q*omega + Q, a non-Archimedean value group.
        alpha_nr = (Fraction(1), Fraction(-n))
        next_nr = (Fraction(1), Fraction(-n - 1))
        check("nonarchimedean_profile_samples", alpha_nr > next_nr > (Fraction(0), Fraction(0)))
        shift = (Fraction(-1, 2), Fraction(7, 3))
        shifted = tuple(x + y for x, y in zip(alpha_nr, shift))
        shifted_next = tuple(x + y for x, y in zip(next_nr, shift))
        check("nonarchimedean_profile_samples", shifted > shifted_next)

    return {
        "status": "PASS",
        "python_version": platform.python_version(),
        "sympy_version": sp.__version__,
        "max_rank": max_rank,
        "total_exact_checks": sum(COUNTS.values()),
        "checks_by_group": dict(sorted(COUNTS.items())),
        "scope": "Finite exact algebra and finite exponent samples only; not a formal proof of any infinite theorem.",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-rank", type=int, default=6)
    parser.add_argument("--output", type=Path, help="Optional JSON report path; no file is changed unless supplied")
    args = parser.parse_args()
    if not 1 <= args.max_rank <= 10:
        parser.error("--max-rank must be between 1 and 10")
    try:
        result = verify(args.max_rank)
    except (AssertionError, ValueError) as exc:
        print(str(exc), file=sys.stderr)
        return 1
    text = json.dumps(result, indent=2)
    print(text)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
