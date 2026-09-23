#!/usr/bin/env python3
"""Exact finite identity checks accompanying unit_dilation_rigidity.tex.

Python 3 standard library only. These tests are NOT proofs about infinite Hahn
supports, all field elements, SML, nonexistence of relations, or novelty.
Run: python3 verify_finite.py [--output finite_verification.json]
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from fractions import Fraction
import json
from math import comb, factorial
from pathlib import Path
from random import Random
from typing import Dict, List, Tuple

Q = Fraction
counts: Dict[str, int] = defaultdict(int)


def check(condition: bool, category: str, detail: str) -> None:
    if not condition:
        raise AssertionError(f"{category}: {detail}")
    counts[category] += 1


def falling(n: int, r: int) -> int:
    if r < 0:
        raise ValueError("The derivative order must be nonnegative")
    ans = 1
    for i in range(r):
        ans *= n - i
    return ans


def first_nonzero(poly: Dict[int, Q]) -> int | None:
    support = [i for i, c in poly.items() if c]
    return min(support) if support else None


def binomial_checks() -> None:
    for n in range(41):
        for d in range(1, 14):
            tail = {h: Q(comb(n, h)) for h in range(n + 1)}
            for h in range(min(n, d - 1) + 1):
                tail[h] -= comb(n, h)
            expected = d if n >= d else None
            check(first_nonzero(tail) == expected,
                  "binomial_tail", f"n={n}, d={d}")
            if expected is not None:
                check(tail[d] == comb(n, d), "binomial_tail",
                      f"leading coefficient n={n}, d={d}")
    for n in range(1, 101):
        poly = {h: Q((-1) ** n * comb(n, h)) for h in range(n + 1)}
        poly[0] -= 1
        check(first_nonzero(poly) == (0 if n % 2 else 1),
              "parity_valuation", f"n={n}")
        expected_lc = -2 if n % 2 else n
        check(poly[first_nonzero(poly)] == expected_lc,
              "parity_valuation", f"leading coefficient n={n}")


def theta_checks() -> None:
    # Rational q checks finite coefficients of formal identities, NOT entireness.
    for q in (Q(2), Q(-2), Q(3, 2), Q(1, 3), Q(-3, 2)):
        a = [q ** (n * (n - 1) // 2) for n in range(42)]
        check(a[0] == 1, "theta_identity", f"q={q}, constant")
        for n in range(1, 41):
            check(a[n] == q ** (n - 1) * a[n - 1],
                  "theta_identity", f"q={q}, n={n}")
        for n in range(40):
            # [z^n](D theta - sigma_q theta - z D sigma_q theta).
            result = (n + 1) * a[n + 1] - q ** n * a[n]
            if n >= 1:
                result -= n * q ** n * a[n]
            check(result == 0, "differentiated_theta",
                  f"q={q}, n={n}")
        for u in (Q(2), Q(-3), Q(2, 5)):
            v = u * q
            f = [a[n] / u ** n for n in range(42)]
            for n in range(40):
                lhs = (n + 1) * u ** (n + 1) * f[n + 1]
                lhs -= v ** n * f[n]
                if n >= 1:
                    lhs -= n * v ** n * f[n]
                check(lhs == 0, "two_prescribed_dilations",
                      f"q={q}, u={u}, n={n}")


def operator_checks() -> None:
    rng = Random(20260923)
    bases = (Q(2), Q(3, 2), Q(-1), Q(-2, 3))
    for case in range(160):
        degree = rng.randrange(7, 23)
        a = [Q(rng.randrange(-5, 6), rng.randrange(1, 5))
             for _ in range(degree + 1)]
        terms: List[Tuple[Q, int, int, Q]] = []
        for u in bases[:rng.randrange(1, 5)]:
            for r in range(rng.randrange(1, 5)):
                for k in range(rng.randrange(1, 6)):
                    c = Q(rng.randrange(-3, 4), rng.randrange(1, 4))
                    if c:
                        terms.append((u, r, k, c))
        if not terms:
            terms.append((Q(2), 0, 0, Q(1)))
        d = max(k for _, _, k, _ in terms)
        s0 = min(r - k for _, r, k, _ in terms)
        maxshift = max(r - k for _, r, k, _ in terms)
        J = maxshift - s0
        direct: Dict[int, Q] = defaultdict(Q)
        for u, r, k, c in terms:
            for index in range(r, len(a)):
                direct[index - r + k] += (
                    c * a[index] * u ** index * falling(index, r))
        for m in range(d, degree + d + 5):
            by_formula = Q(0)
            for u, r, k, c in terms:
                index = m + r - k
                if 0 <= index < len(a):
                    by_formula += c * falling(index, r) * u ** index * a[index]
            check(direct[m] == by_formula, "operator_output_formula",
                  f"case={case}, output={m}")
            n = m + s0
            by_grouping = Q(0)
            for j in range(J + 1):
                if not 0 <= n + j < len(a):
                    continue
                Aj = Q(0)
                for u, r, k, c in terms:
                    if r - k == s0 + j:
                        Aj += u ** n * (u ** j * c * falling(n + j, r))
                by_grouping += Aj * a[n + j]
            check(direct[m] == by_grouping, "reindexed_shift_formula",
                  f"case={case}, output={m}, n={n}, s0={s0}")


def determinant(matrix: List[List[Q]]) -> Q:
    a = [row[:] for row in matrix]
    n = len(a)
    ans = Q(1)
    for col in range(n):
        pivot = next((r for r in range(col, n) if a[r][col]), None)
        if pivot is None:
            return Q(0)
        if pivot != col:
            a[pivot], a[col] = a[col], a[pivot]
            ans = -ans
        p = a[col][col]
        ans *= p
        for r in range(col + 1, n):
            scale = a[r][col] / p
            for j in range(col + 1, n):
                a[r][j] -= scale * a[col][j]
            a[r][col] = Q(0)
    return ans


def independence_checks() -> None:
    for roots in ((Q(2), Q(3)), (Q(1), Q(-1)),
                  (Q(2, 3), Q(-2), Q(5))):
        for maxdegree in range(4):
            columns = [(base, r) for base in roots
                       for r in range(maxdegree + 1)]
            size = len(columns)
            matrix = [[Q(n ** r) * base ** n for base, r in columns]
                      for n in range(size)]
            check(determinant(matrix) != 0, "finite_independence_matrix",
                  f"roots={roots}, degree={maxdegree}")


def boundary_checks() -> None:
    for p in (2, 3, 5, 7):
        for exponent in range(1, 4):
            n = p ** exponent
            check(all(comb(n, h) % p == 0 for h in range(1, n)),
                  "frobenius_boundary", f"p={p}, exponent={exponent}")
    for a in range(81):
        for n in range(81):
            # Coefficient of (sigma_2 - 2^a) z^a.
            c = (2 ** n - 2 ** a) if n == a else 0
            check(c == 0, "unbounded_polynomial_degree", f"a={a}, n={n}")
    # An exact integer check of the escape inequality B+j delta<0.
    for B in range(20):
        for gap in range(1, 7):
            delta = -B - gap
            for jump in range(1, 13):
                check(B + jump * delta < 0, "escape_inequality",
                      f"B={B}, delta={delta}, jump={jump}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=None)
    args = parser.parse_args()
    binomial_checks()
    theta_checks()
    operator_checks()
    independence_checks()
    boundary_checks()
    report = {
        "status": "PASS",
        "arithmetic": "Exact Python integers and fractions.Fraction",
        "random_seed": 20260923,
        "assertions_by_category": dict(sorted(counts.items())),
        "total_assertions": sum(counts.values()),
        "limitations": [
            "Finite algebra and selected examples only",
            "Not a proof of arbitrary Hahn support summability",
            "Not a proof of Skolem-Mahler-Lech or eventual zero bounds",
            "Not a proof of nonexistence of an annihilating equation",
            "Not a Lean formalization or a novelty certificate",
        ],
    }
    text = json.dumps(report, indent=2) + "\n"
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
