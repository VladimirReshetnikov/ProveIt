#!/usr/bin/env python3
"""Exact finite sanity checks for Prime Spectra at Surreal Infinity.

These tests are not a verification of infinite Hahn sums, ultrafilters,
continuum prime chains, or the novelty of any theorem. Only the Python
standard library is required. Run: python3 verify_finite.py --json results.json
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
import json
from pathlib import Path
import random
from typing import Iterable

Vector = dict[Q, Q]
Matrix = list[list[Q]]
COUNTS: dict[str, int] = {}


def check(condition: bool, group: str, message: str) -> None:
    if not condition:
        raise AssertionError(f"{group}: {message}")
    COUNTS[group] = COUNTS.get(group, 0) + 1


def clean(v: Vector) -> Vector:
    return {Q(k): Q(c) for k, c in v.items() if c}


def add(a: Vector, b: Vector) -> Vector:
    out = dict(a)
    for k, c in b.items():
        out[k] = out.get(k, Q(0)) + c
    return clean(out)


def scale(c: Q, a: Vector) -> Vector:
    return clean({k: c * v for k, v in a.items()})


def basis(k: int | Q) -> Vector:
    return {Q(k): Q(1)}


def compare(a: Vector, b: Vector) -> int:
    """Largest occupied index determines the order."""
    d = add(a, scale(Q(-1), b))
    if not d:
        return 0
    c = d[max(d)]
    return 1 if c > 0 else -1


def vmax(a: Vector, b: Vector) -> Vector:
    return a if compare(a, b) >= 0 else b


def vsum(values: Iterable[Vector]) -> Vector:
    ans: Vector = {}
    for v in values:
        ans = add(ans, v)
    return ans


def above_radius(v: Vector, n: int) -> Vector:
    """Representative of the coset after killing indices <= n."""
    return {k: c for k, c in v.items() if k > n}


def in_cut(v: Vector, cutoff: Q) -> bool:
    return all(k <= cutoff for k in v)


def check_cardinals() -> None:
    # Evaluate finite cardinal identities at an exact rational specialization.
    # This checks algebraic identities, not Hahn entireness.
    for n in range(1, 18):
        rho = [Q(2**j) for j in range(1, n + 1)]
        d = n + 2
        for k, z in enumerate(rho):
            value = Q(1)
            for a in rho[:-1]:
                value *= (z - a) / (rho[-1] - a)
            value *= (z / rho[-1]) ** d
            check(value == (1 if k == n - 1 else 0),
                  "cardinal_values", f"n={n}, k={k}")

    # Exact ordered-group damping inequality at rank > 1.
    for n in range(1, 31):
        gamma = basis(n)
        half = scale(Q(1, 2), gamma)
        mu_l = vsum(add(gamma, scale(Q(-1), vmax(half, basis(j))))
                    for j in range(1, n))
        check(compare(mu_l, {}) >= 0, "damping", f"cardinal n={n}")
        for m in range(12):
            d = max(n, 2 * m + 2)
            mu_c = add(scale(Q(-m), gamma),
                       add(mu_l, scale(Q(d, 2), gamma)))
            check(compare(mu_c, gamma) >= 0,
                  "damping", f"n={n}, m={m}, d={d}")


def check_scale_cuts() -> None:
    rng = random.Random(23092026)
    cuts = [Q(1, 10), Q(1, 3), Q(1, 2), Q(3, 4), Q(9, 10)]
    for n in range(1, 13):
        for r in cuts:
            for _ in range(60):
                old = clean({Q(j): Q(rng.randint(-5, 5), rng.randint(1, 5))
                             for j in range(0, n + 4)})
                qold = above_radius(old, n)
                check(in_cut(qold, n + 1 + r) == in_cut(qold, Q(n + 1)),
                      "convex_trace_intermediate", f"n={n}, r={r}")
                check(in_cut(qold, n + r) == (not qold),
                      "convex_trace_maximal", f"n={n}, r={r}")
        for r, s in zip(cuts, cuts[1:]):
            u = (r + s) / 2
            for offset in (0, 1):
                witness = basis(n + offset + u)
                check(not in_cut(witness, n + offset + r)
                      and in_cut(witness, n + offset + s),
                      "strict_cut_witness", f"n={n}, offset={offset}")
                # Even very large rational coefficients at lower indices
                # do not overtake a higher leading index.
                lower = {Q(n) + offset + r: Q(10**50)}
                check(compare(witness, lower) > 0,
                      "strict_cut_witness", "leading-index dominance")

    # Representative finite checks of the power-gap inequalities.  The
    # asymptotic statement for all large n is proved in the article.
    n = 2**60
    for a in range(1, 5):
        for b in range(a + 1, 5):
            da, db = 2**(12 * a), 2**(12 * b)  # exactly n^(a/5), n^(b/5)
            for m in (1, 2, 10, 100, 1000):
                check(m * da < db, "finite_power_gaps", f"{a}/5 < {b}/5")


def identity(n: int) -> Matrix:
    return [[Q(i == j) for j in range(n)] for i in range(n)]


def multiply(a: Matrix, b: Matrix) -> Matrix:
    return [[sum((a[i][k] * b[k][j] for k in range(len(b))), Q(0))
             for j in range(len(b[0]))] for i in range(len(a))]


def val2(x: Q) -> int:
    if x == 0:
        return 10**9  # finite tests use a sentinel, not a mathematical value
    a, b = abs(x.numerator), x.denominator
    out = 0
    while a % 2 == 0:
        a //= 2
        out += 1
    while b % 2 == 0:
        b //= 2
        out -= 1
    return out


def inverse(a: Matrix) -> Matrix:
    n = len(a)
    m = [row[:] + eye for row, eye in zip(a, identity(n))]
    for k in range(n):
        pivot = next((i for i in range(k, n) if m[i][k]), None)
        if pivot is None:
            raise ValueError("singular test matrix")
        m[k], m[pivot] = m[pivot], m[k]
        c = m[k][k]
        m[k] = [v / c for v in m[k]]
        for i in range(n):
            if i != k:
                c = m[i][k]
                m[i] = [v - c * w for v, w in zip(m[i], m[k])]
    return [row[n:] for row in m]


def valuation_smith(a: Matrix) -> tuple[Matrix, Matrix, Matrix]:
    """Finite pivot construction over the valuation ring Z_(2)."""
    m = [row[:] for row in a]
    nr, nc = len(m), len(m[0])
    u, v = identity(nr), identity(nc)
    for k in range(min(nr, nc)):
        candidates = [(val2(m[i][j]), i, j)
                      for i in range(k, nr) for j in range(k, nc) if m[i][j]]
        if not candidates:
            break
        _, pi, pj = min(candidates)
        m[k], m[pi] = m[pi], m[k]
        u[k], u[pi] = u[pi], u[k]
        for mat in (m, v):
            for row in mat:
                row[k], row[pj] = row[pj], row[k]
        pivot = m[k][k]
        for i in range(k + 1, nr):
            c = m[i][k] / pivot
            check(val2(c) >= 0, "smith_pivot_ratios", "row ratio")
            m[i] = [x - c * y for x, y in zip(m[i], m[k])]
            u[i] = [x - c * y for x, y in zip(u[i], u[k])]
        for j in range(k + 1, nc):
            c = m[k][j] / pivot
            check(val2(c) >= 0, "smith_pivot_ratios", "column ratio")
            for mat in (m, v):
                for row in mat:
                    row[j] -= c * row[k]
    return u, m, v


def check_smith() -> None:
    rng = random.Random(10050)
    for nr in range(1, 6):
        for nc in range(1, 6):
            for trial in range(8):
                a = [[Q(rng.randint(-10, 10) * 2**rng.randint(0, 4),
                        2 * rng.randint(0, 7) + 1)
                      for _ in range(nc)] for _ in range(nr)]
                if trial == 0:
                    a = [[Q(0) for _ in range(nc)] for _ in range(nr)]
                u, d, v = valuation_smith(a)
                check(multiply(multiply(u, a), v) == d,
                      "smith_identity", f"{nr}x{nc}, trial={trial}")
                check(all(d[i][j] == 0 for i in range(nr)
                          for j in range(nc) if i != j),
                      "smith_diagonal", "off-diagonal entry")
                for k in range(min(nr, nc) - 1):
                    check(val2(d[k][k]) <= val2(d[k + 1][k + 1]),
                          "smith_divisibility", "diagonal valuations")
                for mat in (u, v, inverse(u), inverse(v)):
                    check(all(val2(x) >= 0 for row in mat for x in row),
                          "smith_integral_automorphisms", "matrix or inverse")


def check_multiplicities() -> None:
    rng = random.Random(31)
    for n in range(1, 50):
        mult = list(range(1, n + 1))
        for power in (1, max(1, n // 2), n, n + 1):
            check(all(power >= m for m in mult) == (power >= n),
                  "multiplicity_uniform_power", f"n={n}, power={power}")
        orders = [rng.randint(1, 5) for _ in range(n)]
        minimum = max((m + o - 1) // o for m, o in zip(mult, orders))
        check(all(minimum * o >= m for m, o in zip(mult, orders)),
              "radical_order_test", "sufficiency of uniform power")
        check(not all((minimum - 1) * o >= m for m, o in zip(mult, orders)),
              "radical_order_test", "minimality of uniform power")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path, help="write deterministic JSON result")
    args = parser.parse_args()
    check_cardinals()
    check_scale_cuts()
    check_smith()
    check_multiplicities()
    result = {
        "status": "PASS",
        "checks": COUNTS,
        "total_assertions": sum(COUNTS.values()),
        "matrix_cases": 200,
        "arithmetic": "Exact integers and fractions; no floating-point arithmetic",
        "scope": "Finite sanity checks only; not proofs of infinite or ultrafilter theorems",
    }
    text = json.dumps(result, indent=2, sort_keys=True)
    print(text)
    if args.json is not None:
        args.json.write_text(text + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
