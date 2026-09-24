#!/usr/bin/env python3
"""Exact reproducibility checks for the Stirling-subset Hankel obstruction.

Python 3.9+, standard library only. Run from any working directory:
    python code/verify.py
The proof is in article.tex; these finite checks are an independent audit.
"""
from __future__ import annotations

import argparse
import csv
import json
from fractions import Fraction
from functools import lru_cache
from itertools import permutations
from math import comb
from pathlib import Path
from typing import Optional

Poly = list[int]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def binom(n: int, k: int) -> int:
    return comb(n, k) if 0 <= k <= n else 0


def rows(r: int, max_n: int, cap: Optional[int] = None) -> list[Poly]:
    """Rows S^(r)_{n,k}, optionally truncated to k <= cap."""
    if r < 1 or max_n < 0 or (cap is not None and cap < 0):
        raise ValueError("Need r >= 1, max_n >= 0, and cap >= 0.")
    result = [[1]]
    for n in range(1, max_n + 1):
        last = result[-1]
        degree = n if cap is None else min(n, cap)
        row = [0] * (degree + 1)
        for k in range(1, degree + 1):
            left = last[k - 1] if k - 1 < len(last) else 0
            same = last[k] if k < len(last) else 0
            row[k] = comb(n + (r - 1) * k - 1, r - 1) * left + k * same
        result.append(row)
    return result


@lru_cache(maxsize=None)
def partitions_by_distinguished_block(r: int, labels: int, blocks: int) -> int:
    """Independent enumeration: choose the block containing label 1."""
    if blocks == 0:
        return int(labels == 0)
    if labels < r * blocks or labels < 1:
        return 0
    return sum(
        comb(labels - 1, size - 1)
        * partitions_by_distinguished_block(r, labels - size, blocks - 1)
        for size in range(r, labels - r * (blocks - 1) + 1)
    )


def add_scaled(target: Poly, source: Poly, scale: int) -> None:
    if len(target) < len(source):
        target.extend([0] * (len(source) - len(target)))
    for i, value in enumerate(source):
        target[i] += scale * value


def multiply(p: Poly, q: Poly, cap: Optional[int] = None) -> Poly:
    degree = len(p) + len(q) - 2
    if cap is not None:
        degree = min(degree, cap)
    result = [0] * (degree + 1)
    for i, u in enumerate(p):
        if u == 0 or i > degree:
            continue
        for j, v in enumerate(q[: degree - i + 1]):
            result[i + j] += u * v
    return result


def hankel_det(polynomials: list[Poly], shift: int,
               cap: Optional[int] = None) -> Poly:
    if shift < 0 or shift + 4 >= len(polynomials):
        raise ValueError("Insufficient polynomial rows or negative shift.")
    result = [0]
    for perm in permutations(range(3)):
        inversions = sum(perm[i] > perm[j] for i in range(3) for j in range(i + 1, 3))
        term = [1]
        for i, j in enumerate(perm):
            term = multiply(term, polynomials[shift + i + j], cap)
        add_scaled(result, term, (-1) ** inversions)
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return result


def eval_poly(p: Poly, x: Fraction) -> Fraction:
    result = Fraction(0)
    for coefficient in reversed(p):
        result = result * x + coefficient
    return result


def two_blocks(r: int, n: int) -> int:
    if n < 1:
        raise ValueError("The two-block formula here requires n >= 1.")
    N = n + 2 * r - 2
    return 2 ** (N - 1) - sum(comb(N, j) for j in range(r))


def partial_binomial(N: int, m: int) -> int:
    return sum(binom(N, j) for j in range(m + 1))


def shift_formula(r: int, a: int) -> int:
    if r < 3 or a < 1:
        raise ValueError("The shifted formula here requires r >= 3, a >= 1.")
    N, m = a + 2 * r - 2, r - 3
    F0, F1, F2 = (partial_binomial(N + i, m) for i in range(3))
    return -2 ** (N - 1) * (binom(N, m) - binom(N, m - 1)) + F0 * F2 - F1 * F1


def first_shift_formula(r: int) -> Fraction:
    if r < 1:
        raise ValueError("Need r >= 1.")
    A = comb(2 * r - 1, r - 1)
    return Fraction(-A * A * (r - 2) * (r - 1) * (r * r + 11 * r + 6),
                    (r + 1) * (r + 2) ** 2 * (r + 3))


def difference_formula(r: int, a: int) -> int:
    b = [two_blocks(r, a + i) for i in range(5)]
    d = [b[i + 2] - 2 * b[i + 1] + b[i] for i in range(3)]
    return d[0] * d[2] - d[1] ** 2


def absolute_bound(polynomials: list[Poly], a: int) -> int:
    L = [sum(polynomials[a + i]) for i in range(5)]
    return (L[0] * L[2] * L[4] + L[0] * L[3] ** 2 + L[1] ** 2 * L[4]
            + 2 * L[1] * L[2] * L[3] + L[2] ** 3)


def isolate_increasing_root(p: Poly, denominator: int = 10 ** 12) -> tuple[Fraction, Fraction]:
    """Certified decimal-grid bracket, for the particular increasing quartic."""
    require(p[0] < 0 and all(c > 0 for c in p[1:]), "Root-isolation hypothesis.")
    lo, hi = 0, denominator
    require(eval_poly(p, Fraction(hi, denominator)) > 0, "Root not in (0,1).")
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if eval_poly(p, Fraction(mid, denominator)) < 0:
            lo = mid
        else:
            hi = mid
    lower, upper = Fraction(lo, denominator), Fraction(hi, denominator)
    require(eval_poly(p, lower) < 0 < eval_poly(p, upper), "Endpoint signs.")
    return lower, upper


def run(outdir: Path) -> dict:
    outdir.mkdir(parents=True, exist_ok=True)
    counts = {}
    # Independent block-containing-label enumeration against triangular recurrence.
    count = 0
    for r in range(1, 7):
        a = rows(r, 8)
        for n in range(9):
            for k, value in enumerate(a[n]):
                other = partitions_by_distinguished_block(r, n + (r - 1) * k, k)
                require(value == other, f"Independent count r={r}, n={n}, k={k}")
                count += 1
    counts["independent_partition_counts"] = count

    # Fully expanded polynomial determinants, no truncation.
    full = []
    for r in range(1, 13):
        a = rows(r, 12)
        for shift in range(1, 9):
            det = hankel_det(a, shift)
            require(all(c == 0 for c in det[:5]), "Coefficients below x^5.")
            leading = det[5] if len(det) > 5 else 0
            require(leading == difference_formula(r, shift), "Rank-one reduction.")
            if r >= 3:
                require(leading == shift_formula(r, shift) < 0, "All-shifts sign/formula.")
            else:
                require(leading == 0, "r=1,2 zero at x^5.")
            full.append({"r": r, "shift": shift, "coefficients_ascending": det})
    counts["full_polynomial_determinants"] = len(full)

    # Degree-five truncation still independently expands all six determinant terms.
    grid = []
    for r in range(3, 31):
        a = rows(r, 44, cap=5)
        for shift in range(1, 41):
            det = hankel_det(a, shift, cap=5)
            k = shift_formula(r, shift)
            require(det == [0] * 5 + [k] and k < 0, "Truncated determinant grid.")
            N, m = shift + 2 * r - 2, r - 3
            bound = -2 ** (N - 1) * (binom(N, m) - binom(N, m - 1))
            require(k <= bound < 0, "Quantitative negative bound.")
            grid.append({"r": r, "shift": shift, "coefficient_x5": k})
    counts["degree_five_determinants"] = len(grid)

    special = []
    for r in range(1, 101):
        k = first_shift_formula(r)
        det = hankel_det(rows(r, 5, cap=5), 1, cap=5)
        actual = det[5] if len(det) > 5 else 0
        require(k.denominator == 1 and k == actual, "Factored first-shift formula.")
        special.append({"r": r, "binomial_A": comb(2 * r - 1, r - 1),
                        "coefficient_x5": int(k)})
    counts["factored_first_shift_cases"] = len(special)

    count = 0
    for m in range(31):
        for N in range(max(1, m), 101):
            F = [partial_binomial(N + i, m) for i in range(3)]
            require(F[0] * F[2] <= F[1] ** 2, "Binomial partial-sum log-concavity.")
            count += 1
    counts["binomial_log_concavity_checks"] = count

    a3 = rows(3, 6)
    h31 = hankel_det(a3, 1)
    h32 = hankel_det(a3, 2)
    q = [-16, 19110, 938700, 15309000, 79380000]
    require(h31 == [0] * 5 + q, "Explicit r=3 polynomial.")
    lower, upper = isolate_increasing_root(q)
    example_x = Fraction(1, 2000)
    value31 = eval_poly(h31, example_x)
    require(value31 < 0, "Exact scalar Stieltjes witness.")
    value32 = eval_poly(h32, Fraction(1, 10000))
    require(value32 < 0, "Simple exact Hamburger witness at x=1/10000.")
    require(eval_poly(h32[5:], Fraction(1, 10000)) < -19, "Uniform example interval.")
    M32 = absolute_bound(a3, 2)
    eps32 = min(Fraction(1), Fraction(-shift_formula(3, 2), 2 * M32))
    require(eval_poly(h32, eps32) < 0, "Exact scalar Hamburger witness.")

    with (outdir / "full_determinants.json").open("w", encoding="utf-8") as f:
        json.dump(full, f, indent=2)
        f.write("\n")
    for name, records in [("leading_coefficients.csv", special), ("shifted_coefficients.csv", grid)]:
        with (outdir / name).open("w", newline="", encoding="utf-8") as f:
            writer = csv.DictWriter(f, fieldnames=list(records[0]))
            writer.writeheader()
            writer.writerows(records)
    report = {
        "status": "all exact checks passed",
        "arithmetic": "Python arbitrary-precision integers and fractions; no floating-point tests",
        "verification_is_not": "a proof assistant check or a substitute for the all-parameter proofs",
        "check_counts": counts,
        "ranges": {"independent_counts": "1<=r<=6, 0<=n<=8, 0<=k<=n",
                   "full_determinants": "1<=r<=12, 1<=shift<=8",
                   "truncated_determinants": "3<=r<=30, 1<=shift<=40",
                   "first_shift": "1<=r<=100"},
        "r3_example": {"rows_1_to_6": a3[1:], "H31_coefficients": h31,
                       "H32_coefficients": h32, "x": str(example_x),
                       "H31_at_x": str(value31), "unique_positive_root_lower": str(lower),
                       "unique_positive_root_upper": str(upper),
                       "H32_at_1_over_10000": str(value32),
                       "H32_bound_M": M32, "H32_epsilon": str(eps32)},
    }
    # Derive decimal-grid endpoints rather than embedding approximations in certificates.
    D = 10 ** 12
    report["r3_example"]["root_bracket_decimal_grid"] = [
        f"0.{int(v * D):012d}" for v in (lower, upper)]
    with (outdir / "verification.json").open("w", encoding="utf-8") as f:
        json.dump(report, f, indent=2)
        f.write("\n")
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--outdir", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data")
    args = parser.parse_args()
    report = run(args.outdir)
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
