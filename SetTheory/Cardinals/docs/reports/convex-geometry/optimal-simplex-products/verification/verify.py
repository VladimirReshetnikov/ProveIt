#!/usr/bin/env python3
"""Exact rational certificates and independent optimization for simplex products.

Uses only the Python standard library.  The finite dynamic program is a
cross-check, not a replacement for the proof for every dimension.
"""
from __future__ import annotations

import argparse
import csv
import json
from fractions import Fraction
from math import factorial
from pathlib import Path


def c(d: int) -> Fraction:
    if d < 1:
        raise ValueError("Simplex dimension must be positive")
    return Fraction((d + 1) * d**d, factorial(d))


def balanced(n: int, k: int) -> tuple[int, ...]:
    a, b = divmod(n, k)
    return (a,) * (k - b) + (a + 1,) * b


def value(parts: tuple[int, ...]) -> Fraction:
    ans = Fraction(1)
    for d in parts:
        ans *= c(d)
    return ans


def two_candidates(n: int) -> tuple[int, ...]:
    ks = {max(1, n // 13), (n + 12) // 13}
    candidates = [balanced(n, k) for k in sorted(ks)]
    return max(candidates, key=value)


def residue_optimizer(n: int) -> tuple[int, ...] | None:
    r = n % 13
    if r <= 8:
        k, rem = divmod(n - 14 * r, 13)
        parts = (13,) * max(k, 0) + (14,) * r
    else:
        b = 13 - r
        k, rem = divmod(n - 12 * b, 13)
        parts = (12,) * b + (13,) * max(k, 0)
    assert rem == 0
    return parts if k >= 0 else None


def run(limit: int, out: Path) -> None:
    out.mkdir(parents=True, exist_ok=True)
    a, b, m = c(12), c(14), c(13)
    ratios = {
        "peak_left": m**12 / a**13,
        "peak_right": m**14 / b**13,
        "branch_r8": b**8 / (m**4 * a**5),
        "branch_r9": m**6 * a**4 / b**9,
        "curvature_left": a**2 / (c(11) * m),
        "curvature_right": b**2 / (m * c(15)),
        "opposite_deviations": m**2 / (a * b),
    }
    prime_power_forms = {
        "peak_left": Fraction(5**2 * 7**13 * 11 * 13**131, 2**290 * 3**151),
        "peak_right": Fraction(13**181, 2**165 * 3**18 * 5**15 * 7**156 * 11),
        "branch_r8": Fraction(5**10 * 7**101 * 11, 2**10 * 3**47 * 13**61),
        "branch_r9": Fraction(3**34 * 13**85, 2**25 * 5**11 * 7**112 * 11),
    }
    for name, q in prime_power_forms.items():
        assert q == ratios[name]
    intervals = {
        "peak_left": (1019009, 1019010),
        "peak_right": (1010131, 1010132),
        "branch_r8": (1001039, 1001040),
        "branch_r9": (1001185, 1001186),
        "curvature_left": (1002550, 1002551),
        "curvature_right": (1001959, 1001960),
        "opposite_deviations": (1002226, 1002227),
    }
    records = {}
    for name, q in ratios.items():
        lo, hi = intervals[name]
        lower_margin = 10**6 * q.numerator - lo * q.denominator
        upper_margin = hi * q.denominator - 10**6 * q.numerator
        assert lower_margin > 0 and upper_margin > 0
        assert q > 1
        records[name] = {
            "numerator": str(q.numerator),
            "denominator": str(q.denominator),
            "strict_lower": f"{lo}/1000000",
            "strict_upper": f"{hi}/1000000",
            "positive_lower_margin": str(lower_margin),
            "positive_upper_margin": str(upper_margin),
        }

    gamma = ratios["branch_r8"]
    for name in ("branch_r9", "curvature_left", "curvature_right",
                 "opposite_deviations", "peak_left", "peak_right"):
        assert ratios[name] > gamma
    # peak_left = exp(13 alpha), peak_right = exp(13 beta).
    assert Fraction(2809964, 10**6)**13 < m
    assert m < Fraction(2809965, 10**6)**13

    best = [Fraction(1)]
    optimizers: list[tuple[int, ...]] = [()]
    maximizing_counts = [1]
    rows = []
    for n in range(1, limit + 1):
        # Independent recurrence over EVERY possible final part size.
        options = [(best[n - d] * c(d), d) for d in range(1, n + 1)]
        v, d = max(options)
        winners = [d0 for v0, d0 in options if v0 == v]
        best.append(v)
        optimizers.append(tuple(sorted(optimizers[n - d] + (d,))))
        maximizing_counts.append(len(winners))
        candidate = two_candidates(n)
        assert value(candidate) == v, (n, candidate, optimizers[n])
        eventual = residue_optimizer(n)
        if eventual is not None:
            assert value(eventual) == v, (n, eventual, optimizers[n])
        if n >= 100:
            assert eventual is not None
        rows.append({
            "dimension": n,
            "optimal_dimensions": " ".join(map(str, optimizers[n])),
            "two_candidate_dimensions": " ".join(map(str, candidate)),
            "residue_formula_available": eventual is not None,
            "ratio_to_simplex_numerator": str((v / c(n)).numerator),
            "ratio_to_simplex_denominator": str((v / c(n)).denominator),
        })

    assert all(best[n] == c(n) for n in range(1, min(20, limit + 1)))
    if limit >= 20:
        assert best[20] > c(20) and optimizers[20] == (10, 10)
    # At n=99 the periodic upper envelope is not attainable; N=100 is sharp.
    assert residue_optimizer(99) is None
    for n in range(112, limit + 1, 13):
        alternative = (12,) * 5 + (13,) * ((n - 60) // 13)
        assert best[n] / value(alternative) == gamma

    (out / "exact_certificates.json").write_text(
        json.dumps(records, indent=2) + "\n", encoding="utf-8")
    initial = {}
    for n in range(13, 21):
        v = value(balanced(n, 2)) / c(n)
        lo = 10**6 * v.numerator // v.denominator
        assert Fraction(lo, 10**6) <= v < Fraction(lo + 1, 10**6)
        assert (v < 1) if n < 20 else (v > 1)
        initial[n] = {
            "balanced_dimensions": balanced(n, 2),
            "numerator": str(v.numerator),
            "denominator": str(v.denominator),
            "weak_lower_numerator_over_1000000": lo,
            "strict_upper_numerator_over_1000000": lo + 1,
        }
    (out / "initial_comparisons.json").write_text(
        json.dumps(initial, indent=2) + "\n", encoding="utf-8")
    if rows:
        with (out / "optimal_products.csv").open("w", newline="", encoding="utf-8") as f:
            writer = csv.DictWriter(f, fieldnames=list(rows[0]))
            writer.writeheader()
            writer.writerows(rows)
    print(json.dumps({
        "status": "PASS",
        "all_rational_certificates": len(records),
        "dynamic_program_dimensions": limit,
        "first_product_improvement": 20 if limit >= 20 else None,
        "periodic_formula_uniform_threshold": 100,
        "sharp_gap": str(gamma),
    }, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=300)
    parser.add_argument("--output", type=Path, default=Path(__file__).parent / "certificates")
    args = parser.parse_args()
    run(args.limit, args.output)
