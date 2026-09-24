#!/usr/bin/env python3
"""Exact checks for Esthetic Numbers, Folded Paths, and Algebraic Diagonals.

Python 3.10+; standard library only.  Run `python3 verify.py`.
All mathematical comparisons use integers or fractions, never floating point.
Finite checks are regression tests, not substitutes for the proofs in article.pdf.
"""
from __future__ import annotations

import argparse
import csv
import itertools
import json
import math
import platform
import time
from collections import Counter
from fractions import Fraction
from pathlib import Path


def require_integer(name: str, value: int, minimum: int = 0) -> None:
    if isinstance(value, bool) or not isinstance(value, int) or value < minimum:
        raise ValueError(f"{name} must be an integer >= {minimum}")


def digit_row(q: int, maximum_length: int) -> list[int]:
    """Counts indexed by k; index 0 is a dummy zero, NOT the extension q/2."""
    require_integer("q", q, 2)
    require_integer("maximum_length", maximum_length, 1)
    counts = [0] + [1] * (q - 1)
    result = [0, q - 1]
    for _ in range(2, maximum_length + 1):
        counts = [
            (counts[i - 1] if i else 0)
            + (counts[i + 1] if i + 1 < q else 0)
            for i in range(q)
        ]
        result.append(sum(counts))
    return result


def full_walk_row(q: int, maximum_length: int) -> list[int]:
    """All walks on the q-vertex path, indexed by number of steps."""
    counts = [1] * q
    result = [q]
    for _ in range(maximum_length):
        counts = [
            (counts[i - 1] if i else 0)
            + (counts[i + 1] if i + 1 < q else 0)
            for i in range(q)
        ]
        result.append(sum(counts))
    return result


def differential_row(n: int, maximum_order: int) -> list[int]:
    """Malešević's operation-index graph: j=i+1 or i+j=n+1 (1-based)."""
    require_integer("n", n, 1)
    successors = [
        [j - 1 for j in range(1, n + 1) if j == i + 1 or i + j == n + 1]
        for i in range(1, n + 1)
    ]
    counts = [1] * n
    result = [0, n]
    for _ in range(2, maximum_order + 1):
        next_counts = [0] * n
        for i, multiplicity in enumerate(counts):
            for j in successors[i]:
                next_counts[j] += multiplicity
        counts = next_counts
        result.append(sum(counts))
    return result


def folded_walk_row(m: int, maximum_length: int) -> list[int]:
    counts = [1] * m
    result = [m]
    for _ in range(maximum_length):
        new = [
            (counts[i - 1] if i else 0)
            + (counts[i + 1] if i + 1 < m else 0)
            for i in range(m)
        ]
        new[-1] += counts[-1]
        counts = new
        result.append(sum(counts))
    return result


def half_power(k: int) -> Fraction | int:
    return Fraction(1, 2) if k == 0 else 1 << (k - 1)


def h(k: int) -> Fraction | int:
    """The parity-dependent central-binomial term; h(0)=1/2."""
    if k % 2:
        return (k + 1) * math.comb(k, (k - 1) // 2)
    return Fraction((2 * k + 1) * math.comb(k, k // 2), 2)


def maximum_sum(k: int) -> Fraction | int:
    return h(k) - half_power(k)


def baseline(d: int, k: int) -> Fraction | int:
    return (k + d + 1) * half_power(k) - h(k)


def beta(t: int) -> int:
    return 1 if t == 0 else 4 * t


def S(k: int, e: int) -> int:
    if e < 0:
        return 0
    return sum(beta(e - 2 * ell) * math.comb(k, ell)
               for ell in range(e // 2 + 1) if ell <= k)


def P(c: int, k: int) -> int:
    require_integer("c", c, 1)
    return S(k, c - 1)


def reflection_formula(q: int, k: int) -> int:
    require_integer("q", q, 2)
    require_integer("k", k, 1)
    value = baseline(q - k, k)
    for j in range(1, k // (q + 1) + 1):
        value += (-1) ** (j - 1) * S(k, k - j * (q + 1))
    assert Fraction(value).denominator == 1
    return int(value)


def poly_trim(p: list[int]) -> list[int]:
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def x_times_minus(p: list[int], r: list[int]) -> list[int]:
    result = [0] + p
    result.extend([0] * max(0, len(r) - len(result)))
    for i, coefficient in enumerate(r):
        result[i] -= coefficient
    return poly_trim(result)


def minimal_polynomial(q: int) -> list[int]:
    """Ascending coefficients of the monic minimal positive-length recurrence."""
    require_integer("q", q, 2)
    if q % 2 == 0:
        m = q // 2
        previous, current = [1], [0, 1]  # U_0(x/2), U_1(x/2)
        for _ in range(2, m + 1):
            previous, current = current, x_times_minus(current, previous)
        result = current[:]
        for i, coefficient in enumerate(previous):
            result[i] -= coefficient
        return poly_trim(result)
    m = (q + 1) // 2
    previous, current = [2], [0, 1]  # 2T_0(x/2), 2T_1(x/2)
    for _ in range(2, m + 1):
        previous, current = current, x_times_minus(current, previous)
    if m % 2:
        assert current[0] == 0
        current = current[1:]
    return current


def catalan(n: int) -> int:
    return math.comb(2 * n, n) // (n + 1)


def a206603_gf_coefficient(k: int) -> int:
    # (1-sqrt(1-4z^2))/(2(1-2z)^2)
    return sum(catalan(j - 1) * (k - 2 * j + 1) * 2 ** (k - 2 * j)
               for j in range(1, k // 2 + 1))


def a182555_gf_coefficient(k: int) -> int:
    return 2 ** k + a206603_gf_coefficient(k)


def addition_triangle_maximum(n: int) -> int:
    weights = sorted(math.comb(n, i) for i in range(n + 1))
    numerator = sum(weight * (2 * i - n) for i, weight in enumerate(weights))
    assert numerator % 2 == 0
    return numerator // 2


def determinant_bareiss(matrix: list[list[int]]) -> int:
    a = [row[:] for row in matrix]
    n = len(a)
    if n == 0:
        return 1
    sign, denominator = 1, 1
    for k in range(n - 1):
        if a[k][k] == 0:
            pivot = next((i for i in range(k + 1, n) if a[i][k]), None)
            if pivot is None:
                return 0
            a[k], a[pivot] = a[pivot], a[k]
            sign = -sign
        p = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                numerator = a[i][j] * p - a[i][k] * a[k][j]
                quotient, remainder = divmod(numerator, denominator)
                assert remainder == 0
                a[i][j] = quotient
            a[i][k] = 0
        denominator = p
    return sign * a[-1][-1]


def check_equal(actual: object, expected: object, context: object) -> None:
    if actual != expected:
        raise AssertionError(f"Mismatch at {context}: {actual!r} != {expected!r}")


def run(output: Path) -> dict:
    started = time.perf_counter()
    counts: Counter[str] = Counter()
    output.mkdir(parents=True, exist_ok=True)
    data = output / "data"
    data.mkdir(exist_ok=True)
    rows = {q: digit_row(q, 250) for q in range(2, 263)}

    for q in range(2, 101):
        walks = full_walk_row(q, 250)
        for k in range(1, 251):
            check_equal(2 * rows[q][k], walks[k], ("reflection orbit", q, k))
            counts["path_orbit_equalities"] += 1
        polynomial = minimal_polynomial(q)
        degree = len(polynomial) - 1
        expected_degree = q // 2 if q % 2 == 0 else (q + 1) // 2 - ((q + 1) // 2) % 2
        check_equal(degree, expected_degree, ("degree", q))
        for k in range(1, 251 - degree):
            check_equal(sum(c * rows[q][k + i] for i, c in enumerate(polynomial)),
                        0, ("recurrence", q, k))
            counts["recurrence_equalities"] += 1

    for q in range(2, 42, 2):
        differential = differential_row(q - 1, 100)
        folded = folded_walk_row(q // 2, 100)
        for k in range(1, 101):
            check_equal(rows[q][k], differential[k], ("differential", q, k))
            check_equal(rows[q][k], folded[k], ("folded", q, k))
            counts["differential_equalities"] += 1
            counts["folded_equalities"] += 1

    # Exhaustive sign-word checks, independently of the transfer-matrix counts.
    for k in range(1, 17):
        ranges: Counter[int] = Counter()
        max_sum = 0
        for steps in itertools.product((-1, 1), repeat=k):
            position = low = high = 0
            for step in steps:
                position += step
                low = min(low, position)
                high = max(high, position)
            ranges[high - low] += 1
            max_sum += high
            counts["sign_words_enumerated"] += 1
        check_equal(max_sum, maximum_sum(k), ("maximum", k))
        counts["maximum_sum_equalities"] += 1
        for q in range(2, 22):
            all_walks = sum(max(q - r, 0) * count for r, count in ranges.items())
            check_equal(all_walks, 2 * rows[q][k], ("range", q, k))
            counts["range_equalities"] += 1

    for q in range(2, 41):
        for k in range(1, 151):
            check_equal(reflection_formula(q, k), rows[q][k], ("universal", q, k))
            counts["universal_formula_equalities"] += 1

    for d in range(13):
        for k in range(max(1, 2 - d), 251):
            check_equal(baseline(d, k), rows[k + d][k], ("nonnegative diagonal", d, k))
            counts["nonnegative_diagonal_equalities"] += 1

    for c in range(1, 31):
        threshold = max(c + 2, 2 * c - 1)
        for k in range(threshold, 251):
            check_equal(baseline(-c, k) + P(c, k), rows[k - c][k],
                        ("negative diagonal", c, k))
            counts["eventual_polynomial_equalities"] += 1
        if c >= 4:
            k = 2 * c - 2
            check_equal(baseline(-c, k) + P(c, k) - rows[k - c][k], 1,
                        ("sharp threshold", c, k))
            counts["sharp_threshold_equalities"] += 1
        # Verify the entire diagonal-GF coefficient description, including all
        # exceptional low indices and the artificial length-zero extensions.
        for k in range(251):
            predicted = baseline(-c, k) + P(c, k)
            if k <= c + 1:
                predicted -= baseline(-c, k) + P(c, k)
            elif k <= 2 * c - 2:
                q = k - c
                predicted += sum((-1) ** (j - 1) * S(k, k - j * (q + 1))
                                 for j in range(2, k // (q + 1) + 1))
            expected = rows[k - c][k] if k >= c + 2 else 0
            check_equal(predicted, expected, ("entire diagonal GF", c, k))
            counts["full_diagonal_gf_equalities"] += 1

    for k in range(1, 251):
        check_equal(rows[k + 2][k], a182555_gf_coefficient(k), ("A182555", k))
        counts["A182555_equalities"] += 1
    for k in range(2, 251):
        check_equal(rows[k][k], a206603_gf_coefficient(k), ("A206603 GF", k))
        check_equal(rows[k][k], addition_triangle_maximum(k), ("addition triangle", k))
        counts["A206603_equalities"] += 1
        counts["addition_triangle_equalities"] += 1

    hankel = []
    for q in range(2, 41):
        degree = len(minimal_polynomial(q)) - 1
        matrix = [[rows[q][i + j + 1] for j in range(degree)] for i in range(degree)]
        det = determinant_bareiss(matrix)
        if det == 0:
            raise AssertionError(f"Unexpected singular degree-sized Hankel matrix for q={q}")
        counts["nonsingular_hankel_minimality_checks"] += 1
        hankel.append({"q": q, "degree": degree, "determinant": det})

    with (data / "rows.csv").open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(["base_q", "length_k", "T_q_k"])
        for q in range(2, 41):
            for k in range(1, 101):
                writer.writerow([q, k, rows[q][k]])
    with (data / "diagonals.csv").open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(["offset_d", "length_k", "base_q", "T_q_k"])
        for d in range(-12, 13):
            for k in range(max(1, 2 - d), 201):
                writer.writerow([d, k, k + d, rows[k + d][k]])
    (data / "minimal_polynomials.json").write_text(json.dumps(
        [{"q": q, "ascending_coefficients": minimal_polynomial(q)}
         for q in range(2, 101)], indent=2) + "\n", encoding="utf-8")
    (data / "hankel_determinants.json").write_text(json.dumps(hankel, indent=2) + "\n",
                                                   encoding="utf-8")
    report = {
        "status": "all checks passed",
        "arithmetic": "exact integers and fractions; no floating-point comparisons",
        "python_version": platform.python_version(),
        "checks": dict(counts),
        "total_equalities_or_nonsingularity_checks": sum(v for key, v in counts.items()
                                                        if key != "sign_words_enumerated"),
        "elapsed_seconds": round(time.perf_counter() - started, 3),
        "scope": {
            "row_recurrences_and_orbit_identity": "2 <= q <= 100, 1 <= k <= 250",
            "differential_and_folded_models": "even q in [2,40], 1 <= k <= 100",
            "universal_reflection_formula": "2 <= q <= 40, 1 <= k <= 150",
            "negative_offsets": "1 <= c <= 30; all applicable k <= 250",
            "nonnegative_offsets": "0 <= d <= 12; all applicable k <= 250",
            "exhaustive_sign_words": "all 1 <= k <= 16",
            "hankel_nonsingularity": "2 <= q <= 40",
            "OEIS_GFs": "A182555 and A206603 through index 250"
        },
        "warning": "Finite checks are not proofs and cannot establish historical novelty."
    }
    (output / "verification" ).mkdir(exist_ok=True)
    (output / "verification" / "results.json").write_text(json.dumps(report, indent=2) + "\n",
                                                            encoding="utf-8")
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parent,
                        help="Output directory for exact data and verification/results.json")
    args = parser.parse_args()
    print(json.dumps(run(args.output.resolve()), indent=2))


if __name__ == "__main__":
    main()
