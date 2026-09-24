#!/usr/bin/env python3
"""Exact reproducibility checks for the accompanying log-concavity article.

Python 3.9+; standard library only. No network access and no floating-point
arithmetic is used to determine a coefficient, determinant, or certified sign.
The finite tests supplement, and do not replace, the proofs in article.pdf.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
import platform
import sys
import time
from fractions import Fraction
from pathlib import Path
from typing import List, Sequence


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def invert_transform(weights: Sequence[int], u: int = 1) -> List[int]:
    """weights[k] is g(k), with unused weights[0]. Return a[0..N]."""
    require(u > 0, "u must be positive")
    a = [1]
    for n in range(1, len(weights)):
        a.append(u * sum(weights[k] * a[n - k] for k in range(1, n + 1)))
    return a


def determinants(a: Sequence[int]) -> List[int]:
    return [a[n] * a[n] - a[n - 1] * a[n + 1]
            for n in range(1, len(a) - 1)]


def divisor_sums(d: int, nmax: int) -> List[int]:
    require(d >= 0 and nmax >= 0, "nonnegative integer inputs required")
    result = [0] * (nmax + 1)
    for k in range(1, nmax + 1):
        value = k ** d
        for n in range(k, nmax + 1, k):
            result[n] += value
    return result


def eulerian(d: int) -> List[int]:
    """E_d(z), constant coefficient first; d >= 1."""
    require(d >= 1, "d must be positive")
    a = [1]
    for k in range(1, d):
        b = [0] * (len(a) + 1)
        for j, value in enumerate(a):
            b[j] += (j + 1) * value
            b[j + 1] += (k - j) * value
        a = b
    return a


def power_rational_coefficients(d: int, u: int, nmax: int) -> List[int]:
    """Independent coefficient extraction from the rational generating function."""
    if d == 0:
        return [1] + [u * (u + 1) ** (n - 1) for n in range(1, nmax + 1)]
    numerator = [(-1) ** j * math.comb(d + 1, j) for j in range(d + 2)]
    denominator = numerator[:]
    for j, value in enumerate(eulerian(d)):
        denominator[j + 1] -= u * value
    a = []
    for n in range(nmax + 1):
        value = numerator[n] if n < len(numerator) else 0
        value -= sum(denominator[j] * a[n - j]
                     for j in range(1, min(n, len(denominator) - 1) + 1))
        a.append(value)
    return a


def square_determinant_stream(nmax: int):
    """Yield exact (n, Delta_n), using O(1) big integers of working memory."""
    for n, value in ((1, -4), (2, 7), (3, 9), (4, -9)):
        if n <= nmax:
            yield n, value
    d2, d3, d4 = 7, 9, -9
    for n in range(5, nmax + 1):
        d2, d3, d4 = d3, d4, 2 * d4 - 4 * d3 + d2
        yield n, d4


def lambert_negative_certificate(d: int, r: Fraction, nmax: int = 600):
    """Enclose L_d(-r) by a rational partial sum plus a rigorous absolute tail.

    sigma_d(n) <= n**(d+1). For n >= N+1, consecutive terms of the
    majorant n**(d+1) * r**n have ratio at most qtail < 1.
    """
    weights = divisor_sums(d, nmax)
    partial = Fraction(0)
    for n in range(nmax, 0, -1):
        partial = (partial + weights[n]) * (-r)
    qtail = r * Fraction(nmax + 2, nmax + 1) ** (d + 1)
    require(qtail < 1, "increase truncation order for this r,d")
    tail = Fraction((nmax + 1) ** (d + 1)) * r ** (nmax + 1) / (1 - qtail)
    return partial, tail


def cubic_discriminant(b: int, c: int, d: int) -> int:
    return b*b*c*c - 4*c*c*c - 4*b*b*b*d - 27*d*d + 18*b*c*d


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=100000,
                        help="number of square determinants to classify (default: 100000)")
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parent / "data")
    args = parser.parse_args()
    if args.limit < 100:
        parser.error("--limit must be at least 100")
    args.output.mkdir(parents=True, exist_ok=True)
    started = time.perf_counter()
    report = {"python": platform.python_version(), "square_limit": args.limit}
    print("Exact arithmetic verification for geometric-transform log-concavity")
    print("Python:", platform.python_version())
    print("All assertions below are checked with integers or rational numbers.")

    # Square coefficients: direct convolution versus rational coefficient extraction.
    check_limit = 600
    square = invert_transform([0] + [n*n for n in range(1, check_limit + 2)])
    square_independent = power_rational_coefficients(2, 1, check_limit + 1)
    require(square == square_independent, "square coefficient mismatch")
    exact_delta = determinants(square)
    require(exact_delta == [v for _, v in square_determinant_stream(check_limit)],
            "square determinant recurrence mismatch")
    require(square[:10] == [1, 1, 5, 18, 63, 221, 776, 2725, 9569, 33602],
            "square initial data mismatch")
    require(exact_delta[:8] == [-4, 7, 9, -9, -47, -49, 81, 311],
            "determinant initial data mismatch")
    report["independent_square_checks"] = check_limit
    print(f"PASS: direct convolution and rational recurrence agree through a_{check_limit+1}.")
    print(f"PASS: direct determinants and order-three recurrence agree through Delta_{check_limit}.")

    # Polynomial identities and independent extraction for the power family.
    count = 0
    for d in range(0, 13):
        for u in (1, 2, 3):
            direct = invert_transform([0] + [n**d for n in range(1, 122)], u)
            independent = power_rational_coefficients(d, u, 121)
            require(direct == independent, f"power coefficient mismatch d={d},u={u}")
            ds = determinants(direct)
            if d == 0:
                require(ds[0] == -u and all(x == 0 for x in ds[1:]), "d=0 classification")
            if d == 1:
                require(ds[0] == -2*u and all(x == u*u for x in ds[1:]), "d=1 classification")
            count += 1
    for d in range(1, 31):
        e = eulerian(d)
        require(e == e[::-1], f"Eulerian reciprocity d={d}")
        require(all(x > 0 for x in e) and sum(e) == math.factorial(d), "Eulerian identities")
        for u in (1, 2, 3):
            denominator = [(-1)**j * math.comb(d+1, j) for j in range(d+2)]
            for j, value in enumerate(e):
                denominator[j+1] -= u*value
            require(sum(denominator) == -u*math.factorial(d), "D(1) identity")
            if d % 2:
                require(denominator == denominator[::-1], "odd d denominator reciprocity")
    report["power_parameter_pairs_checked"] = count
    print(f"PASS: {count} power-family parameter pairs checked independently through a_121.")
    print("PASS: Eulerian identities through d=30; denominator reciprocity for odd d.")

    # Check divisor sums against enumeration and verify the exact parity identity.
    for d in range(0, 11):
        sigma = divisor_sums(d, 600)
        for n in range(1, 301):
            require(sigma[n] == sum(k**d for k in range(1, n+1) if n % k == 0),
                    "divisor sieve mismatch")
            rhs = (1 + 2**d) * sigma[n] - (2**d * sigma[n//2] if n % 2 == 0 else 0)
            require(sigma[2*n] == rhs, "divisor parity identity mismatch")
    print("PASS: divisor enumeration and parity identity for d=0..10, n=1..300.")

    certificate_rows = []
    exact_certificates = []
    for d in range(0, 11):
        r = Fraction(9, 10)
        partial, tail = lambert_negative_certificate(d, r)
        require(partial - tail > 1, f"negative Lambert pole certificate failed d={d}")
        certificate_rows.append([d, "9/10", 600, float(partial), float(tail), True])
        exact_certificates.append({"d": d, "r": str(r), "truncation": 600,
                                   "partial_sum": str(partial), "tail_bound": str(tail),
                                   "lower_bound_exceeds_one": True})
    print("PASS: rigorous rational certificates L_d(-9/10)>1 for d=0..10.")
    with (args.output / "lambert_certificates.csv").open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(["d", "r", "truncation", "partial_sum_approx", "tail_bound_approx", "certified_gt_one"])
        writer.writerows(certificate_rows)
    (args.output / "lambert_certificates_exact.json").write_text(
        json.dumps(exact_certificates, indent=2) + "\n", encoding="utf-8")

    # Algebraic invariants for the exact square-case density proof.
    require(cubic_discriminant(-4, 2, -1) == -107, "cubic discriminant")
    require(all(x**3-4*x*x+2*x-1 != 0 for x in (-1, 1)), "rational root check")
    # Pair-product polynomial: roots have sum 2, pairwise sum 4, product 1.
    require((-(-4), 2, -(-1)) == (4, 2, 1), "Vieta certificate")
    require(Fraction(7, 2)**3 - 4*Fraction(7, 2)**2 + 2*Fraction(7, 2) - 1 == Fraction(-1, 8),
            "lower root endpoint")
    require(4**3 - 4*4**2 + 2*4 - 1 == 7, "upper root endpoint")
    require(Fraction(4046) < Fraction(1592, 25)**2, "four-point margin comparison")
    require(Fraction(32, 435) < Fraction(1, 10), "perturbation amplitude bound")
    print("PASS: discriminant -107, rational-root irreducibility, and exact gap-bound constants.")

    # Exact long-range signs; retain just signs, not huge coefficients.
    counts = {"positive": 0, "negative": 0, "zero": 0}
    progressions = {(m, r): [0, 0, 0] for m in range(1, 13) for r in range(m)}
    checkpoints = []
    max_runs = {1: 0, -1: 0}
    previous_sign = 0
    run = 0
    signs = bytearray()
    selected = []
    checkpoint_set = {100, 1000, 10000, 100000, args.limit}
    for n, value in square_determinant_stream(args.limit):
        sign = (value > 0) - (value < 0)
        counts["positive" if sign > 0 else "negative" if sign < 0 else "zero"] += 1
        require(n == 1 or value % 2 == 1, f"parity failure n={n}")
        require(sign != 0, f"unexpected equality n={n}")
        signs.append(43 if sign > 0 else 45)  # ASCII + or -
        for m in range(1, 13):
            progressions[(m, n % m)][0 if sign > 0 else 1 if sign < 0 else 2] += 1
        if sign == previous_sign:
            run += 1
        else:
            run, previous_sign = 1, sign
        max_runs[sign] = max(max_runs[sign], run)
        if n <= 50:
            selected.append([n, square[n], value])
        if n in checkpoint_set:
            checkpoints.append([n, counts["positive"], counts["negative"], counts["zero"],
                                counts["positive"] / n])
    report["square_counts"] = counts
    report["max_observed_sign_runs"] = {str(k): v for k, v in max_runs.items()}
    report["signs_sha256"] = hashlib.sha256(signs).hexdigest()
    print(f"PASS: Delta_1..Delta_{args.limit}: {counts}; all nonzero, all n>=2 odd.")
    print("Observed longest consecutive runs (+,-):", max_runs[1], max_runs[-1])
    require(max_runs[1] <= 3 and max_runs[-1] <= 3, "four-term-block bound")
    print("PASS: finite check of the sharp four-term-block theorem (proof in article).")
    (args.output / "square_signs.txt").write_bytes(signs + b"\n")
    for filename, header, rows in (
        ("square_initial_terms.csv", ["n", "a_n", "Delta_n"], selected),
        ("square_density_checkpoints.csv", ["N", "positive", "negative", "zero", "positive_fraction"], checkpoints),
        ("square_arithmetic_progressions.csv", ["modulus", "residue", "positive", "negative", "zero", "positive_fraction"],
         [[m, r, *value, value[0]/sum(value)] for (m, r), value in progressions.items()]),
    ):
        with (args.output / filename).open("w", newline="", encoding="utf-8") as f:
            writer = csv.writer(f)
            writer.writerow(header)
            writer.writerows(rows)

    # Small comparison table, with exact determinants independently from convolution.
    family_rows = []
    for family in ("power", "divisor"):
        for d in range(0, 9):
            weights = ([0] + [n**d for n in range(1, 502)] if family == "power"
                       else divisor_sums(d, 501))
            ds = determinants(invert_transform(weights))
            family_rows.append([family, d, 500, sum(x > 0 for x in ds),
                                sum(x < 0 for x in ds), sum(x == 0 for x in ds),
                                "".join("+" if x > 0 else "-" if x < 0 else "0" for x in ds[:30])])
    with (args.output / "family_comparison.csv").open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(["family", "d", "N", "positive", "negative", "zero", "first_30_signs"])
        writer.writerows(family_rows)
    print("PASS: exact 500-determinant comparison tables generated for both families, d=0..8.")
    report["seconds"] = round(time.perf_counter()-started, 3)
    (args.output / "verification_summary.json").write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    print("All checks passed. Elapsed seconds:", report["seconds"])
    print("Output:", args.output)


if __name__ == "__main__":
    main()
