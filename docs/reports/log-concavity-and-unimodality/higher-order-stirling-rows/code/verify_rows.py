#!/usr/bin/env python3
"""Exact subset-triangle checks for the sharp higher-order Stirling theorem.

Uses only the Python standard library. All mathematical calculations are integer
calculations. The default run checks 224250 strict log-concavity inequalities,
compares 728 entries with an independent block-size-profile enumeration, and
evaluates 1711 instances of the full six-term fifth-order certificate.

This is the deeper but narrower of the package's two finite scans: it reaches
n = 300 for the five subset triangles. The companion ../verify.py reaches
n = 200 but covers ten triangles (subset and cycle, r = 1..5), checks the
quantitative bound, and verifies entries by generating-function convolution
rather than by block-size profiles. Neither scan range contains the other and
both are meant to be run.

Notation follows the merged article: alpha, beta, gamma are the three
fifth-order auxiliary polynomials of equation (4.11).
"""
from __future__ import annotations

import argparse
from collections import Counter
from collections.abc import Iterator
import json
from math import comb, factorial, prod
from pathlib import Path
import platform


def rows(order: int, max_n: int) -> Iterator[list[int]]:
    """Yield S^(order)[n,0..n], starting with n=0, by the defining recurrence."""
    if order < 1 or max_n < 0:
        raise ValueError("order must be positive and max_n must be nonnegative")
    previous = [1]
    yield previous
    for n in range(1, max_n + 1):
        current = [0] * (n + 1)
        for k in range(1, n + 1):
            current[k] = comb(n + (order - 1) * k - 1, order - 1) * previous[k-1]
            if k < len(previous):
                current[k] += k * previous[k]
        yield current
        previous = current


def partitions(total: int, max_parts: int, minimum: int = 1) -> Iterator[tuple[int, ...]]:
    """Nondecreasing positive integer partitions; used for block-size excesses."""
    if total == 0:
        yield ()
    elif max_parts > 0:
        for first in range(minimum, total + 1):
            for tail in partitions(total-first, max_parts-1, first):
                yield (first,) + tail


def from_block_sizes(order: int, n: int, k: int) -> int:
    """Count partitions from unordered block-size profiles, without the recurrence."""
    if order < 1 or n < 0:
        raise ValueError("invalid order or n")
    if k == 0:
        return int(n == 0)
    if not 1 <= k <= n:
        return 0
    N = n + (order - 1) * k
    answer = 0
    for excesses in partitions(n-k, k):
        sizes = [order] * (k-len(excesses)) + [order+x for x in excesses]
        counts = Counter(sizes)
        denominator = prod(factorial(size)**multiplicity * factorial(multiplicity)
                           for size, multiplicity in counts.items())
        numerator = factorial(N)
        value, remainder = divmod(numerator, denominator)
        if remainder:
            raise AssertionError("a block-profile count was nonintegral")
        answer += value
    return answer


def find_first_failure(order: int, max_n: int) -> dict | None:
    for n, row in enumerate(rows(order, max_n)):
        for k in range(1, n):
            defect = row[k]**2 - row[k-1]*row[k+1]
            if defect < 0:
                return {"order": order, "n": n, "k": k,
                        "adjacent_triple": row[k-1:k+2], "defect": defect}
    return None


def verify_certificate_instances(max_n: int) -> int:
    previous = [1]
    checked = 0
    def p(t: int) -> int:
        return t*(t-1)*(t-2)*(t-3)
    for n, row in enumerate(rows(5, max_n)):
        normalized = [factorial(4)**k * value for k, value in enumerate(row)]
        if n == 0:
            continue
        for k in range(1, n+1):
            expected = p(n+4*k-1)*previous[k-1]
            if k < len(previous):
                expected += k*previous[k]
            if normalized[k] != expected:
                raise AssertionError(f"normalized recurrence failed at {(n,k)}")
        for k in range(2, n):
            t = n+4*k-1
            a = previous[k-2]
            u, v = previous[k-1:k+1]
            z = previous[k+1] if k+1 < len(previous) else 0
            alpha = 2*t**3+9*t*t-161*t+255
            beta = 2*t*t-6*t+9
            gamma = 7*t**3-31*t*t-126*t+1080
            pieces = [25*p(t-4)*p(t+4)*(u*u-a*v),
                      25*(k*k-1)*(v*v-u*z),
                      25*p(t-4)*(k+1)*(u*v-a*z),
                      (5*v-8*alpha*u)**2,
                      96*(t-5)*beta*gamma*u*u,
                      480*beta*(n-k-1)*u*v]
            direct = 25*(normalized[k]**2-normalized[k-1]*normalized[k+1])
            if any(piece < 0 for piece in pieces) or pieces[4] <= 0:
                raise AssertionError(f"certificate has invalid signs at {(n,k)}")
            if direct != sum(pieces):
                raise AssertionError(f"full certificate equality failed at {(n,k)}")
            checked += 1
        previous = normalized
    return checked


def verify(max_n: int) -> tuple[dict, dict]:
    scans = []
    for order in range(1, 6):
        inequalities, largest_bits = 0, 0
        for n, row in enumerate(rows(order, max_n)):
            if n > 0 and (row[0] != 0 or any(x <= 0 for x in row[1:])):
                raise AssertionError("incorrect support")
            for k in range(1, n):
                if row[k]**2 <= row[k-1]*row[k+1]:
                    raise AssertionError(f"strict log-concavity failed at {(order,n,k)}")
                inequalities += 1
            largest_bits = max(largest_bits, max(x.bit_length() for x in row))
        scans.append({"order": order, "max_n": max_n,
                      "strict_inequalities_checked": inequalities,
                      "largest_entry_bit_length": largest_bits})

    independent = 0
    for order in range(1, 9):
        for n, row in enumerate(rows(order, 12)):
            for k, value in enumerate(row):
                if value != from_block_sizes(order, n, k):
                    raise AssertionError(f"independent enumeration mismatch at {(order,n,k)}")
                independent += 1

    failures = []
    for order in range(6, 21):
        witness = find_first_failure(order, 4)
        expected_n = 4 if order == 6 else 3
        if witness is None or witness["n"] != expected_n or witness["k"] != 2:
            raise AssertionError(f"unexpected first failure for order {order}")
        failures.append(witness)
    if failures[0]["adjacent_triple"] != [1,4719,23279256]:
        raise AssertionError("incorrect order-six witness")

    # Check the general third-row formula at many parameter values.
    third_row_checks = 0
    for order in range(1, 101):
        row = list(rows(order, 3))[-1]
        expected = [0, 1, comb(2*order+1, order),
                    factorial(3*order)//(6*factorial(order)**3)]
        if row != expected:
            raise AssertionError(f"third-row formula failed at order {order}")
        third_row_checks += 1
    instances = verify_certificate_instances(60)
    samples = {str(order): list(rows(order, 8)) for order in range(1,9)}
    report = {
        "status": "PASS", "arithmetic": "exact integers; no floating-point arithmetic",
        "python_version": platform.python_version(),
        "log_concavity_scans": scans,
        "total_strict_inequalities_checked": sum(s["strict_inequalities_checked"] for s in scans),
        "independent_block_profile_entries": independent,
        "independent_block_profile_ranges": {"orders": [1,8], "n": [0,12], "k": "0..n"},
        "full_fifth_order_certificate_instances": instances,
        "certificate_range": {"n": [3,60], "k": "2..n-1"},
        "third_row_formula_orders_checked": third_row_checks,
        "first_failures": failures,
        "note": "Finite checks supplement, but do not replace, the proof in article.tex.",
        "companion_scan": "verify.py covers n<=200 for ten subset and cycle triangles."
    }
    return report, samples


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=300)
    parser.add_argument("--output-dir", type=Path, default=Path("data"))
    args = parser.parse_args()
    if args.max_n < 2:
        parser.error("--max-n must be at least 2")
    report, samples = verify(args.max_n)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    (args.output_dir/"row_checks.json").write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    (args.output_dir/"sample_rows.json").write_text(json.dumps(samples, indent=2)+"\n", encoding="utf-8")
    print(f"PASS: {report['total_strict_inequalities_checked']} strict inequalities")
    print(f"PASS: {report['independent_block_profile_entries']} independent block-profile entries")
    print(f"PASS: {report['full_fifth_order_certificate_instances']} full certificate instances")
    print(f"PASS: {report['third_row_formula_orders_checked']} third-row formula checks")
    print("PASS: first counterexamples for orders 6 through 20")
    print(f"Reports written to {args.output_dir.resolve()}")


if __name__ == "__main__":
    main()
