#!/usr/bin/env python3
"""Exact and floating-point checks for exponential-feedback transseries.

Exact integer arithmetic computes A[n] = n! [q^n] U, where
    U = sum_{j>=1} q**j * exp(lambda[j] * U).
An independent partition implementation checks the Lagrange formula.
Floating-point envelope values are diagnostics, NOT interval certificates.
"""
from __future__ import annotations

import argparse
import csv
import json
import math
from fractions import Fraction
from pathlib import Path
from typing import Iterator, Sequence


def coefficients(slopes: Sequence[int], order: int) -> list[int]:
    """Return exact factorial-scaled coefficients through the given order.

    slopes[0] is unused.  All slopes must be nonnegative integers.
    Time O(order**3) arithmetic operations; memory O(order**2) integers.
    """
    if order < 1 or len(slopes) <= order:
        raise ValueError("Provide at least order+1 slopes, including index zero")
    if any(not isinstance(x, int) or x < 0 for x in slopes[1:order + 1]):
        raise ValueError("Exact mode requires nonnegative integer slopes")
    factorials = [math.factorial(n) for n in range(order + 1)]
    scaled = [0] * (order + 1)
    exponentials = [[1] for _ in range(order + 1)]
    for n in range(1, order + 1):
        value = factorials[n]  # j=n, constant coefficient of the exponential
        for j in range(1, n):
            k = n - j
            row = exponentials[j]
            assert len(row) == k
            entry = slopes[j] * sum(
                math.comb(k - 1, r - 1) * scaled[r] * row[k - r]
                for r in range(1, k + 1)
            )
            row.append(entry)
            value += (factorials[n] // factorials[k]) * entry
        scaled[n] = value
    return scaled


def partitions(total: int, minimum: int = 1) -> Iterator[tuple[int, ...]]:
    if total == 0:
        yield ()
    else:
        for first in range(minimum, total + 1):
            for rest in partitions(total - first, first):
                yield (first,) + rest


def partition_coefficient(slopes: Sequence[int], n: int) -> Fraction:
    answer = Fraction(0)
    for partition in partitions(n):
        multiplicities: dict[int, int] = {}
        for j in partition:
            multiplicities[j] = multiplicities.get(j, 0) + 1
        k = len(partition)
        slope_sum = sum(slopes[j] for j in partition)
        denominator = math.prod(math.factorial(m) for m in multiplicities.values())
        answer += Fraction(slope_sum ** (k - 1), denominator)
    return answer


def quadratic_envelope(n: int) -> tuple[float, float, int]:
    """Log lower and upper bounds, evaluated in ordinary floating point.

    The inequalities themselves are proved in the article. Rounding is not
    directed, so returned decimal numbers are illustrative approximations.
    """
    import numpy as np
    from scipy.special import gammaln, logsumexp

    k = np.arange(1, n + 1, dtype=float)
    r = n - k + 1.0
    slope_sum = r*r + k - 1.0
    log_upper_rows = (
        gammaln(n) - gammaln(k) - gammaln(r)
        + (k - 1.0) * np.log(slope_sum) - gammaln(k + 1.0)
    )
    log_lower_rows = (k - 1.0) * np.log(slope_sum) - gammaln(k)
    # r=1 has only one composition, not k distinct placements.
    log_lower_rows[-1] = (n - 1.0) * math.log(n) - math.lgamma(n + 1)
    index = int(np.argmax(log_lower_rows))
    return float(log_lower_rows[index]), float(logsumexp(log_upper_rows)), n-index


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    # Editorial amendment (ProveIt, 2026-09-29): default 120 matches the recorded
    # run, so a bare run no longer overwrites the degree-120 tables with shorter ones.
    parser.add_argument("--order", type=int, default=120)
    parser.add_argument("--out", type=Path, default=Path(__file__).resolve().parents[1] / "data")
    args = parser.parse_args()
    if args.order < 12:
        parser.error("--order must be at least 12 for the independent checks")
    args.out.mkdir(parents=True, exist_ok=True)
    nmax = args.order
    slopes = [j*j for j in range(nmax + 1)]
    scaled = coefficients(slopes, nmax)
    checks = []
    for n in range(1, 13):
        direct = Fraction(scaled[n], math.factorial(n))
        independent = partition_coefficient(slopes, n)
        assert direct == independent, (n, direct, independent)
        checks.append({"n": n, "coefficient": str(direct), "partition_match": True})
    zero = coefficients([0] * (nmax + 1), 12)
    assert all(zero[n] == math.factorial(n) for n in range(1, 13))
    linear = coefficients(list(range(nmax + 1)), 12)
    for n in range(1, 13):
        # U=q(1+U)e^U, using an independent finite Lagrange sum.
        value = sum(Fraction(math.comb(n, j) * n**(n - 1 - j),
                             n * math.factorial(n - 1 - j))
                    for j in range(n))
        assert value == Fraction(linear[n], math.factorial(n))
    with (args.out / "quadratic_coefficients.csv").open("w", newline="") as file:
        writer = csv.writer(file, lineterminator="\n")  # LF on every platform (ProveIt, 2026-09-29)
        writer.writerow(["n", "factorial_scaled_coefficient", "coefficient", "normalized_log", "log_coefficient"])
        for n in range(1, nmax + 1):
            log_u = math.log(scaled[n]) - math.lgamma(n + 1)
            normalized = log_u/n - math.log(n) + 2*math.log(math.log(n)) if n > 1 else ""
            writer.writerow([n, scaled[n], str(Fraction(scaled[n], math.factorial(n))), normalized, log_u])
    with (args.out / "quadratic_envelopes.csv").open("w", newline="") as file:
        writer = csv.writer(file, lineterminator="\n")  # LF on every platform (ProveIt, 2026-09-29)
        writer.writerow(["n", "normalized_log_lower", "normalized_log_upper", "maximizing_large_action", "scaled_large_action"])
        for n in [100, 1000, 10000, 100000, 1000000]:
            low, high, action = quadratic_envelope(n)
            shift = -math.log(n) + 2*math.log(math.log(n))
            writer.writerow([n, low/n + shift, high/n + shift, action, action*math.log(n)/n])
    result = {
        "exact_partition_checks": checks,
        "zero_slope_checks": 12,
        "linear_slope_checks": 12,
        "quadratic_exact_order": nmax,
        "quadratic_logarithmic_constant": 2*math.log(2)-1,
        "status": "All exact checks passed. Floating-point tables are diagnostics, not proofs."
    }
    (args.out / "verification.json").write_text(json.dumps(result, indent=2) + "\n", newline="\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
