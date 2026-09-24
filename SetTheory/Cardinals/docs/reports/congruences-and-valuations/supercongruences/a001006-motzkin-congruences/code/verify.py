"""Reproduce the finite checks in the article (Python 3.9+, no dependencies).

The main oracle is the exact integer Motzkin recurrence. Tested congruences
are NOT used to manufacture their own expected input values. Small inputs
are independently checked using binomial sums and path dynamic programming.
Finite computation supplements, but does not replace, the proofs.
"""
from __future__ import annotations

import argparse
import csv
import json
import platform
from collections import Counter
from math import comb
from pathlib import Path

from motzkin import (
    block_mod_prime_power, central_trinomial_numbers, motzkin_binomial,
    motzkin_mod_prime, motzkin_numbers, primes_up_to,
    trinomial_binomial, trinomial_prime_table,
)


def run(max_index: int, prime_limit: int, output: Path) -> dict:
    if max_index < 200 or prime_limit < 7:
        raise ValueError("require max-index >= 200 and prime-limit >= 7")
    counts = Counter()

    def check(name: str, actual: int, expected: int, modulus: int = 0) -> None:
        valid = ((actual - expected) % modulus == 0) if modulus else (actual == expected)
        if not valid:
            raise AssertionError((name, actual, expected, modulus))
        counts[name] += 1

    # Division takes place over the integers, before any modular reduction.
    M = motzkin_numbers(max_index)
    T = central_trinomial_numbers(max_index + 2)
    U = [(T[n + 1] - T[n]) // 2 for n in range(max_index + 1)]
    primes = [p for p in primes_up_to(prime_limit) if p > 2]
    for n in range(151):
        check("exact_binomial_M", M[n], motzkin_binomial(n))
        check("exact_binomial_T", T[n], trinomial_binomial(n))
    for n in range(max_index + 1):
        check("three_trinomial_identity", 2 * M[n],
              3 * T[n] + 2 * T[n + 1] - T[n + 2])

    # Count nonnegative paths independently for n <= 80.
    heights = [1]
    for n in range(81):
        check("path_dynamic_programming", heights[0], M[n])
        next_heights = [0] * (len(heights) + 1)
        for h, count in enumerate(heights):
            next_heights[h] += count
            next_heights[h + 1] += count
            if h:
                next_heights[h - 1] += count
        heights = next_heights

    boundaries = []
    for p in primes:
        eps = 0 if p == 3 else (1 if p % 3 == 1 else -1)
        table = trinomial_prime_table(p)
        for n in range(min(1200, max_index) + 1):
            check("digit_algorithm", motzkin_mod_prime(n, p, table), M[n], p)
        if p > 3:
            for m in range(1, min(101, max_index // p + 1)):
                check("trinomial_prime_square", T[m * p], T[m], p * p)
                check("neighbor_prime_square", U[m * p],
                      m * p * (T[m] + 3 * eps * T[m - 1]) * pow(2, -1, p * p),
                      p * p)
            for m in range(1, 15):
                for j in range(m + 1):
                    check("Babbage", comb(m * p, j * p), comb(m, j), p * p)
        q = p
        r = 1
        while q - 2 <= max_index:
            c = (eps ** r - 1) * pow(2, -1, p)
            for m in range(1, min(13, (max_index + 2) // q + 1)):
                check("unified_boundary", M[m * q - 2], c * T[m - 1] - U[m - 1], p)
                if p % 6 == 1:
                    check("Bala_1", M[m * q - 2], -U[m - 1], p)
                if p % 6 == 5 and r == 1:
                    check("Bala_2", M[m * p - 2], -(T[m - 1] + U[m - 1]), p)
            if 2 * q - 2 <= max_index:
                for d in range(q - 2):
                    check("Bala_3", M[q + d], M[d], p)
                check("sharp_mod_p_boundary", M[2 * q - 2] - M[q - 2], -1, p)
            if p > 3 and r >= 2:
                w = q // p
                if q + w - 2 <= max_index:
                    for d in range(w - 2):
                        check("Bala_4", M[q + d], M[d], p * p)
                    delta = (M[q + w - 2] - M[w - 2]) % (p * p)
                    expected = (-p * (1 + 3 * eps) // 2) % (p * p)
                    check("sharp_mod_p2_boundary", delta, expected)
                    if delta == 0:
                        raise AssertionError("The first omitted term must fail")
                    boundaries.append(dict(p=p, k=r, first_excluded=w - 2,
                                           observed_defect=delta, expected_defect=expected))
            q *= p
            r += 1

    # Check the entire local block, including both boundary corrections.
    for p in [3, 5, 7, 11, 13]:
        for s in range(1, 5):
            for k in range(s, 9):
                q = p ** (k - s + 1)
                for m in range(1, 5):
                    base = m * p ** k
                    h = m * p ** (s - 1)
                    if base + q - 1 > max_index:
                        continue
                    for d in range(q):
                        predicted = T[h] * M[d]
                        if d == q - 2:
                            predicted -= U[h]
                        elif d == q - 1:
                            predicted -= (q - 1) * U[h]
                        check("full_prime_power_block", M[base + d], predicted, p ** s)
                        if s == 2 and p >= 5 and d <= q - 3:
                            check("multiplier_mod_p2", M[base + d], T[m] * M[d], p * p)
                    for d in sorted(set([0, max(0, q - 3), q - 2, q - 1])):
                        check("block_implementation", block_mod_prime_power(m, k, d, p, s),
                              M[base + d], p ** s)

    # Explicit failures of tempting, but invalid, strengthenings.
    check("failure_at_p3", M[9], 7, 9)
    check("failure_mod_p3", M[125], 51, 125)
    check("precision2_first_failure", M[28] - M[3], 5, 25)

    # Large-index examples produced by the proved digit algorithm, not
    # independent verification against gigantic exact Motzkin numbers.
    large_n = 10 ** 100 + 123456789
    huge_examples = {str(p): motzkin_mod_prime(large_n, p) for p in [5, 7, 11, 97]}
    output.mkdir(parents=True, exist_ok=True)
    report = dict(
        status="PASS", python=platform.python_version(), max_exact_index=max_index,
        prime_limit=prime_limit, checks=dict(sorted(counts.items())),
        total_checks=sum(counts.values()),
        boundary_rows=len(boundaries),
        limitations="Finite exact-arithmetic checks, not formal proof-assistant verification.",
        huge_index=str(large_n), huge_index_residues=huge_examples,
        huge_index_note="These are algorithm outputs, not independent exact-oracle checks."
    )
    (output / "verification.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    with (output / "sharp_boundaries.csv").open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=["p", "k", "first_excluded", "observed_defect", "expected_defect"])
        writer.writeheader()
        writer.writerows(boundaries)
    with (output / "initial_values.csv").open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(["n", "M_n_A001006", "T_n_A002426", "U_n_A005717_extended", "D_n_A005773"])
        for n in range(201):
            writer.writerow([n, M[n], T[n], U[n], 1 if n == 0 else T[n - 1] + U[n - 1]])
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-index", type=int, default=20000)
    parser.add_argument("--prime-limit", type=int, default=97)
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parents[1] / "data")
    args = parser.parse_args()
    report = run(args.max_index, args.prime_limit, args.output)
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
