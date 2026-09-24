#!/usr/bin/env python3
"""Reproduce exact tests and data. No network or third-party modules needed."""
from __future__ import annotations

import argparse
import csv
import json
import platform
from fractions import Fraction
from pathlib import Path
from time import perf_counter

from carries import (a000139, automaton_valuation, carry_count, dyadic_histograms,
                     fibonacci, histogram_below, is_odd_term, least_positive_index,
                     v2, valuation)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true", help="smaller exhaustive ranges")
    parser.add_argument("--out", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data")
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    start = perf_counter()
    digits = 15 if args.quick else 20
    direct_limit = 250 if args.quick else 2000
    auto_digits = 12 if args.quick else 18
    report: dict[str, object] = {"python": platform.python_version(), "quick": args.quick}

    # Independent integer quotient versus all three valuation methods.
    for n in range(direct_limit + 1):
        a = a000139(n)
        assert v2(a) == valuation(n) == automaton_valuation(n)
        assert (a % 2 == 1) == is_odd_term(n)
        assert valuation(n) == 1 - v2(n + 1) + carry_count(n)
    report["direct_factorial_quotient_indices"] = [0, direct_limit]

    # A million digit-formula entries versus parity and exact distributions.
    hists = dyadic_histograms(256)
    count = [0] * (digits + 2)
    for n in range(1 << digits):
        r = valuation(n)
        assert r >= 0
        assert (r == 0) == is_odd_term(n)
        count[r] += 1
        if ((n + 1) & n) == 0:
            m = (n + 1).bit_length() - 1
            p = hists[m]
            assert count[:len(p)] == p
            assert not any(count[len(p):])
    report["exhaustive_digit_formula_and_parity_bound"] = 1 << digits
    report["dyadic_enumeration_m_range"] = [0, digits]

    for n in range(1 << auto_digits):
        assert automaton_valuation(n) == valuation(n)
        assert 1 - v2(n + 1) + carry_count(n) == valuation(n)
    report["independent_carry_and_automaton_bound"] = 1 << auto_digits

    # Every small arbitrary bound, independent of the dyadic recurrence.
    running = [0]
    dp_limit = 256 if args.quick else 2048
    assert histogram_below(0) == [0]
    for bound in range(1, dp_limit + 1):
        r = valuation(bound - 1)
        if len(running) <= r:
            running += [0] * (r + 1 - len(running))
        running[r] += 1
        assert histogram_below(bound) == running
    report["all_arbitrary_bounds_through"] = dp_limit

    for m in range(257):
        p = hists[m]
        assert sum(p) == 2 ** m
        assert p[0] == fibonacci(m)
        assert histogram_below(2 ** m) == p
        mu = Fraction(sum(r * a for r, a in enumerate(p)), 2 ** m)
        ev2 = Fraction(sum(r * r * a for r, a in enumerate(p)), 2 ** m)
        emu = Fraction(m, 2) - Fraction(2, 3) + Fraction(9 + (-1) ** m, 6 * 2 ** m)
        assert mu == emu
        if m:
            evar = (Fraction(11 * m, 12) - Fraction(23, 9)
                    + Fraction(27 - (-1) ** m, 6 * 2 ** m)
                    - Fraction((9 + (-1) ** m) ** 2, 36 * 4 ** m))
            assert ev2 - mu ** 2 == evar
        else:
            assert ev2 - mu ** 2 == 0
        if m >= 3:
            assert len(p) - 1 == m and p[-1] == fibonacci(m - 2)
    report["digit_DP_recurrence_moments_and_extremes_m_range"] = [0, 256]

    # Exhaustive least-index tests for all reachable small valuations.
    first: dict[int, int] = {}
    for n in range(1, 1 << auto_digits):
        first.setdefault(valuation(n), n)
    for r, n in first.items():
        assert n == least_positive_index(r)
    report["least_positive_indices_exhaustively_verified_r"] = sorted(first)

    # Large-index tests of the explicit minimizer (not exhaustive minimality).
    for r in range(3, 1001):
        assert valuation(least_positive_index(r)) == r
    report["large_formula_witness_r_range_not_exhaustive_minimality"] = [3, 1000]

    with (args.out / "initial_terms.csv").open("w", newline="") as fh:
        writer = csv.writer(fh)
        writer.writerow(["n", "binary_n", "a_n", "valuation", "odd"])
        for n in range(201):
            writer.writerow([n, format(n, "b"), a000139(n), valuation(n), int(is_odd_term(n))])
    with (args.out / "dyadic_histograms.csv").open("w", newline="") as fh:
        writer = csv.writer(fh)
        writer.writerow(["m", "valuation", "count"])
        for m, p in enumerate(hists):
            for r, count in enumerate(p):
                writer.writerow([m, r, count])
    with (args.out / "least_indices.csv").open("w", newline="") as fh:
        writer = csv.writer(fh)
        writer.writerow(["valuation", "least_positive_index", "binary_index"])
        for r in range(65):
            n = least_positive_index(r)
            writer.writerow([r, n, format(n, "b")])
    report["large_arbitrary_bound"] = str(10 ** 100)
    big = histogram_below(10 ** 100)
    assert sum(big) == 10 ** 100
    (args.out / "histogram_below_10_pow_100.json").write_text(
        json.dumps({"exclusive_bound": str(10 ** 100), "counts_by_valuation": big}, indent=2) + "\n")
    report["all_tests_passed"] = True
    report["elapsed_seconds"] = round(perf_counter() - start, 3)
    (args.out / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
