#!/usr/bin/env python3
"""Exact finite checks for the article's density-extraction inequalities.

Uses Python's standard library only. Run:

    python verification/density_checks.py

The output JSON is written beside this script. Every calculation uses
fractions.Fraction; no floating-point tolerances are involved.

Coverage: all ordered positive compositions of N into M cells for
2 <= N <= 10 and 2 <= M <= min(4, N), with every possible count of A
inside each cell. Trivial A and configurations with zero cell variation
are excluded. Each remaining configuration is checked with both the
symmetric range [-1, 1] and the indicator range [-delta, 1-delta].
Thus 22,752 indicator/partition configurations give 45,504 range cases.
The finite checks support the proofs but are not substitutes for them.
"""

from fractions import Fraction
from itertools import product
import json
from pathlib import Path


def compositions(n, k):
    if k == 1:
        if n > 0:
            yield (n,)
        return
    for x in range(1, n - k + 2):
        for tail in compositions(n - x, k - 1):
            yield (x,) + tail


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def check_partitions():
    configurations = 0
    range_cases = 0
    per_n = {}
    F = Fraction
    for n in range(2, 11):
        count_for_n = 0
        for cell_count in range(2, min(4, n) + 1):
            for sizes in compositions(n, cell_count):
                for a_counts in product(*(range(s + 1) for s in sizes)):
                    total_a = sum(a_counts)
                    if not 0 < total_a < n:
                        continue
                    delta = F(total_a, n)
                    weights = [F(s, n) for s in sizes]
                    averages = [F(a, s) - delta
                                for a, s in zip(a_counts, sizes)]
                    variation = sum(w * abs(x)
                                    for w, x in zip(weights, averages))
                    if variation == 0:
                        continue
                    configurations += 1
                    count_for_n += 1
                    context = (n, sizes, a_counts)
                    require(sum(w * x for w, x in zip(weights, averages)) == 0,
                            f"Balance failed: {context}")
                    eta = variation / 4
                    positive_integral = variation / 2
                    for a, b in [(F(1), F(1)), (delta, 1 - delta)]:
                        S = (positive_integral -
                             eta * (1 - positive_integral / a)) / (b - eta)
                        require(S > 0, f"Unexpected nonpositive S: {context}")
                        high = [w for w, x in zip(weights, averages) if x > eta]
                        require(high and sum(high) >= S,
                                f"High-cell mass bound failed: {context}")
                        if cell_count == 2:
                            bound = positive_integral / b
                        else:
                            bound = min(positive_integral / (b * (cell_count - 1)),
                                        S / (cell_count - 2))
                        require(max(high) >= bound,
                                f"Optimal finite-M bound failed: {context}")
                        range_cases += 1
        per_n[str(n)] = count_for_n
    return configurations, range_cases, per_n


def check_extremizers():
    F = Fraction
    a = b = F(1)
    positive = negative = F(1, 5)
    cell_count = 5
    records = []
    for eta in (F(1, 100), F(1, 10)):
        S = (positive - eta * (1 - negative / a)) / (b - eta)
        first = positive / (b * (cell_count - 1))
        second = S / (cell_count - 2)
        if first <= second:
            weights = [first] * (cell_count - 1) + [1 - positive / b]
            averages = [b] * (cell_count - 1) + [-negative / (1 - positive / b)]
            branch = "two-level"
        else:
            weights = [second] * (cell_count - 2) + [1 - negative / a - S,
                                                       negative / a]
            averages = [b] * (cell_count - 2) + [eta, -a]
            branch = "three-level"
        require(all(w > 0 for w in weights), "Extremizer has a null cell")
        require(sum(weights) == 1, "Extremizer mass failed")
        require(sum(w * x for w, x in zip(weights, averages)) == 0,
                "Extremizer balance failed")
        require(sum(w * abs(x) for w, x in zip(weights, averages)) == 2 * positive,
                "Extremizer variation failed")
        largest = max(w for w, x in zip(weights, averages) if x > eta)
        require(largest == min(first, second), "Extremizer did not attain bound")
        records.append({"branch": branch, "eta": str(eta),
                        "optimal_high_cell_mass": str(largest),
                        "weights": list(map(str, weights)),
                        "cell_averages": list(map(str, averages))})
    return records


def main():
    configurations, range_cases, per_n = check_partitions()
    extremizers = check_extremizers()
    require(configurations == 22752, "Coverage count changed")
    require(range_cases == 45504, "Range-case count changed")
    results = {
        "status": "all exact checks passed",
        "arithmetic": "fractions.Fraction (exact rational arithmetic)",
        "coverage": {
            "N": "2 through 10 inclusive",
            "M": "2 through min(4, N) inclusive",
            "partitions": "all ordered positive compositions of N into M cells",
            "sets": "all cellwise A-counts, excluding trivial A and zero variation",
            "threshold": "eta = cell variation / 4",
            "ranges": ["[-1,1]", "[-delta,1-delta]"],
        },
        "indicator_partition_configurations": configurations,
        "range_cases": range_cases,
        "configurations_by_N": per_n,
        "exact_extremizers": extremizers,
    }
    output = Path(__file__).with_name("density_results.json")
    output.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(f"Passed {range_cases:,} exact range cases on "
          f"{configurations:,} indicator/partition configurations.")
    print("Both extremal branches attained exactly.")
    print(f"Results: {output.name}")


if __name__ == "__main__":
    main()
