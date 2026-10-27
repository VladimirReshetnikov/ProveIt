#!/usr/bin/env python3
"""Reproduce the certificate comparison and finite abstract partition counts.

Counts below describe a weighted mode pool, not measured SAT running times.
All tuple counts and exact-weight indexing checks use integer arithmetic.
Floating-point values are used only to display analytic constants/logarithms.
"""
from __future__ import annotations

import csv
import itertools
import json
import math
from fractions import Fraction
from pathlib import Path

from exact_weight_index import ExactWeightIndex
from verify_mode_graph import schedule_constants


def mode_weight(q: int, slope: int) -> int:
    if slope == 1:
        return q + 1
    if slope == 2:
        return 1 + 2 * q - q.bit_count()
    if slope == 3:
        return 1 + 3 * q - 2 * q.bit_count()
    if slope == 4:
        return 1 + 4 * q - 2 * q.bit_count()
    raise ValueError("unknown mode basis")


def abstract_count(precision: int, colors: int, slope: int) -> int:
    coefficients = [0] * precision
    coefficients[0] = 1
    q = 0
    while mode_weight(q, slope) < precision:
        weight = mode_weight(q, slope)
        for _ in range(colors):
            for total in range(weight, precision):
                coefficients[total] += coefficients[total - weight]
        q += 1
    return sum(coefficients)


def verify_indexing() -> dict:
    examples = [(), (1,), (2,), (1, 3), (2, 2, 6), (3, 5, 8), (1, 3, 3, 7)]
    totals_checked = vectors_checked = 0
    for weights in examples:
        indexer = ExactWeightIndex(weights, 16)
        for total in range(17):
            expected = [t for t in itertools.product(
                *(range(total // w + 1) for w in weights))
                if sum(w * e for w, e in zip(weights, t)) == total]
            actual = list(indexer.tuples(total))
            if actual != expected or len(actual) != indexer.count(total):
                raise ArithmeticError(("exact-weight enumeration", weights, total))
            totals_checked += 1
            for rank, vector in enumerate(actual):
                if indexer.rank(vector) != (total, rank):
                    raise ArithmeticError(("ranking", weights, vector))
                vectors_checked += 1
    rejected = 0
    for weights, maximum in [((0,), 2), ((-1, 2), 4), ((1,), -1)]:
        try:
            ExactWeightIndex(weights, maximum)
        except ValueError:
            rejected += 1
        else:
            raise ArithmeticError("invalid indexer was accepted")
    return {"status": "PASS", "exact_weight_totals_checked": totals_checked,
            "rank_unrank_vectors_checked": vectors_checked,
            "invalid_inputs_rejected": rejected}


def family_infimum() -> dict:
    # This is the already-described continuous boundary family. An integer
    # group count and a strict packing margin are needed for an algorithm.
    def derivative_equation(r):
        return (r / 6) ** (2 / 3) - 1 - 2 * math.log(r)
    lo, hi = 200.0, 300.0
    for _ in range(80):
        mid = (lo + hi) / 2
        if derivative_equation(mid) > 0:
            hi = mid
        else:
            lo = mid
    r = (lo + hi) / 2
    geometric = (2 * math.pi * math.sqrt(480 * math.log2(r)) /
                 (math.log(2) * (1 - (6 / r) ** (2 / 3)) ** 1.5))
    return {"continuous_r_approx": r,
            "geometric_boundary_infimum_approx": geometric,
            "existing_slope3_boundary_infimum_approx": geometric / math.sqrt(3),
            "new_slope4_boundary_infimum_approx": geometric / 2,
            "scope": "Numerical evaluation of a specified boundary certificate family, not an attained boundary algorithm or a runtime lower bound."}


def exact_rounded_certificates() -> dict:
    """Certify the convenient rounded bounds without floating-point tests.

    The classical bound pi < 22/7 is the sole supplied transcendental
    inequality; the needed bounds on ln(2), sqrt(12), and log_2(7) are
    reduced below to positive rational series terms and integer powers.
    """
    ln2_lower = Fraction(6931, 10000)
    series_lower = 2 * sum(
        (Fraction(1, (2*j+1) * 3**(2*j+1)) for j in range(4)), Fraction())
    if not series_lower > ln2_lower:
        raise ArithmeticError("logarithm lower bound failed")
    if not Fraction(12) < Fraction(52, 15)**2:
        raise ArithmeticError("gamma upper bound failed")
    if not 7**100 < 2**281:
        raise ArithmeticError("Strassen exponent upper bound failed")
    kappa_squared_upper = Fraction(22, 7)**2 * 4200 / ln2_lower**2
    fast_squared_upper = Fraction(43690, 65536) - (
        (1 - Fraction(81, 100)**2) * Fraction(14450, 65536))
    bounds = {
        "polynomial_space_time": (320, kappa_squared_upper / Fraction(147, 160)**2),
        "cached_strassen_time": (226, kappa_squared_upper * fast_squared_upper),
        "cached_strassen_space": (197, kappa_squared_upper * Fraction(29240, 65536)),
    }
    records = {}
    for name, (limit, squared_upper) in bounds.items():
        margin = limit**2 - squared_upper
        if margin <= 0:
            raise ArithmeticError(("rounded coefficient failed", name))
        records[name] = {"coefficient_strictly_below": limit,
                         "squared_rational_upper_bound": str(squared_upper),
                         "squared_rational_margin": str(margin)}
    return {"status": "PASS", "ln2_four_term_lower_bound": str(series_lower),
            "pi_upper_bound_used": "22/7", "certificates": records}


def main():
    root = Path(__file__).resolve().parents[1]
    out = root / "results"
    out.mkdir(exist_ok=True)
    rows = []
    for colors in (1, 4, 16):
        for precision in (64, 128, 256, 512):
            counts = [abstract_count(precision, colors, slope) for slope in range(1, 5)]
            if not all(counts[j] >= counts[j + 1] for j in range(3)):
                raise ArithmeticError("mode-count monotonicity failed")
            row = {"colors": colors, "precision": precision}
            for slope, count in enumerate(counts, 1):
                row[f"slope{slope}_count"] = str(count)
                row[f"slope{slope}_log2_count"] = math.log2(count)
            row["log_count_ratio_4_to_3"] = math.log2(counts[3]) / math.log2(counts[2])
            rows.append(row)
    with (out / "mode_count_comparison.csv").open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    summary = {"status": "PASS", "scope": "Analytic coefficient evaluations and exact finite abstract mode counts, not SAT benchmarks.",
               "constants": schedule_constants(), "existing_schedule_family": family_infimum(),
               "exact_rounded_certificates": exact_rounded_certificates(),
               "indexing_checks": verify_indexing(), "partition_models_checked": len(rows),
               "mode_count_rows": rows}
    (out / "certificate_comparison.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": "PASS", "partition_models_checked": len(rows),
                      "indexing_checks": summary["indexing_checks"],
                      "output": str(out / "certificate_comparison.json")}, sort_keys=True))


if __name__ == "__main__":
    main()
