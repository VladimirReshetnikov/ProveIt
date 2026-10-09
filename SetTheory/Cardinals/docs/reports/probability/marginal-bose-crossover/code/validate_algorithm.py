#!/usr/bin/env python3
"""Reproduce evaluator comparisons, slow-tail bounds, and inverse errors."""

from __future__ import annotations

import json
from pathlib import Path
import time

from mpmath import mp
import bose_crossover as bose


def text(x):
    return mp.nstr(x, 45)


def main():
    mp.dps = 65
    began = time.perf_counter()
    comparisons = []
    for literal in ["1", "2", "3.9", "4.5", "5", "10", "100"]:
        s = mp.mpf(literal)
        t = time.perf_counter()
        result = bose.evaluate(s, abs_tol=mp.mpf("1e-35"))
        elapsed = time.perf_counter() - t
        # A different direct-sum cutoff and a smaller asymptotic tolerance
        # provide a reproducibility cross-check beyond the radius too.
        reference = bose.accelerated_positive_sum(s, abs_tol=mp.mpf("1e-48"))
        overlap = bool(result.lower <= reference.upper and reference.lower <= result.upper)
        row = {
            "s": literal,
            "estimate": text(result.value),
            "truncation_error_bound": text(result.truncation_error_bound),
            "method": result.method,
            "degree": result.degree,
            "direct_terms": result.direct_terms,
            "reference_midpoint": text(reference.midpoint),
            "reference_bound": text(reference.truncation_error_bound),
            "absolute_difference": text(abs(result.value-reference.midpoint)),
            "truncation_intervals_overlap": overlap,
            "unaccelerated_1000_term_tail_lower_bound": text(bose.direct_sum_tail_lower_bound(s, 1000)),
            "unaccelerated_1000_term_tail_upper_bound": text(bose.direct_sum_tail_upper_bound(s, 1000)),
            "evaluation_seconds": round(elapsed, 6),
        }
        if not overlap:
            raise AssertionError(f"Incompatible estimates at s={s}")
        comparisons.append(row)

    inversions = []
    rho = mp.mpf(".1")
    for literal in [".03", ".01", ".003", ".001", ".0001"]:
        delta = mp.mpf(literal)
        solution = bose.critical_temperature(rho, delta, relative_tol=mp.mpf("1e-40"))
        _, w, t0 = bose.inverse_parameters(rho, delta)
        approximations = [bose.inverse_approximation(rho, delta, order=k) for k in range(3)]
        errors = [abs(x-solution) for x in approximations]
        inversions.append({
            "rho": text(rho), "delta": literal, "w": text(w),
            "temperature_numerical": text(solution),
            "temperature_approximations_order_0_1_2": list(map(text, approximations)),
            "absolute_errors_order_0_1_2": list(map(text, errors)),
            "second_order_scaled_error": text(errors[2]*mp.sqrt(t0)*(w+1)/delta**3),
            "relative_density_residual": text(abs(bose.critical_density(
                solution, delta, abs_tol=mp.mpf("1e-45"))/rho-1)),
        })

    report = {
        "precision_digits": mp.dps,
        "rounding_certified": False,
        "limitation": "Bounds control analytic truncation. Ordinary mpmath rounding is not enclosed. Tiny Hurwitz-zeta values are evaluated with additional precision before gamma rescaling. Independent quadrature evidence is in independent_validation.json.",
        "comparisons": comparisons,
        "inversions": inversions,
        "all_truncation_intervals_overlap": all(r["truncation_intervals_overlap"] for r in comparisons),
        "evaluation_count_complexity": {
            "unaccelerated_positive_series_fixed_s": "Theta(epsilon^-4) terms for absolute error epsilon",
            "convergent_series_fixed_0_s_R": "O(log(1/epsilon)) terms",
            "accelerated_tail_fixed_s": "O((1+s^-2) log(1/epsilon)) special-function evaluations",
            "combined_method_uniform_s_positive": "O(log(1/epsilon)) special-function evaluations, with crossover at s=sqrt(8*pi)/2",
            "model": "Counts special-function evaluations; does not assert a bit-operation bound for those evaluations.",
        },
        "elapsed_seconds": round(time.perf_counter()-began, 3),
    }
    target = Path(__file__).resolve().parents[1]/"data"/"algorithm_validation.json"
    target.write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    print(target)
    print(f"All {len(comparisons)} numerical comparisons passed; {len(inversions)} inverse cases recorded.")


if __name__ == "__main__":
    main()
