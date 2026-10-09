#!/usr/bin/env python3
"""Independent quadrature checks for the marginal Bose crossover series.

The reference calculation integrates Li_{3/4}(exp(-x^4-lambda*x^2))
after x=t^2. It does not call the article's crossover implementation.

This script produces numerical evidence, not interval-certified values.
The recorded analytic truncation bounds are rigorous in exact arithmetic;
quadrature and floating-point rounding are assessed by precision comparison.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import time

import mpmath as mp


def reference_integral(lam: mp.mpf, dps: int) -> mp.mpf:
    """G(lambda)=4 integral_0^infty t Li_{3/4}(e^-t^8-lambda*t^4) dt."""
    with mp.workdps(dps):
        lam = +lam
        gamma = mp.gamma(mp.mpf(1) / 4)
        zeta0 = mp.zeta(mp.mpf(3) / 4)
        zeta1 = mp.zeta(-mp.mpf(1) / 4)
        zeta2 = mp.zeta(-mp.mpf(5) / 4)
        tiny = mp.power(10, -dps // 2)

        def integrand(t):
            energy = t**8 + lam * t**4
            if energy < tiny:
                # Standard local polylog expansion prevents exp(-energy)
                # from rounding to one. Its omitted term is O(t*energy^3).
                regular = zeta0 - energy * zeta1 + energy**2 * zeta2 / 2
                singular = 4 * gamma / mp.root(t**4 + lam, 4)
                return singular + 4 * t * regular
            return 4 * t * mp.polylog(mp.mpf(3) / 4, mp.exp(-energy))

        scale = mp.root(lam, 4)
        interior = [mp.mpf("0.2"), mp.mpf("0.5"), mp.mpf(1), mp.mpf(2)]
        interior.extend(x for x in [scale / 4, scale, 4 * scale] if 0 < x < 2)
        points = [mp.mpf(0)] + sorted(set(interior)) + [mp.inf]
        return +mp.quad(integrand, points)


def normalized_coefficient(m: int) -> mp.mpf:
    """Return c_m R^m using positive zeta arguments, m >= 3."""
    if m < 3:
        raise ValueError("Use the elementary formulas for m=1,2")
    halfsqrt2 = mp.sqrt(2) / 2
    cos_values = [1, halfsqrt2, 0, -halfsqrt2, -1, -halfsqrt2, 0, halfsqrt2]
    cosine = cos_values[m % 8]
    if not cosine:
        return mp.mpf(0)
    x = mp.mpf(m) / 2
    return (
        2 * mp.sqrt(mp.pi) / m
        * (-1) ** m * cosine
        * mp.gamma(x + mp.mpf(1) / 4) / mp.gamma(x + mp.mpf(1) / 2)
        * mp.zeta(x)
    )


def correction_series(lam: mp.mpf, degree: int) -> mp.mpf:
    gamma = mp.gamma(mp.mpf(1) / 4)
    value = gamma * (mp.log(1 / lam) + mp.pi / 4 + mp.mpf(3) / 2 * mp.log(2))
    if degree >= 1:
        value -= mp.gamma(mp.mpf(3) / 4) * mp.zeta(mp.mpf(1) / 2) * lam / 2
    if degree >= 2:
        value -= gamma * lam**2 / 32
    r = lam / mp.sqrt(8 * mp.pi)
    rpower = r**2
    for m in range(3, degree + 1):
        rpower *= r
        value += normalized_coefficient(m) * rpower
    return value


def analytic_tail_bound(lam: mp.mpf, degree: int) -> mp.mpf:
    if degree < 2:
        raise ValueError("The geometric tail bound requires degree >= 2")
    r = lam / mp.sqrt(8 * mp.pi)
    if not 0 < r < 1:
        raise ValueError("Use the contour bound at the boundary")
    constant = 2 * mp.sqrt(2 * mp.pi) * mp.zeta(mp.mpf(3) / 2)
    return constant * (degree + 1) ** (-mp.mpf(5) / 4) * r ** (degree + 1) / (1 - r)


def contour_tail_bound(lam: mp.mpf, j: int) -> mp.mpf:
    r = lam / mp.sqrt(8 * mp.pi)
    return (
        mp.sqrt(mp.pi) * mp.zeta(2 * j + 1)
        / ((4 * j + 2) * (2 * j + mp.mpf(1) / 4) ** (mp.mpf(1) / 4))
        * r ** (4 * j + 2)
    )


def textnum(value: mp.mpf, digits: int = 38) -> str:
    return mp.nstr(value, digits)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dps", type=int, default=40)
    parser.add_argument("--reference-dps", type=int, default=55)
    parser.add_argument("--target-digits", type=int, default=28)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data" / "independent_validation.json")
    args = parser.parse_args()
    mp.mp.dps = max(args.reference_dps + 10, args.dps + 10)
    began = time.perf_counter()
    rows = []
    for literal in ["1e-6", "1e-3", "0.1", "1", "3", "4.9", "boundary"]:
        started = time.perf_counter()
        lam = mp.sqrt(8 * mp.pi) if literal == "boundary" else mp.mpf(literal)
        low = reference_integral(lam, args.dps)
        high = reference_integral(lam, args.reference_dps)
        if literal == "boundary":
            j = 1023
            degree = 4 * j + 1
            bound = contour_tail_bound(lam, j)
            bound_kind = "explicit Mellin contour remainder"
        else:
            degree = 2
            target = mp.power(10, -args.target_digits)
            while analytic_tail_bound(lam, degree) > target:
                degree += 1
            bound = analytic_tail_bound(lam, degree)
            bound_kind = "absolute geometric coefficient tail"
        estimate = correction_series(lam, degree)
        difference = abs(estimate - high)
        precision_difference = abs(high - low)
        gamma = mp.gamma(mp.mpf(1) / 4)
        theta = lam**2 / 8
        extracted_constant = 2 * high / gamma - mp.log(1 / theta)
        row = {
            "lambda": textnum(lam),
            "lambda_input": literal,
            "reference_quadrature": textnum(high),
            "lower_precision_quadrature": textnum(low),
            "quadrature_precision_difference": textnum(precision_difference, 12),
            "series_degree": degree,
            "series_value": textnum(estimate),
            "absolute_difference": textnum(difference, 12),
            "analytic_truncation_bound": textnum(bound, 12),
            "bound_kind": bound_kind,
            "difference_within_analytic_bound": bool(difference <= bound),
            "normalized_log_constant_plus_corrections": textnum(extracted_constant),
            "expected_limit_pi_over_two": textnum(mp.pi / 2),
            "elapsed_seconds": round(time.perf_counter() - started, 3),
        }
        if precision_difference > bound:
            # The smallest lambda needs very few series coefficients, so its
            # analytic tail can be below the first precision-comparison gap.
            # Resolve that concrete numerical risk with one additional run.
            extra_started = time.perf_counter()
            extra_dps = args.reference_dps + 15
            extra = reference_integral(lam, extra_dps)
            row["additional_reference_dps"] = extra_dps
            row["additional_reference"] = textnum(extra, extra_dps - 5)
            row["difference_from_stored_reference"] = textnum(
                abs(extra - mp.mpf(row["reference_quadrature"])), 16)
            row["series_difference_to_additional_reference"] = textnum(
                abs(extra - estimate), 16)
            row["additional_precision_check_seconds"] = round(
                time.perf_counter() - extra_started, 3)
            row["difference_within_analytic_bound"] = bool(abs(extra - estimate) <= bound)
        rows.append(row)
        print(literal, "G=", textnum(high, 24), "degree=", degree,
              "difference=", textnum(difference, 6), "bound=", textnum(bound, 6), flush=True)

    output = {
        "purpose": "Independent numerical validation of the exact marginal crossover expansion",
        "reference_identity": "G(lambda) = 4 integral_0^infinity t Li_(3/4)(exp(-t^8-lambda*t^4)) dt",
        "reference_quadrature_dps": args.reference_dps,
        "comparison_quadrature_dps": args.dps,
        "target_absolute_truncation_digits": args.target_digits,
        "interval_certified": False,
        "limitation": "Quadrature and floating-point errors are numerical estimates. The analytic truncation bounds are proved in the article but evaluated here with ordinary mpmath rounding.",
        "all_differences_within_analytic_bound": all(r["difference_within_analytic_bound"] for r in rows),
        "elapsed_seconds": round(time.perf_counter() - began, 3),
        "rows": rows,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")
    print("Wrote", args.output, flush=True)
    if not output["all_differences_within_analytic_bound"]:
        raise SystemExit("A numerical difference exceeded its analytic truncation bound")


if __name__ == "__main__":
    main()
