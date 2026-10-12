#!/usr/bin/env python3
"""Numerical diagnostics for Section 8's Gamma integral basis.

Requirements: Python 3.10+ and mpmath.
Run from any directory: python /path/to/verify_gamma_integrals.py

The script uses 45-digit Gamma quadrature for m=1,2,3 and n=1,...,m+3.
It checks the exact top-derivative identities and every recurrence row
available in that range. Bernoulli recurrence coefficients are generated
independently as exact fractions before conversion to mpmath numbers.
All entries and residuals are written beside this script to
gamma_integral_results.json. These are floating-point diagnostics, not
interval certificates or substitutes for the article's proofs.
"""

from __future__ import annotations

from fractions import Fraction
from math import comb, factorial
from pathlib import Path
import json
import platform

import mpmath as mp


DPS = 45
ABSOLUTE_TOLERANCE = "1e-35"
OUTPUT = Path(__file__).with_name("gamma_integral_results.json")


def exact_bernoulli_numbers(stop: int) -> list[Fraction]:
    """B_0,...,B_stop with the convention B_1=-1/2."""
    values = [Fraction(1)]
    for n in range(1, stop + 1):
        values.append(
            -sum(comb(n + 1, k) * values[k] for k in range(n)) / (n + 1)
        )
    return values


def to_mp(value: Fraction) -> mp.mpf:
    return mp.mpf(value.numerator) / value.denominator


def decimal(value: mp.mpf) -> str:
    return mp.nstr(value, DPS)


def check_residual(value: mp.mpf, tolerance: mp.mpf, description: str) -> None:
    if not mp.isfinite(value) or abs(value) > tolerance:
        raise AssertionError(
            f"{description}: residual {decimal(value)} exceeds "
            f"the absolute tolerance {decimal(tolerance)}"
        )


def verify() -> dict:
    mp.mp.dps = DPS
    tolerance = mp.mpf(ABSOLUTE_TOLERANCE)
    bernoulli = exact_bernoulli_numbers(10)
    beta = {
        k: 2 * abs(bernoulli[2 * k]) / factorial(2 * k)
        for k in range(1, 6)
    }
    top_max = mp.mpf(0)
    coefficient_top_max = mp.mpf(0)
    recurrence_max = mp.mpf(0)
    operator_max = mp.mpf(0)
    assertion_count = 0
    cases = []

    for m in (1, 2, 3):
        print(f"Gamma quadrature: m={m}, n=1,...,{m + 3}", flush=True)

        def weight(x: mp.mpf) -> mp.mpf:
            return abs(mp.gamma(mp.mpf(1) / 4 + mp.j * x / 2)) ** (4 * m)

        multipliers = [
            (f"sinh({k}*pi*x)", lambda x, k=k: mp.sinh(mp.pi * k * x))
            for k in range(m - 1, 0, -1)
        ] + [("tanh(pi*x)", lambda x: mp.tanh(mp.pi * x))]
        coefficients = []
        for n in range(1, m + 4):
            row = []
            for _, multiplier in multipliers:
                integral = mp.quad(
                    lambda x: (
                        mp.im((x + mp.j / 2) ** (2 * n))
                        * multiplier(x)
                        * weight(x)
                    ),
                    [0, mp.mpf("0.5"), 1, 2, 4, 8, mp.inf],
                )
                row.append(4 * integral / factorial(2 * n))
            coefficients.append(row)

        top_checks = []
        for j in range(1, m + 1):
            expected = (
                (-1) ** (m + 1) * 2 ** (2 * m + 2) * mp.pi**m
                if j == m
                else mp.mpf(0)
            )
            actual = factorial(2 * m) * coefficients[m - 1][j - 1]
            residual = actual - expected
            coefficient_residual = (
                coefficients[m - 1][j - 1] - expected / factorial(2 * m)
            )
            check_residual(residual, tolerance, f"top derivative m={m}, j={j}")
            assertion_count += 1
            top_max = max(top_max, abs(residual))
            coefficient_top_max = max(coefficient_top_max, abs(coefficient_residual))
            top_checks.append(
                {
                    "j": j,
                    "multiplier": multipliers[j - 1][0],
                    "actual_derivative": decimal(actual),
                    "expected_derivative": decimal(expected),
                    "derivative_residual": decimal(residual),
                    "absolute_derivative_residual": decimal(abs(residual)),
                    "coefficient_residual": decimal(coefficient_residual),
                }
            )

        def aa(r: int) -> int:
            return factorial(2 * r) // factorial(2 * r - 2 * m) if r > m else 0

        def bb(n: int) -> int:
            return factorial(2 * n - 1) // factorial(2 * n - 2 * m - 1)

        recurrence_checks = []
        for n in range(m + 1, m + 4):
            d_n = 2 * (aa(n) + bb(n))
            for j in range(1, m + 1):
                weighted_sum = mp.fsum(
                    to_mp(beta[n - r])
                    * (aa(r) + bb(n))
                    * coefficients[r - 1][j - 1]
                    for r in range(1, n)
                )
                rhs = weighted_sum / d_n
                residual = coefficients[n - 1][j - 1] - rhs
                operator_residual = d_n * coefficients[n - 1][j - 1] - weighted_sum
                check_residual(residual, tolerance, f"recurrence m={m}, n={n}, j={j}")
                assertion_count += 1
                recurrence_max = max(recurrence_max, abs(residual))
                operator_max = max(operator_max, abs(operator_residual))
                recurrence_checks.append(
                    {
                        "n": n,
                        "j": j,
                        "d_n": d_n,
                        "actual_coefficient": decimal(coefficients[n - 1][j - 1]),
                        "recurrence_coefficient": decimal(rhs),
                        "coefficient_residual": decimal(residual),
                        "absolute_coefficient_residual": decimal(abs(residual)),
                        "unnormalized_operator_residual": decimal(operator_residual),
                    }
                )

        initial = mp.matrix(coefficients[:m])
        initial_determinant = mp.det(initial)
        expected_sign = (-1) ** (m * (m - 1) // 2)
        if not expected_sign * initial_determinant > 0:
            raise AssertionError(f"initial determinant has wrong sign at m={m}")
        assertion_count += 1
        cases.append(
            {
                "m": m,
                "mode_order": [label for label, _ in multipliers],
                "n_range": [1, m + 3],
                "initial_matrix": [
                    [decimal(value) for value in row] for row in coefficients[:m]
                ],
                "initial_determinant": decimal(initial_determinant),
                "positive_K_m": decimal(expected_sign * initial_determinant),
                "all_coefficients": [
                    {"n": n, "values": [decimal(value) for value in row]}
                    for n, row in enumerate(coefficients, start=1)
                ],
                "top_derivative_checks": top_checks,
                "recurrence_checks": recurrence_checks,
            }
        )

    return {
        "status": "passed",
        "arithmetic_status": "floating-point numerical diagnostics; not interval certificates",
        "python_version": platform.python_version(),
        "mpmath_version": mp.__version__,
        "decimal_precision": DPS,
        "absolute_assertion_tolerance": ABSOLUTE_TOLERANCE,
        "quadrature_breakpoints": ["0", "0.5", "1", "2", "4", "8", "infinity"],
        "assertion_count": assertion_count,
        "top_derivative_identity_count": sum(len(case["top_derivative_checks"]) for case in cases),
        "recurrence_identity_count": sum(len(case["recurrence_checks"]) for case in cases),
        "max_absolute_top_derivative_residual": decimal(top_max),
        "max_absolute_top_coefficient_residual": decimal(coefficient_top_max),
        "max_absolute_recurrence_coefficient_residual": decimal(recurrence_max),
        "max_absolute_unnormalized_operator_residual": decimal(operator_max),
        "cases": cases,
    }


def main() -> None:
    result = verify()
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    summary = {key: value for key, value in result.items() if key != "cases"}
    summary["output_file"] = OUTPUT.name
    print(json.dumps(summary, indent=2), flush=True)


if __name__ == "__main__":
    main()
