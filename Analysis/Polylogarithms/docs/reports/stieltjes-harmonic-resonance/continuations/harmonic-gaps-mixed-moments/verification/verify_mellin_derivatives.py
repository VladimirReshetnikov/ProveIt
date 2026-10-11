#!/usr/bin/env python3
"""Numerically check the all-r normalized Mellin derivative formula.

This is a reproducible numerical diagnostic, not an interval certificate or
a substitute for the proof in sections/03_transverse.tex (label tr:Mjet).
Only Python's standard library and mpmath are required.

For f(y) = exp(-c*y) * (p0 + p1*y + p2*y**2), Re(c) > 0, its normalized
Mellin transform has the exact entire expression

    M(u) = c**(-u) * (p0 + p1*u/c + p2*u*(u+1)/c**2).

For m >= 0 and r >= 1, the article asserts

    M^(r)(-m) = (-1)**m * r! * sum_{j=1}^r c_j/(r-j)! * I_(r-j),
    I_q = integral_0^infinity log(y)**q/y * (g(y)-g(0)*exp(-y)) dy,
    g = f^(m),   c_j = [v**j] rgamma(v).

The left side is differentiated directly with mp.diff. The right side uses
analytically formed derivative polynomials and numerical quadrature. The
subtracted integrand is evaluated with expm1 near zero. On (0,1), y=exp(-t)
removes the logarithmic endpoint singularity before quadrature. Complex
powers use the principal logarithm of c, which is unambiguous for Re(c)>0.

Usage:
    python verification/verify_mellin_derivatives.py
    python verification/verify_mellin_derivatives.py --output /path/check.json
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import mpmath as mp


DPS = 80
M_VALUES = (0, 1, 3)
R_VALUES = (1, 2, 3, 4)
ABSOLUTE_TOLERANCE = "1e-50"


def serialize_number(value):
    """Retain working precision without converting through binary floats."""
    return {
        "real": mp.nstr(mp.re(value), DPS),
        "imag": mp.nstr(mp.im(value), DPS),
    }


def derivative_polynomial(c, coefficients, m):
    """Return coefficients of (D-c)^m P, in ascending degree order."""
    degree = len(coefficients) - 1
    return [
        mp.fsum(
            mp.binomial(m, j)
            * (-c) ** (m - j)
            * mp.factorial(k + j)
            / mp.factorial(k)
            * coefficients[k + j]
            for j in range(min(m, degree - k) + 1)
        )
        for k in range(degree + 1)
    ]


def subtracted_derivative(y, c, polynomial):
    """Compute f^(m)(y)-f^(m)(0)*exp(-y), stably at small y."""
    q0, q1, q2 = polynomial
    if y <= 1:
        return mp.exp(-c * y) * (
            -q0 * mp.expm1((c - 1) * y) + y * (q1 + q2 * y)
        )
    return mp.exp(-c * y) * (q0 + y * (q1 + q2 * y)) - q0 * mp.exp(-y)


def logarithmic_integral(q, c, polynomial):
    """Evaluate I_q as two absolutely convergent ordinary integrals."""

    def below_one(t):
        if mp.isinf(t):
            return mp.mpf(0)
        return (-t) ** q * subtracted_derivative(mp.exp(-t), c, polynomial)

    def above_one(y):
        if mp.isinf(y):
            return mp.mpf(0)
        return mp.log(y) ** q * subtracted_derivative(y, c, polynomial) / y

    # The first term is the exact substitution y=exp(-t) on 0<y<1.
    return mp.quad(below_one, [0, 1, 4, 12, mp.inf]) + mp.quad(
        above_one, [1, 2, 5, 15, mp.inf]
    )


def run_checks():
    mp.mp.dps = DPS
    tolerance = mp.mpf(ABSOLUTE_TOLERANCE)
    rgamma_coefficients = mp.taylor(mp.rgamma, mp.mpf(0), max(R_VALUES))
    cases = (
        {
            "name": "real_decay_real_polynomial",
            "c": mp.mpf("0.7"),
            "p": (mp.mpf("1.1"), mp.mpf("-0.4"), mp.mpf("0.3")),
        },
        {
            "name": "complex_decay_complex_polynomial",
            "c": mp.mpc("1.6", "0.4"),
            "p": (
                mp.mpc("0.9", "-0.2"),
                mp.mpc("-0.7", "0.35"),
                mp.mpc("0.45", "0.15"),
            ),
        },
    )

    tests = []
    moment_data = []
    residuals = []
    for case in cases:
        c = case["c"]
        p0, p1, p2 = case["p"]

        def exact_mellin(u):
            return mp.exp(-u * mp.log(c)) * (
                p0 + p1 * u / c + p2 * u * (u + 1) / c**2
            )

        for m in M_VALUES:
            polynomial = derivative_polynomial(c, case["p"], m)
            moments = [
                logarithmic_integral(q, c, polynomial)
                for q in range(max(R_VALUES))
            ]
            moment_data.append(
                {
                    "case": case["name"],
                    "m": m,
                    "derivative_polynomial_ascending": [
                        serialize_number(z) for z in polynomial
                    ],
                    "logarithmic_integrals_q_0_through_3": [
                        serialize_number(z) for z in moments
                    ],
                }
            )
            for r in R_VALUES:
                exact = mp.diff(exact_mellin, -m, r)
                from_formula = (-1) ** m * mp.factorial(r) * mp.fsum(
                    rgamma_coefficients[j]
                    / mp.factorial(r - j)
                    * moments[r - j]
                    for j in range(1, r + 1)
                )
                residual = from_formula - exact
                absolute_residual = abs(residual)
                passed = bool(mp.isfinite(absolute_residual) and absolute_residual < tolerance)
                residuals.append(absolute_residual)
                tests.append(
                    {
                        "case": case["name"],
                        "m": m,
                        "r": r,
                        "exact_mellin_derivative": serialize_number(exact),
                        "integral_formula": serialize_number(from_formula),
                        "residual_formula_minus_exact": serialize_number(residual),
                        "absolute_residual": mp.nstr(absolute_residual, DPS),
                        "passed": passed,
                    }
                )

    expected_count = len(cases) * len(M_VALUES) * len(R_VALUES)
    assert len(tests) == expected_count == 24
    report = {
        "schema_version": 1,
        "script": "verification/verify_mellin_derivatives.py",
        "article_source": "sections/03_transverse.tex, formula tr:Mjet",
        "description": "Higher derivative normalization of the normalized Mellin transform.",
        "precision_decimal_digits": DPS,
        "mpmath_version": mp.__version__,
        "absolute_tolerance": ABSOLUTE_TOLERANCE,
        "numerical_diagnostic_only": True,
        "interval_certificate": False,
        "quadrature": {
            "method": "mpmath.quad (default tanh-sinh)",
            "near_zero_subtraction": "expm1((c-1)*y)",
            "below_one_substitution": "y=exp(-t)",
            "below_one_t_breakpoints": ["0", "1", "4", "12", "infinity"],
            "above_one_y_breakpoints": ["1", "2", "5", "15", "infinity"],
        },
        "m_values": list(M_VALUES),
        "r_values": list(R_VALUES),
        "cases": [
            {
                "name": case["name"],
                "c": serialize_number(case["c"]),
                "polynomial_coefficients_ascending": [
                    serialize_number(z) for z in case["p"]
                ],
            }
            for case in cases
        ],
        "rgamma_coefficients_c_1_through_4": [
            serialize_number(z) for z in rgamma_coefficients[1:]
        ],
        "moment_data": moment_data,
        "number_of_tests": len(tests),
        "number_passed": sum(test["passed"] for test in tests),
        "maximum_absolute_residual": mp.nstr(max(residuals), DPS),
        "status": "passed" if all(test["passed"] for test in tests) else "failed",
        "tests": tests,
    }
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(__file__).resolve().parents[1] / "results" / "mellin_derivatives.json",
        help="JSON report path (default: package results/mellin_derivatives.json)",
    )
    args = parser.parse_args()
    report = run_checks()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(
        f"{report['number_passed']}/{report['number_of_tests']} checks passed at {DPS} dps; "
        f"maximum absolute residual {report['maximum_absolute_residual']}"
    )
    print(f"Numerical diagnostic only; JSON written to {args.output}")
    assert report["status"] == "passed", (
        f"Mellin derivative normalization check failed; inspect {args.output}"
    )


if __name__ == "__main__":
    main()
