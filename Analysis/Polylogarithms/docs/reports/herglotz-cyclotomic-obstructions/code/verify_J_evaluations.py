#!/usr/bin/env python3
"""Independently check explicit J evaluations by its defining real integral.

Requires mpmath. The reference is integral_0^1 log(1+t^x)/(1+t) dt;
no Herglotz F evaluation or finite dilogarithm formula is used on that side.
These are high-precision floating-point checks, not interval certificates.

Run from the package root:
    python code/verify_J_evaluations.py
    python code/verify_J_evaluations.py --digits 80 --max-even-m 40

The default data path is relative to this script, so the working directory
does not affect where the standard output file is written.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
import time

import mpmath as mp


def log_sine_square_sum(n: int):
    if n < 1:
        raise ValueError("n must be positive")
    return mp.fsum(mp.log(2*mp.sin(mp.pi*k/n))**2 for k in range(1, n))


def direct_integral(p: int, q: int):
    x = mp.mpf(p)/q
    return mp.quad(lambda t: mp.log1p(t**x)/(1+t),
                   [0, mp.mpf("0.01"), mp.mpf("0.25"), 1])


def exceptional_cases():
    l2, l3, l5 = mp.log(2), mp.log(3), mp.log(5)
    golden = (1+mp.sqrt(5))/2
    return [
        ("J(1)", 1, 1, l2*l2/2,
         "log(2)^2/2"),
        ("J(2/3)", 2, 3, -mp.pi**2/144+3*l2*l2/4,
         "-pi^2/144+3*log(2)^2/4"),
        ("J(2/5)", 2, 5, 11*mp.pi**2/240+3*l2*l2/4-2*mp.log(golden)**2,
         "11*pi^2/240+3*log(2)^2/4-2*log(phi)^2"),
        ("J(1/3)", 1, 3, mp.pi**2/9+l2*l2/2-l3*l3/2-mp.polylog(2, mp.mpf(1)/3),
         "pi^2/9+log(2)^2/2-log(3)^2/2-Li_2(1/3)"),
        ("J(1/5)", 1, 5,
         7*mp.pi**2/60+l2*l2/2-l5*l5/4-mp.log(golden)**2-mp.polylog(2, mp.mpf(1)/5)/2,
         "7*pi^2/60+log(2)^2/2-log(5)^2/4-log(phi)^2-Li_2(1/5)/2"),
    ]


def verify(digits: int = 80, max_even_m: int = 40) -> dict:
    if digits < 30:
        raise ValueError("Use at least 30 decimal digits")
    if max_even_m < 2 or max_even_m % 2:
        raise ValueError("max_even_m must be a positive even integer at least 2")
    mp.mp.dps = digits
    cases = [(name, p, q, value, formula, "exceptional")
             for name, p, q, value, formula in exceptional_cases()]
    for m in range(2, max_even_m+1, 2):
        value = (mp.pi**2*(m*m-2)/(48*m)+log_sine_square_sum(m)
                 -log_sine_square_sum(m//2)/2-log_sine_square_sum(2*m)/2)
        cases.append((f"J(1/{m})", 1, m, value,
                      "pi^2*(m^2-2)/(48*m)+S(m)-S(m/2)/2-S(2*m)/2",
                      "even_reciprocal_family"))
    tolerance = mp.power(10, -(digits-8))
    rows, residuals = [], []
    for name, p, q, value, formula, family in cases:
        reference = direct_integral(p, q)
        residual = abs(reference-value)
        assert residual < tolerance, (name, mp.nstr(residual), mp.nstr(tolerance))
        residuals.append(residual)
        rows.append({"name": name, "numerator": p, "denominator": q,
                     "family": family, "formula": formula,
                     "direct_integral_value": mp.nstr(reference, digits),
                     "closed_form_value": mp.nstr(value, digits),
                     "absolute_residual": mp.nstr(residual, 20),
                     "passed": True})
    return {
        "method": "mpmath high-precision direct real quadrature compared with explicit closed forms",
        "reference_integral": "integral from 0 to 1 of log(1+t^x)/(1+t) dt",
        "quadrature_subdivision": ["0", "0.01", "0.25", "1"],
        "reference_does_not_use": ["Herglotz F values", "RZ finite dilogarithm sum"],
        "arithmetic_scope": "Floating-point numerical checks, not rigorous interval certificates; "
                            "the mathematical identities are proved in the article.",
        "working_precision_digits": digits,
        "software": {"Python": sys.version.split()[0], "mpmath": mp.__version__},
        "case_count": len(rows), "exceptional_case_count": 5,
        "even_reciprocal_m_range": [2, max_even_m],
        "even_reciprocal_m_step": 2,
        "absolute_residual_test_threshold": mp.nstr(tolerance, 10),
        "maximum_absolute_residual": mp.nstr(max(residuals), 20),
        "cases": rows,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--digits", type=int, default=80,
                        help="Working decimal precision (default: 80; minimum: 30)")
    parser.add_argument("--max-even-m", type=int, default=40,
                        help="Largest even denominator in J(1/m) family (default: 40)")
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1]/"data"/"J_evaluation_checks.json")
    args = parser.parse_args()
    started = time.monotonic()
    try:
        results = verify(args.digits, args.max_even_m)
    except ValueError as error:
        parser.error(str(error))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(results, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"status": "passed", "case_count": results["case_count"],
                      "working_precision_digits": results["working_precision_digits"],
                      "maximum_absolute_residual": results["maximum_absolute_residual"],
                      "output": str(args.output),
                      "elapsed_seconds": round(time.monotonic()-started, 3)}, indent=2))
