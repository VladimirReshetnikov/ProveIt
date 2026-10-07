#!/usr/bin/env python3
"""Supplemental checks for the inverse logarithmic repair-cost formulas.

Requirements: Python 3.10+ and mpmath.  SymPy is optional and enables exact
symbolic verification of B_1,...,B_4 by formal substitution, independently
of the Lagrange coefficient formula used by the numerical checks.

    python -m pip install mpmath
    python -m pip install sympy       # optional exact symbolic checks
    python code/verify_inversion.py > inversion_results.json
    python code/verify_inversion.py --require-symbolic --dps 120

The receipt contains no timestamps, timings, random draws, or machine paths.
Its floating-point values are serialized as decimal strings.  Fixed inputs,
options, and dependency versions give deterministic output.  Numerical
checks at finitely many X do not prove a remainder bound for every X; the
article supplies the analytic convergence and remainder proofs.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import json
import sys

try:
    import mpmath as mp
except ImportError as exc:
    raise SystemExit("mpmath is required: python -m pip install mpmath") from exc


HEIGHTS = (16, 64, 128, 512)
X_VALUES = (64, 100, 1000)
TRUNCATIONS = (0, 1, 2, 4, 8, 12)
DISPLAY_DIGITS = 50


def decimal(value: mp.mpf) -> str:
    """Avoid conversion through binary double precision in the JSON receipt."""
    return mp.nstr(value, n=DISPLAY_DIGITS, strip_zeros=False)


def scaled_error(actual: mp.mpf, expected: mp.mpf) -> mp.mpf:
    """Relative error, with the zero case defined without a zero divisor."""
    if expected == 0:
        return abs(actual)
    return abs((actual - expected) / expected)


def exact_parameter_checks() -> dict:
    """Exact rational checks only; no floating-point operations occur here."""
    records = []
    for h in HEIGHTS:
        m = 1 << h
        d = 20 * h + 2
        n = d * m
        tau = Fraction(m, n * n)
        epsilon = Fraction(m * m, n * n)
        passed = tau == Fraction(1, d * d * m) and epsilon == Fraction(1, d * d)
        records.append({
            "h": h,
            "d": d,
            "tau_exact": str(tau),
            "epsilon_exact": str(epsilon),
            "passed": passed,
        })
    return {
        "arithmetic": "Python integers and fractions.Fraction",
        "scope": "Exact identities for the given combinatorial parameters",
        "passed": all(row["passed"] for row in records),
        "cases": records,
    }


def symbolic_checks() -> dict:
    """Solve the formal fixed-point equation coefficient by coefficient."""
    try:
        import sympy as sp
    except ImportError:
        return {
            "status": "skipped",
            "reason": "Optional dependency sympy is unavailable",
            "passed": None,
        }

    z, t = sp.symbols("z t")
    v = sp.Integer(0)
    coefficients = []
    for order in range(1, 5):
        unknown = sp.Symbol(f"v{order}")
        trial = v + unknown * z**order
        residual = sp.series(
            trial + 2 * z * (t + sp.log(1 + trial)), z, 0, order + 1
        ).removeO().expand()
        equation = residual.coeff(z, order)
        # The unknown enters linearly with coefficient one.  Retain this
        # check so a change of equation cannot silently invalidate solving.
        if sp.diff(equation, unknown) != 1:
            return {"status": "failed", "passed": False,
                    "reason": "Unexpected formal coefficient equation"}
        solved = sp.expand(-equation.subs(unknown, 0))
        v = sp.expand(v + solved * z**order)
        coefficients.append(sp.sstr(solved))

    residual = sp.series(v + 2 * z * (t + sp.log(1 + v)), z, 0, 5).removeO()
    fixed_point_passed = sp.expand(residual) == 0
    repair_series = sp.series((1 + v)**-2, z, 0, 5).removeO().expand()
    expected = (
        4 * t,
        12 * t**2 - 8 * t,
        32 * t**3 - 56 * t**2 + 16 * t,
        80 * t**4 - sp.Rational(752, 3) * t**3 + 192 * t**2 - 32 * t,
    )
    cases = []
    for order, target in enumerate(expected, 1):
        derived = repair_series.coeff(z, order).expand()
        cases.append({
            "order": order,
            "derived_polynomial": sp.sstr(derived),
            "expected_polynomial": sp.sstr(target),
            "passed": sp.expand(derived - target) == 0,
        })
    passed = fixed_point_passed and all(row["passed"] for row in cases)
    return {
        "status": "passed" if passed else "failed",
        "sympy_version": sp.__version__,
        "arithmetic": "Exact rational polynomial arithmetic",
        "method": "Solve v+2z(t+log(1+v))=0, then expand (1+v)^(-2)",
        "formal_v_coefficients": coefficients,
        "fixed_point_residual_through_degree_4_is_zero": fixed_point_passed,
        "passed": passed,
        "cases": cases,
    }


def convolution(left: list, right: list, degree: int) -> list:
    return [mp.fsum(left[j] * right[k - j] for j in range(k + 1))
            for k in range(degree + 1)]


def lagrange_coefficient(order: int, t: mp.mpf) -> mp.mpf:
    """Finite coefficient arithmetic, avoiding numerical differentiation.

    B_n(t)=(-2)^(n+1)/n * [w^(n-1)]
                         (t+log(1+w))^n (1+w)^(-3).
    """
    degree = order - 1
    log_series = [t] + [mp.mpf((-1)**(k + 1)) / k
                        for k in range(1, degree + 1)]
    power = [mp.mpf(1)] + [mp.mpf(0)] * degree
    for _ in range(order):
        power = convolution(power, log_series, degree)
    inverse_cube = [mp.mpf((-1)**k * (k + 1) * (k + 2)) / 2
                    for k in range(degree + 1)]
    coefficient = mp.fsum(power[k] * inverse_cube[degree - k]
                          for k in range(degree + 1))
    return mp.mpf((-2)**(order + 1)) * coefficient / order


def numerical_relation_checks(a: mp.mpf, tolerance: mp.mpf) -> dict:
    records = []
    for h in HEIGHTS:
        d = mp.mpf(20 * h + 2)
        m = mp.mpf(1 << h)
        tau = 1 / (d**2 * m)
        epsilon = 1 / d**2
        tau_from_epsilon = mp.exp(2 * a) * epsilon * mp.exp(-a / mp.sqrt(epsilon))
        argument = (a / 2) * mp.exp(a) / mp.sqrt(tau)
        w = mp.lambertw(argument, 0)
        epsilon_from_w = a**2 / (4 * w**2)
        x = mp.log(1 / tau) + 2 * mp.log(a) + 2 * a
        u = a * d
        errors = {
            "tau_formula_relative_error": scaled_error(tau_from_epsilon, tau),
            "epsilon_from_W_relative_error": scaled_error(epsilon_from_w, epsilon),
            "W_defining_equation_relative_error": scaled_error(w * mp.exp(w), argument),
            "u_plus_2logu_scaled_residual": abs(u + 2 * mp.log(u) - x) / (1 + abs(x)),
        }
        records.append({
            "h": h,
            "X": decimal(x),
            "tau": decimal(tau),
            "epsilon": decimal(epsilon),
            "errors": {key: decimal(value) for key, value in errors.items()},
            "passed": all(value <= tolerance for value in errors.values()),
        })
    return {"passed": all(row["passed"] for row in records), "cases": records}


def numerical_expansion_checks(a: mp.mpf, tolerance: mp.mpf) -> dict:
    records = []
    for x_value in X_VALUES:
        x = mp.mpf(x_value)
        t = mp.log(x)
        # This root solve is independent of the Lagrange polynomial arithmetic.
        u = mp.findroot(lambda y: y + 2 * mp.log(y) - x,
                        (x - 2 * t, x), tol=mp.eps * 32, maxsteps=100)
        u_from_w = 2 * mp.lambertw(mp.exp(x / 2) / 2, 0)
        root_error = scaled_error(u, u_from_w)
        residual = abs(u + 2 * mp.log(u) - x) / (1 + x)
        epsilon = a**2 / u**2
        ratio = 8 * (t + 1) / x
        prefactor = a**2 / x**2
        coefficients = [mp.mpf(1)] + [lagrange_coefficient(j, t)
                                      for j in range(1, max(TRUNCATIONS) + 1)]
        closed = (
            4 * t,
            12 * t**2 - 8 * t,
            32 * t**3 - 56 * t**2 + 16 * t,
            80 * t**4 - mp.mpf(752) / 3 * t**3 + 192 * t**2 - 32 * t,
        )
        coefficient_errors = [scaled_error(coefficients[j], closed[j - 1])
                              for j in range(1, 5)]
        truncations = []
        for degree in TRUNCATIONS:
            approximation = prefactor * mp.fsum(coefficients[j] / x**j
                                                for j in range(degree + 1))
            actual_error = abs(epsilon - approximation)
            bound = 4 * prefactor * ratio**(degree + 1) / (1 - ratio)
            truncations.append({
                "N": degree,
                "approximation": decimal(approximation),
                "absolute_error": decimal(actual_error),
                "analytic_bound_evaluated_numerically": decimal(bound),
                "error_divided_by_bound": decimal(actual_error / bound),
                "observed_error_within_bound": bool(actual_error <= bound),
            })
        passed = (0 < ratio < 1 and root_error <= tolerance and residual <= tolerance
                  and all(error <= tolerance for error in coefficient_errors)
                  and all(row["observed_error_within_bound"] for row in truncations))
        records.append({
            "X": x_value,
            "r_X": decimal(ratio),
            "epsilon_from_independent_root_solve": decimal(epsilon),
            "root_vs_W_relative_error": decimal(root_error),
            "root_scaled_residual": decimal(residual),
            "B1_to_B4_closed_formula_relative_errors": [decimal(e) for e in coefficient_errors],
            "truncations": truncations,
            "passed": bool(passed),
        })
    return {
        "scope": "Finite numerical checks; no assertion of a computational proof for all X",
        "passed": all(row["passed"] for row in records),
        "cases": records,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--dps", type=int, default=120,
                        help="mpmath working decimal precision (minimum 80; default 120)")
    parser.add_argument("--require-symbolic", action="store_true",
                        help="fail if optional SymPy exact checks cannot run")
    args = parser.parse_args()
    if args.dps < 80:
        parser.error("--dps must be at least 80")
    mp.mp.dps = args.dps
    tolerance = mp.mpf(10)**(-(args.dps - 25))
    a = mp.log(2) / 20
    exact = exact_parameter_checks()
    symbolic = symbolic_checks()
    relations = numerical_relation_checks(a, tolerance)
    expansion = numerical_expansion_checks(a, tolerance)
    symbolic_ok = symbolic["passed"] is True or (
        symbolic["status"] == "skipped" and not args.require_symbolic)
    receipt = {
        "receipt_schema": "ordered-matrix-inversion-checks-v1",
        "scope": "Supplemental verification of stated formulas, not a formalization of the article",
        "dependencies": {"mpmath": mp.__version__, "sympy": symbolic.get("sympy_version")},
        "mpmath_decimal_precision": args.dps,
        "numerical_relative_tolerance": decimal(tolerance),
        "display_significant_digits": DISPLAY_DIGITS,
        "parameter_a": "log(2)/20",
        "exact_rational_checks": exact,
        "exact_symbolic_checks": symbolic,
        "high_precision_numerical_relation_checks": relations,
        "high_precision_numerical_expansion_checks": expansion,
        "all_requested_checks_passed": bool(exact["passed"] and symbolic_ok
                                           and relations["passed"] and expansion["passed"]),
    }
    print(json.dumps(receipt, indent=2, sort_keys=True, ensure_ascii=True))
    return 0 if receipt["all_requested_checks_passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
