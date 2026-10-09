#!/usr/bin/env python3
"""Symbolic and high-precision checks of the optimal scalar remainder theorem.

This is an experiment, not an interval certificate for the continuous supremum.
The accompanying proof establishes global localization and uniqueness. SymPy
checks exact coefficients, while mpmath locates the predicted local maximum
and compares its value with independent points across the scalar domain.

Run from any directory, for example::

    python experiments/sharp_scalar.py --orders 1,2,3,4,5,6 --m 1000,10000

The default output files are results/sharp_scalar.csv and
results/sharp_scalar_symbolic.json. Requires sympy and mpmath.
"""

from __future__ import annotations

import argparse
import csv
import json
from math import comb, factorial
from pathlib import Path

import mpmath as mp
import sympy as sp


def symbolic_coefficients(degree):
    """Coefficients from the exact differential identity (1-x)E'=-mxE."""
    m = sp.Symbol("m")
    coefficients = [sp.Integer(1)]
    if degree:
        coefficients.append(sp.Integer(0))
    for k in range(2, degree + 1):
        coefficients.append(sp.expand(
            ((k - 1) * coefficients[k - 1] - m * coefficients[k - 2]) / k
        ))
    return m, coefficients


def validate_symbolic(order):
    m, c = symbolic_coefficients(2 * order + 2)
    s = order
    sign = (-1) ** s
    leading = sp.Rational(1, 2**s * factorial(s))
    subleading = sp.expand(sign * c[2 * s]).coeff(m, s - 1)
    linear = sp.expand(sign * c[2 * s + 1]).coeff(m, s)
    quadratic = -sp.expand(sign * c[2 * s + 2]).coeff(m, s + 1)
    beta = sp.simplify(linear / (2 * quadratic))
    correction = sp.simplify((subleading + linear**2 / (4 * quadratic)) / leading)
    expected_beta = sp.Rational(2 * s * (s + 1), 3)
    expected_correction = sp.Rational(s * (-2 * s * s + 5 * s + 1), 9)
    assert sp.expand(sign * c[2 * s]).coeff(m, s) == leading
    assert sp.simplify(beta - expected_beta) == 0
    assert sp.simplify(correction - expected_correction) == 0
    assert subleading == -leading * sp.Rational(s * (s - 1) * (4 * s + 1), 9)

    # Independently check the symbolic coefficient polynomials at integer m
    # using the direct binomial-exponential convolution.
    for m_value in (1, 2, 7, 19):
        for k, polynomial in enumerate(c):
            direct = sum(
                sp.Rational(
                    (-1) ** j * comb(m_value, j) * m_value ** (k - j),
                    factorial(k - j),
                )
                for j in range(min(m_value, k) + 1)
            )
            assert polynomial.subs(m, m_value) == direct

    return {
        "s": s,
        "leading_A": str(leading),
        "c_2s": str(c[2 * s]),
        "c_2s_plus_1": str(c[2 * s + 1]),
        "c_2s_plus_2": str(c[2 * s + 2]),
        "maximizer_beta": str(beta),
        "relative_second_coefficient": str(correction),
        "absolute_second_coefficient": str(sp.simplify(leading * correction)),
    }


def mp_coefficients(m, degree):
    """Exact rational convolution evaluated at current mpmath precision."""
    return [
        mp.fsum(
            mp.mpf((-1) ** j * comb(m, j) * m ** (k - j)) / factorial(k - j)
            for j in range(min(m, k) + 1)
        )
        for k in range(degree + 1)
    ]


def numerical_peak(m, order, digits=120):
    with mp.workdps(digits):
        s, degree = order, 2 * order
        c = mp_coefficients(m, degree)
        polynomial_coefficients = c[:degree]
        derivative_coefficients = [k * c[k] for k in range(1, degree)]
        sign = (-1) ** s
        leading = mp.mpf(1) / (2**s * factorial(s))
        beta = mp.mpf(2 * s * (s + 1)) / 3
        expected_relative = mp.mpf(s * (-2 * s * s + 5 * s + 1)) / 9

        def exponential(x):
            return mp.exp(m * (mp.log1p(-x) + x)) if x != 1 else mp.mpf(0)

        def polynomial(x):
            return mp.polyval(list(reversed(polynomial_coefficients)), x)

        def quotient(x):
            if x == 0:
                return abs(c[degree]) / mp.mpf(m) ** s
            return abs(exponential(x) - polynomial(x)) / (x**degree * mp.mpf(m)**s)

        def derivative_numerator(x):
            e = exponential(x)
            q = polynomial(x)
            e_prime = -m * x / (1 - x) * e
            q_prime = mp.polyval(list(reversed(derivative_coefficients)), x)
            return sign * (x * (e_prime - q_prime) - degree * (e - q))

        guess = beta / m
        left, right = guess / 4, min(mp.mpf("0.99"), guess * 4)
        left_value, right_value = derivative_numerator(left), derivative_numerator(right)
        if not (left_value > 0 and right_value < 0):
            raise ArithmeticError(
                f"Asymptotic maximum not bracketed at m={m}, s={s}; use a larger m."
            )
        # Bisection avoids relying on a Newton starting point or on an
        # unverified optimizer status flag.
        for _ in range(180):
            midpoint = (left + right) / 2
            value = derivative_numerator(midpoint)
            if value > 0:
                left = midpoint
            else:
                right = midpoint
        maximizer = (left + right) / 2
        peak = quotient(maximizer)

        probes = [mp.mpf(0), mp.mpf(1)]
        probes += [guess * mp.mpf(k) / 8 for k in range(1, 65) if guess * k / 8 <= 1]
        root_m = mp.sqrt(m)
        probes += [mp.mpf(k) / (8 * root_m) for k in range(1, 129)
                   if mp.mpf(k) / (8 * root_m) <= 1]
        probes += [mp.mpf(k) / 32 for k in range(1, 32)]
        largest_probe = max(quotient(x) for x in probes)
        if largest_probe > peak + mp.mpf("1e-40"):
            raise ArithmeticError("A domain probe exceeds the predicted maximum.")

        scaled_first_correction = m * (peak / leading - 1)
        second_residual = m**2 * (peak / leading - 1 - expected_relative / m)
        as_text = lambda number: mp.nstr(number, 32)
        return {
            "m": m,
            "s": s,
            "m_x_peak": as_text(m * maximizer),
            "predicted_beta": as_text(beta),
            "K_over_m_power_s": as_text(peak),
            "leading_A": as_text(leading),
            "m_relative_correction": as_text(scaled_first_correction),
            "predicted_relative_correction": as_text(expected_relative),
            "m2_remaining_relative_residual": as_text(second_residual),
            "grid_probes": len(probes),
            "grid_check_passed": True,
            "working_decimal_digits": digits,
            "numerical_scope": "local root plus domain probes; global optimality is proved analytically",
        }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--orders", default="1,2,3,4,5,6")
    parser.add_argument("--m", default="1000,10000")
    parser.add_argument("--digits", type=int, default=120)
    parser.add_argument("--output-dir", type=Path,
                        default=Path(__file__).resolve().parents[1] / "results")
    args = parser.parse_args()
    orders = [int(value) for value in args.orders.split(",")]
    draw_counts = [int(value) for value in args.m.split(",")]
    if min(orders + draw_counts) < 1 or args.digits < 80:
        parser.error("Orders and m must be positive; use at least 80 decimal digits.")
    symbolic = [validate_symbolic(s) for s in orders]
    numerical = [numerical_peak(m, s, args.digits) for s in orders for m in draw_counts]
    args.output_dir.mkdir(parents=True, exist_ok=True)
    symbolic_path = args.output_dir / "sharp_scalar_symbolic.json"
    numerical_path = args.output_dir / "sharp_scalar.csv"
    symbolic_path.write_text(json.dumps(symbolic, indent=2) + "\n")
    with numerical_path.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(numerical[0]))
        writer.writeheader()
        writer.writerows(numerical)
    print(f"Symbolic identities passed for {len(orders)} orders.")
    print(f"High-precision local peaks and domain probes passed for {len(numerical)} cases.")
    print(f"Wrote {symbolic_path}")
    print(f"Wrote {numerical_path}")


if __name__ == "__main__":
    main()
