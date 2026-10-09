#!/usr/bin/env python3
"""Reproduce the all-weight Gaussian Euler-sum checks.

These are high-precision numerical consistency checks, not proof certificates.
The article supplies the analytic proof.  No PSLQ or fitted coefficients are used.
Run: python code/verify_gaussian.py --dps 90
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction
from math import comb, factorial
from pathlib import Path

import mpmath as mp


def euler_even(up_to: int) -> list[int]:
    """E_0,...,E_(2*up_to), where sech(t)=sum E_n*t^n/n!."""
    values = [1]
    for n in range(1, up_to + 1):
        values.append(-sum(comb(2 * n, 2 * k) * values[k] for k in range(n)))
    return values


def beta(s: int) -> mp.mpf:
    return (mp.zeta(s, mp.mpf(1) / 4) - mp.zeta(s, mp.mpf(3) / 4)) / 4**s


def exact_coefficients(m: int) -> list[Fraction]:
    """Coefficients of pi^(2m-1-2k)*B_k, k=0,...,m-1.

    B_0=log(2); B_k=zeta(2k+1) for k>0. All returned coefficients
    include the negative sign in the finite reduction.
    """
    evens = euler_even(m - 1)
    result = []
    for k in range(m):
        j = m - 1 - k
        coeff = -Fraction(abs(evens[j]), 2 ** (2 * j + 1) * factorial(2 * j))
        if k:
            coeff *= 1 - Fraction(1, 2 ** (2 * k + 1))
        result.append(coeff)
    return result


def finite_formula(m: int) -> mp.mpf:
    answer = (2 * m - 1) * beta(2 * m)
    for k, coefficient in enumerate(exact_coefficients(m)):
        value = mp.log(2) if k == 0 else mp.zeta(2 * k + 1)
        answer += (mp.mpf(coefficient.numerator) / coefficient.denominator
                   * mp.pi ** (2 * m - 1 - 2 * k) * value)
    return answer


def defining_sum(p: int) -> mp.mpf:
    return mp.nsum(lambda n: (-1)**n * mp.harmonic(n) / (2 * n + 1)**p,
                   [1, mp.inf], method="alternating")


def moment_integral(p: int) -> mp.mpf:
    return -mp.quad(lambda x: (-mp.log(x))**(p - 1)
                    * mp.log1p(x * x) / (1 + x * x), [0, 1]) / mp.factorial(p - 1)


def b_derivative(s: mp.mpc) -> mp.mpc:
    return (mp.polygamma(1, (s + 2) / 4) - mp.polygamma(1, s / 4)) / 16


def generating_digamma(z: mp.mpc) -> mp.mpc:
    bracket = mp.digamma(1) - (mp.digamma((1 + z) / 2)
                              + mp.digamma((1 - z) / 2)) / 2
    return (-(b_derivative(1 + z) + b_derivative(1 - z)) / 2
            - mp.pi * bracket / (4 * mp.cos(mp.pi * z / 2)))


def generating_integral(z: mp.mpc) -> mp.mpc:
    return -mp.quad(lambda x: mp.cosh(z * mp.log(x))
                    * mp.log1p(x * x) / (1 + x * x), [0, 1])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dps", type=int, default=90)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data" / "gaussian_checks.json")
    args = parser.parse_args()
    if args.dps < 40:
        parser.error("use at least 40 decimal digits")
    mp.mp.dps = args.dps
    threshold = mp.mpf(10) ** (-(args.dps - 15))
    fmt = lambda value: mp.nstr(value, args.dps)
    checks = []
    for m in range(1, 6):
        p = 2 * m - 1
        direct, integral, closed = defining_sum(p), moment_integral(p), finite_formula(m)
        residual = max(abs(direct - integral), abs(direct - closed), abs(integral - closed))
        assert residual < threshold, (p, residual, threshold)
        checks.append({"p": p, "weight": p + 1, "defining_sum_accelerated": fmt(direct),
                       "moment_integral": fmt(integral), "finite_formula": fmt(closed),
                       "max_pairwise_absolute_residual": fmt(residual),
                       "coefficient_beta": p,
                       "coefficients_log2_then_odd_zeta": [str(c) for c in exact_coefficients(m)]})
    generating_checks = []
    for zr, zi in [("0", "0"), ("0.2", "0"), ("0.6", "0"), ("0.3", "0.2"), ("1.5", "0")]:
        z = mp.mpc(zr, zi)
        a, b = generating_integral(z), generating_digamma(z)
        residual = abs(a - b)
        assert residual < threshold, (z, residual, threshold)
        generating_checks.append({"z": fmt(z), "integral": fmt(a), "digamma": fmt(b),
                                  "absolute_residual": fmt(residual)})
    special = generating_integral(mp.mpf(1))
    special_residual = abs(special + mp.pi**2 / 48)
    assert special_residual < threshold
    payload = {"status": "numerical checks only; analytic proof is in the article",
               "mpmath_version": mp.__version__, "working_decimal_precision": args.dps,
               "absolute_acceptance_threshold": fmt(threshold),
               "euler_sum_checks": checks, "generating_function_checks": generating_checks,
               "resummation_at_one": {"integral": fmt(special), "exact_value": "-pi^2/48",
                                      "absolute_residual": fmt(special_residual)}}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(f"Verified 5 Euler-sum cases, {len(generating_checks)} generating-function values, and F(1).")
    print(f"Maximum Euler-sum residual: {max(mp.mpf(c['max_pairwise_absolute_residual']) for c in checks)}")
    print(f"Results written to {args.output}")


if __name__ == "__main__":
    main()
