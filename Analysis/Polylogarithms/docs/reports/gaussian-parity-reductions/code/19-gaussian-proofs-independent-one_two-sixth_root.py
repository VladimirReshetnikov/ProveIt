"""Independent checks of the one-2 sixth-root specialization.

The article proves U_{a,b}(omega) + (-1)**N conjugate(U_{a,b}(omega))
    = R_{N,a} (i*pi)**N,
where omega=exp(i*pi/3), N=a+b+2, and R_{N,a} is rational.
This script constructs R_{N,a} with exact Fraction arithmetic and compares
the specialized formula with the independent logarithmic moment from
one_two_identities.py at both conjugate sixth roots.  It also checks the
two explicit weight-three identities.  Only mpmath and the Python standard
library are required.  These checks are not interval-error certificates.

Run from any working directory:
    python path/to/sixth_root.py --digits 100
An optional --output argument overrides the package-relative JSON path.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from functools import lru_cache
import json
from math import comb, factorial
from pathlib import Path

import mpmath as mp

from one_two_identities import one_two_closed, one_two_quadrature


@lru_cache(maxsize=None)
def bernoulli_number(n: int) -> Fraction:
    """The exact convention B_0=1, B_1=-1/2."""
    if n < 0:
        raise ValueError("Bernoulli index must be nonnegative")
    if n == 0:
        return Fraction(1)
    return -sum(
        (comb(n + 1, k) * bernoulli_number(k) for k in range(n)),
        Fraction(0),
    ) / (n + 1)


def bernoulli_polynomial(n: int, x: Fraction) -> Fraction:
    return sum(
        (comb(n, k) * bernoulli_number(k) * x ** (n - k)
         for k in range(n + 1)),
        Fraction(0),
    )


def parity_coefficient(n: int, a: int) -> Fraction:
    """The exact rational R_{N,a} multiplying (i*pi)**N."""
    if n < 2 or not 0 <= a <= n - 2:
        raise ValueError("require N >= 2 and 0 <= a <= N-2")
    coefficient = Fraction(-2, 3**n * factorial(n))
    for k in range(a + 1, n + 1):
        coefficient -= (
            Fraction((-1) ** (a + k) * comb(k - 1, a) * 2**k,
                     3 ** (n - k) * factorial(n - k) * factorial(k))
            * bernoulli_polynomial(k, Fraction(1, 6))
        )
    for m in range(n - a, n + 1):
        if m % 2 == 0:
            coefficient += (
                Fraction((-1) ** (n - a) * comb(m - 1, n - a - 1) * 2**m,
                         3 ** (n - m) * factorial(n - m) * factorial(m))
                * bernoulli_number(m)
            )
    return coefficient


def mp_fraction(value: Fraction):
    return mp.mpf(value.numerator) / value.denominator


def sixth_root_closed(a: int, b: int, sign: int = 1):
    """Closed formula with exactly L=sign*i*pi/3 and w=omega**sign."""
    if a < 0 or b < 0 or sign not in (-1, 1):
        raise ValueError("require a,b >= 0 and sign in {-1,1}")
    n = a + b + 2
    z = (1 + sign * mp.j * mp.sqrt(3)) / 2
    ell = sign * mp.j * mp.pi / 3
    return (
        sum(
            (-1) ** (a + k) * comb(k - 1, a)
            * ell ** (n - k) / factorial(n - k) * mp.polylog(k, z)
            for k in range(a + 1, n + 1)
        )
        - ell**n / factorial(n)
        + (-1) ** (b + 1) * sum(
            comb(b + j + 1, j) * ell ** (a - j)
            / factorial(a - j) * mp.zeta(b + j + 2)
            for j in range(a + 1)
        )
    )


def run_checks(digits: int = 100):
    if digits < 30:
        raise ValueError("at least 30 working decimal digits are required")
    mp.mp.dps = digits
    tolerance = mp.power(10, -digits + 5)
    records = []
    moments = {}
    maxima = {
        "specialized_vs_moment": mp.mpf(0),
        "general_vs_specialized": mp.mpf(0),
        "parity_projection": mp.mpf(0),
        "pure_component": mp.mpf(0),
        "explicit_weight3": mp.mpf(0),
    }
    for sign in (1, -1):
        z = (1 + sign * mp.j * mp.sqrt(3)) / 2
        for n in range(2, 9):
            for a in range(n - 1):
                b = n - a - 2
                r = parity_coefficient(n, a)
                pure_r = r * Fraction((-1) ** (n // 2), 2)
                if n % 2:
                    pure_r *= sign
                value = sixth_root_closed(a, b, sign)
                moment = one_two_quadrature(a, b, z)
                general = one_two_closed(a, b, z)
                moments[sign, n, a] = moment
                parity_lhs = moment + (-1) ** n * mp.conj(moment)
                parity_rhs = mp_fraction(r) * (sign * mp.j * mp.pi) ** n
                component = mp.re(moment) if n % 2 == 0 else mp.im(moment)
                pure_rhs = mp_fraction(pure_r) * mp.pi**n
                residuals = {
                    "specialized_vs_moment": abs(value - moment),
                    "general_vs_specialized": abs(general - value),
                    "parity_projection": abs(parity_lhs - parity_rhs),
                    "pure_component": abs(component - pure_rhs),
                }
                for key, residual in residuals.items():
                    maxima[key] = max(maxima[key], residual)
                    if residual >= tolerance:
                        raise AssertionError(
                            f"{key} failed at sign={sign}, N={n}, a={a}: "
                            f"{mp.nstr(residual, 12)}"
                        )
                records.append({
                    "root": "omega" if sign == 1 else "conjugate_omega",
                    "weight": n,
                    "a": a,
                    "b": b,
                    "R_N_a": str(r),
                    "pure_component": "real" if n % 2 == 0 else "imaginary",
                    "pure_component_over_pi_to_weight": str(pure_r),
                    "specialized_real": mp.nstr(mp.re(value), digits),
                    "specialized_imaginary": mp.nstr(mp.im(value), digits),
                    "moment_real": mp.nstr(mp.re(moment), digits),
                    "moment_imaginary": mp.nstr(mp.im(moment), digits),
                    "residuals": {key: mp.nstr(residual, 12)
                                  for key, residual in residuals.items()},
                })

    # Use a separate real Clausen evaluation for the explicit formulas.
    clausen = mp.clsin(2, mp.pi / 3)
    explicit = []
    for sign in (1, -1):
        rhs21 = (2 * mp.zeta(3) / 3 - mp.pi * clausen / 3
                 + sign * mp.j * mp.pi**3 / 324)
        rhs12 = (-4 * mp.zeta(3) / 3 + mp.pi * clausen / 3
                 + sign * mp.j * mp.pi**3 / 324)
        for a, name, rhs in ((0, "Li_2_1", rhs21), (1, "Li_1_2", rhs12)):
            moment = moments[sign, 3, a]
            residual = abs(moment - rhs)
            maxima["explicit_weight3"] = max(maxima["explicit_weight3"], residual)
            if residual >= tolerance:
                raise AssertionError(f"{name} failed for sign={sign}")
            explicit.append({
                "root": "omega" if sign == 1 else "conjugate_omega",
                "identity": name,
                "rhs_real": mp.nstr(mp.re(rhs), digits),
                "rhs_imaginary": mp.nstr(mp.im(rhs), digits),
                "residual": mp.nstr(residual, 12),
            })

    assert parity_coefficient(2, 0) == Fraction(-1, 18)
    assert parity_coefficient(3, 0) == parity_coefficient(3, 1) == Fraction(-1, 162)
    return {
        "working_decimal_digits": digits,
        "status": "Numerical checks of proved identities; no quadrature error certificate.",
        "exact_arithmetic": "R_N_a and Bernoulli values use fractions.Fraction.",
        "root_convention": "omega=(1+i*sqrt(3))/2; all branches are principal.",
        "scope": "All positions of one 2 at weights 2 through 8, at both conjugate roots.",
        "comparison_count": len(records),
        "explicit_example_count": len(explicit),
        "failure_threshold": mp.nstr(tolerance, 12),
        "maximum_residuals": {key: mp.nstr(value, 12) for key, value in maxima.items()},
        "records": records,
        "explicit_weight3_examples": explicit,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--digits", type=int, default=100)
    parser.add_argument(
        "--output", type=Path,
        default=Path(__file__).resolve().parents[3]
                / "results" / "independent" / "one_two" / "sixth_root_checks.json",
    )
    args = parser.parse_args()
    if args.digits < 30:
        parser.error("at least 30 working decimal digits are required")
    report = run_checks(args.digits)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", encoding="utf-8") as stream:
        json.dump(report, stream, indent=2)
        stream.write("\n")
    print(json.dumps({
        "comparison_count": report["comparison_count"],
        "explicit_example_count": report["explicit_example_count"],
        "maximum_residuals": report["maximum_residuals"],
        "output": str(args.output.resolve()),
    }, indent=2))
