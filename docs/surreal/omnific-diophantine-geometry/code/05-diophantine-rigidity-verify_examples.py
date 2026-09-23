#!/usr/bin/env python3
"""Exact, finite checks accompanying 'Omnific Integers and Diophantine Rigidity'.

These checks do not constitute a formal verification of the article. In
particular they do not implement arbitrary surreal normal forms or prove
statements about infinite supports, all integer solutions, or class-sized rings.

Requires Python 3.9+ and SymPy. Run:
    python verify_examples.py
    python verify_examples.py --standard-radius 40
"""

from __future__ import annotations

import argparse
import math
from typing import Dict, List, Tuple

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required. Install it with: python -m pip install sympy") from exc


def check_zero(expression: sp.Expr, description: str) -> None:
    """Raise an explicit error instead of relying on Python's disableable assert."""
    value = sp.cancel(sp.expand(expression))
    if value != 0:
        raise RuntimeError(f"FAILED: {description}: residual {value}")


def four_squares(n: int) -> Tuple[int, int, int, int]:
    """Construct a four-square certificate for one ordinary nonnegative integer.

    This finite pair-sum search does not prove that every input will succeed;
    that universal assertion is the imported theorem of Lagrange.
    """
    if n < 0:
        raise ValueError("four_squares requires a nonnegative integer")
    pairs: Dict[int, Tuple[int, int]] = {}
    for a in range(math.isqrt(n) + 1):
        for b in range(a, math.isqrt(n - a * a) + 1):
            pairs.setdefault(a * a + b * b, (a, b))
    for total, pair in pairs.items():
        other = pairs.get(n - total)
        if other is not None:
            result = pair + other
            if sum(v * v for v in result) != n:
                raise RuntimeError("Invalid four-square certificate")
            return result
    raise RuntimeError(f"No four-square certificate found for {n}")


def pell_above(bound: int) -> Tuple[int, int]:
    """Return a positive ordinary Pell witness with x >= bound."""
    x, y = 3, 2
    while x < bound:
        x, y = 3 * x + 4 * y, 2 * x + 3 * y
    if x * x - 2 * y * y != 1:
        raise RuntimeError("Invalid Pell certificate")
    return x, y


def run_checks(radius: int) -> List[str]:
    if not 0 <= radius <= 200:
        raise ValueError("standard-radius must lie between 0 and 200")
    report: List[str] = []
    t, x, y, z, dx, dy, dz, c = sp.symbols("t x y z dx dy dz c")

    check_zero((3 * x + 4 * y) ** 2 - 2 * (2 * x + 3 * y) ** 2
               - (x ** 2 - 2 * y ** 2), "Pell recurrence")
    report.append("PASS: symbolic Pell recurrence preserves x^2 - 2 y^2.")

    px, py, pz = 2 * t, t ** 2 - 1, t ** 2 + 1
    check_zero(px ** 2 + py ** 2 - pz ** 2, "Pythagorean identity")
    check_zero(t * px / 2 - py - 1, "Pythagorean unit-ideal witness")
    report.append("PASS: symbolic Pythagorean identity and (t/2)x - y = 1.")

    rho = sp.sqrt(2) - 1
    check_zero(rho ** 2 + 2 * rho - 1, "Euclidean remainder ratio")
    report.append("PASS: rho^2 + 2 rho = 1 for rho = sqrt(2) - 1.")

    separated_cases = 0
    for m in range(2, 10):
        for n in range(2, 10):
            f = x ** m - y ** n - c
            df = m * x ** (m - 1) * dx - n * y ** (n - 1) * dy
            lhs = x ** (m - 1) * (n * x * dy - m * y * dx) - n * c * dy
            check_zero(lhs - (n * f * dy - y * df),
                       f"Separated-power derivative identity ({m}, {n})")
            if (m * n - m - n <= 0) != ((m, n) == (2, 2)):
                raise RuntimeError("Incorrect degree inequality case")
            separated_cases += 1
    report.append(f"PASS: {separated_cases} exact separated-power identities, 2 <= m,n <= 9.")

    for p in range(2, 11):
        f = x ** p + y ** p - z ** p
        df_over_p = x ** (p - 1) * dx + y ** (p - 1) * dy - z ** (p - 1) * dz
        w_identity = (x ** (p - 1) * (z * dx - x * dz)
                      + y ** (p - 1) * (z * dy - y * dz))
        check_zero(w_identity - (z * df_over_p - dz * f),
                   f"Fermat Wronskian identity p={p}")
    report.append("PASS: exact Fermat Wronskian identities for 2 <= p <= 10.")

    u, v, a = sp.symbols("u v a", nonzero=True)
    for length in range(1, 17):
        q = sum(a / u * (v / u) ** k for k in range(length))
        check_zero((u - v) * q - a * (1 - (v / u) ** length),
                   f"Finite geometric telescoping length={length}")
    report.append("PASS: 16 finite geometric telescoping identities.")
    report.append("NOTE: this last check is NOT an infinite-sum convergence or support proof.")

    # Formal power-series coefficients, only to the stated finite order.
    s = sp.symbols("s")
    for n in range(2, 8):
        truncation = sum(sp.binomial(sp.Rational(1, n), k) * s ** k
                         for k in range(7))
        residual = sp.series(truncation ** n - (1 + s), s, 0, 7).removeO()
        check_zero(residual, f"Binomial nth-root coefficients n={n}")
    report.append("PASS: nth-root binomial coefficients through order 6 for 2 <= n <= 7.")

    certificate_samples: List[str] = []
    for standard_t in range(-radius, radius + 1):
        pell_x, pell_y = pell_above(standard_t * standard_t)
        squares = four_squares(pell_x - standard_t * standard_t)
        first = pell_x * pell_x - 2 * pell_y * pell_y - 1
        second = pell_x - standard_t * standard_t - sum(q * q for q in squares)
        quartic = first * first + second * second
        if quartic != 0:
            raise RuntimeError(f"Quartic certificate failed for t={standard_t}")
        if standard_t in {0, 1, radius}:
            certificate_samples.append(
                f"  t={standard_t}: x={pell_x}, y={pell_y}, z={squares}")
    report.append(f"PASS: explicit quartic-definition certificates for all t in [-{radius},{radius}].")
    report.extend(certificate_samples)

    for mx, my in [(-1, 0), (0, 1), (0, -1), (2, 3), (2, -3)]:
        if my * my != mx ** 3 + 1:
            raise RuntimeError("Incorrect displayed Mordell example")
    report.append("PASS: the five displayed points on y^2 = x^3 + 1.")
    report.append("NOTE: no completeness assertion for the integer solution set is checked.")
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--standard-radius", type=int, default=40,
                        help="Check ordinary quartic-definition inputs from -R to R (0 <= R <= 200).")
    args = parser.parse_args()
    print("Exact finite checks for Omnific Integers and Diophantine Rigidity")
    print(f"SymPy version: {sp.__version__}")
    for line in run_checks(args.standard_radius):
        print(line)
    print("ALL FINITE CHECKS PASSED. No full formal verification is claimed.")


if __name__ == "__main__":
    main()
