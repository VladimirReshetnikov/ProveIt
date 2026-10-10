#!/usr/bin/env python3
"""Independently verify six CM genus-ratio radical identities.

This file uses only Python's standard library and exact Fraction arithmetic.
It does not import SymPy, mpmath, cm_genus.py, or their receipts.

For each of D=-15,-20,-39, the supplied quadratic genus factors H_+, H_-
and period data imply

    R_4^3 = A^6 u^(-t) |H_+(0)/H_-(0)|,
    R_6^2 = A^6 u^(-t) |H_+(1728)/H_-(1728)|,

where t=12 h(e) L(0, chi_{D_-}).  This script checks these two equalities
and the positivity needed for unique positive-root extraction, using
rational pairs representing a+b*sqrt(e).  The analytic period theorem,
the Hilbert-polynomial certificates, and the assignment of the two
factors to their genera are separate inputs, proved in cm_genus.tex and
certified by cm_genus.py.  No assertion about those inputs is established
merely by this arithmetic check.

Run:
    python3 verify_genus_arithmetic.py

Output:
    verify_genus_arithmetic_receipt.json beside this script.
"""

from fractions import Fraction as F
from pathlib import Path
import json
import platform


def multiply(x, y, e):
    """Multiply two rational pairs in Q(sqrt(e))."""
    return (x[0] * y[0] + e * x[1] * y[1],
            x[0] * y[1] + x[1] * y[0])


def inverse(x, e):
    norm = x[0] * x[0] - e * x[1] * x[1]
    if norm == 0:
        raise ZeroDivisionError("Zero quadratic-field denominator")
    return (x[0] / norm, -x[1] / norm)


def power(x, n, e):
    if n < 0:
        return power(inverse(x, e), -n, e)
    result = (F(1), F(0))
    for _ in range(n):
        result = multiply(result, x, e)
    return result


def quotient(x, y, e):
    return multiply(x, inverse(y, e), e)


def is_positive(x, e):
    """Exact sign at the embedding sqrt(e)>0, without numerical roots."""
    a, b = x
    if b == 0:
        return a > 0
    if a >= 0 and b >= 0:
        return True
    if a <= 0 and b <= 0:
        return False
    # In the remaining cases, compare the two nonnegative magnitudes
    # by squaring. Here e is 5 or 13, so a nonzero pair cannot vanish.
    return a * a > e * b * b if a > 0 else e * b * b > a * a


def absolute(x, e):
    if x == (F(0), F(0)) or is_positive(x, e):
        return x
    return (-x[0], -x[1])


def evaluate(poly, x):
    """Horner evaluation; polynomial coefficients are in ascending order."""
    result = (F(0), F(0))
    for a, b in reversed(poly):
        result = (result[0] * x + a, result[1] * x + b)
    return result


def pair_json(x):
    return {"rational_coefficient": str(x[0]),
            "sqrt_coefficient": str(x[1])}


# Each entry specifies: D, e, A, u, t, H_+, R_4, R_6.
# The conjugate of H_+ is H_-. All constants below are rational integers
# or exact fractions; every root is represented by a rational pair.
DATA = [
    (-15, 5, F(1, 2), (F(1, 2), F(1, 2)), 4,
     [(F(191025, 2), F(85995, 2)), (F(1), F(0))],
     (F(21, 44), F(2, 11)),
     (F(29, 88), F(3, 22))),
    (-20, 5, F(1, 2), (F(1, 2), F(1, 2)), 6,
     [(F(-632000), F(-282880)), (F(1), F(0))],
     (F(29, 44), F(3, 11)),
     (F(601, 1672), F(63, 418))),
    (-39, 13, F(3, 4), (F(3, 2), F(1, 2)), 4,
     [(F(63399280527, 2), F(17399806263, 2)),
      (F(165765798), F(45975573)), (F(1), F(0))],
     (F(103299, 181424), F(555, 22678)),
     (F(1323, 1472), F(81, 368))),
]


def verify():
    checks = []
    for D, e, A, u, t, hp, r4, r6 in DATA:
        hm = [(a, -b) for a, b in hp]
        for point, weight, candidate, exponent in [
                (0, 4, r4, 3), (1728, 6, r6, 2)]:
            polynomial_ratio = absolute(
                quotient(evaluate(hp, F(point)),
                         evaluate(hm, F(point)), e), e)
            target = multiply(power(u, -t, e), polynomial_ratio, e)
            target = (A ** 6 * target[0], A ** 6 * target[1])
            candidate_power = power(candidate, exponent, e)
            if candidate_power != target:
                raise AssertionError((D, weight, "identity failed"))
            if not is_positive(candidate, e):
                raise AssertionError((D, weight, "root is not positive"))
            checks.append({
                "discriminant": D,
                "quadratic_field_radicand": e,
                "weight": weight,
                "root_extraction_power": exponent,
                "polynomial_evaluation_point": point,
                "A": str(A),
                "unit": pair_json(u),
                "unit_exponent": -t,
                "candidate_ratio": pair_json(candidate),
                "absolute_genus_polynomial_ratio": pair_json(polynomial_ratio),
                "candidate_power": pair_json(candidate_power),
                "period_formula_target": pair_json(target),
                "equality_verified_exactly": True,
                "candidate_verified_positive_exactly": True,
            })
    return checks


def main():
    checks = verify()
    receipt = {
        "method": "Independent exact Fraction arithmetic in real quadratic fields",
        "python_version": platform.python_version(),
        "external_dependencies": [],
        "scope": (
            "Six radical equalities and their positive-root choices. "
            "The analytic genus formula and labeled genus factors are inputs."
        ),
        "number_of_equalities": len(checks),
        "checks": checks,
    }
    destination = Path(__file__).with_name(
        "verify_genus_arithmetic_receipt.json")
    destination.write_text(json.dumps(receipt, indent=2) + "\n",
                           encoding="utf-8")
    for check in checks:
        print("D =", check["discriminant"], "weight =", check["weight"],
              ": exact equality and positivity verified")
    print("Receipt:", destination)


if __name__ == "__main__":
    main()
