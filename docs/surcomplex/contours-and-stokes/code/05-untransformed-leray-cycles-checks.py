#!/usr/bin/env python3
"""Exact finite checks for the mixed six-sheeted Hahn residue example.

Requires Python 3.10+ and SymPy. Run from any directory:
    python code/checks.py --output data/checks.json

The checks are not formal verification of the general analytic or Hahn proofs.
No network access, numerical integration, or floating-point tolerance is used.
"""
from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path
from typing import Any

import sympy as sp


def run_checks() -> dict[str, Any]:
    t, s, a, b, x, y, r = sp.symbols("t s a b x y r", nonzero=True)
    counts: Counter[str] = Counter()

    def check_equal(lhs: Any, rhs: Any, category: str, label: str) -> None:
        if isinstance(lhs, sp.MatrixBase) or isinstance(rhs, sp.MatrixBase):
            difference = sp.Matrix(lhs) - sp.Matrix(rhs)
            ok = all(sp.cancel(entry) == 0 for entry in difference)
        else:
            ok = sp.cancel(sp.expand(lhs - rhs)) == 0
        if not ok:
            raise AssertionError(f"{category}: {label}: {lhs!s} != {rhs!s}")
        counts[category] += 1

    basis = [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)]
    index = {pair: i for i, pair in enumerate(basis)}

    def reduced_monomial(px: int, py: int) -> tuple[sp.Expr, int]:
        qx, rx = divmod(px, 2)
        qy, ry = divmod(py, 3)
        return (-t) ** qx * (2 * t) ** qy, index[(rx, ry)]

    def multiplication(dx: int, dy: int) -> sp.Matrix:
        matrix = sp.zeros(6)
        for col, (px, py) in enumerate(basis):
            scalar, row = reduced_monomial(px + dx, py + dy)
            matrix[row, col] = scalar
        return matrix

    mx, my = multiplication(1, 0), multiplication(0, 1)
    identity, zero = sp.eye(6), sp.zeros(6)
    check_equal(mx * my, my * mx, "quotient", "commuting multiplication")
    check_equal(mx ** 2, -t * identity, "quotient", "x^2=-t")
    check_equal(my ** 3, 2 * t * identity, "quotient", "y^3=2t")
    check_equal(mx ** 2 + my ** 3 - t * identity, zero, "quotient", "F1=0")
    check_equal(mx ** 2 + 3 * my ** 3 - 5 * t * identity,
                zero, "quotient", "F2=0")
    jacobian = sp.Matrix([x**2 + y**3 - t, x**2 + 3*y**3 - 5*t]).jacobian([x, y]).det()
    check_equal(jacobian, 12 * x * y**2, "quotient", "Jacobian determinant")
    jmat = 12 * mx * my**2
    jinv = jmat.inv()
    check_equal(jmat * jinv, identity, "quotient", "Jacobian inverse over Q(t)")

    def expected_residue(px: int, py: int) -> sp.Expr:
        if px % 2 == 1 and py % 3 == 2:
            return sp.Rational(1, 2) * (-t)**((px-1)//2) * (2*t)**((py-2)//3)
        return sp.S.Zero

    xpowers = [mx**k for k in range(15)]
    ypowers = [my**k for k in range(15)]
    for px in range(15):
        for py in range(15):
            matrix = xpowers[px] * ypowers[py]
            residue = sp.trace(matrix * jinv)
            check_equal(residue, expected_residue(px, py),
                        "monomial_residues", f"x^{px} y^{py}")
    check_equal(sp.trace(jmat * jinv), 6, "normalization", "R(J)=6")
    check_equal(sp.trace(mx * my**2 * jinv), sp.Rational(1, 2),
                "normalization", "R(x y^2)=1/2")

    # Telescoping relations checked directly from the independent closed formula.
    for px in range(10):
        for py in range(10):
            f1 = (expected_residue(px+2, py) + expected_residue(px, py+3)
                  - t*expected_residue(px, py))
            f2 = (expected_residue(px+2, py) + 3*expected_residue(px, py+3)
                  - 5*t*expected_residue(px, py))
            check_equal(f1, 0, "ideal_annihilation", f"F1 x^{px} y^{py}")
            check_equal(f2, 0, "ideal_annihilation", f"F2 x^{px} y^{py}")

    # Work with x^2 and y^3 to verify the branch-independent target equations.
    zx2 = (3*s**6*a**6-s**12*b)/2
    zy3 = (s**12*b-s**6*a**6)/2
    check_equal(zx2 + zy3, s**6*a**6, "target_equations", "ordinary target 1")
    check_equal(zx2 + 3*zy3, s**12*b, "target_equations", "ordinary target 2")
    phix2, phiy3 = zx2-s**40, zy3+2*s**40
    check_equal(phix2 + phiy3 - s**40, s**6*a**6,
                "target_equations", "adapted target 1")
    check_equal(phix2 + 3*phiy3 - 5*s**40, s**12*b,
                "target_equations", "adapted target 2")
    check_equal(sp.det(sp.Matrix([[1, 1], [1, 3]])), 2,
                "target_equations", "ordered equation determinant")

    # Ordinary binomial jets: no symbolic branch simplification is trusted.
    for denominator in (2, 3):
        for order in range(1, 13):
            exponent = sp.Rational(1, denominator)
            truncated = sum(sp.binomial(exponent, k)*r**k for k in range(order+1))
            difference = sp.Poly(sp.expand(truncated**denominator - (1+r)), r)
            for degree in range(order+1):
                check_equal(difference.nth(degree), 0, "binomial_jets",
                            f"root {denominator}, order {order}, coefficient {degree}")

    # The leading changes follow by differentiating x^2 and y^3.
    cx = sp.sqrt(sp.Rational(3, 2))
    cy = -2**(-sp.Rational(1, 3))
    dx = -1/(2*cx*a**3)
    dy = 2/(3*cy**2*a**4)
    check_equal(2*cx*a**3*dx, -1, "displacement", "leading square-root correction")
    check_equal(3*cy**2*a**4*dy, 2, "displacement", "leading cube-root correction")
    check_equal(sp.simplify(dy), 2**sp.Rational(5, 3)/(3*a**4),
                "displacement", "displayed cube-root coefficient")
    check_equal(sp.Rational(1)-4*sp.Rational(1, 40), sp.Rational(36, 40),
                "displacement", "attained valuation bound")

    exponential_coefficients: list[str] = []
    for degree in range(9):
        coefficient = sum(
            sp.Rational(1, 2)*(-1)**p*2**(degree-p)
            / (sp.factorial(2*p+1)*sp.factorial(3*(degree-p)+2))
            for p in range(degree+1)
        )
        independent = sp.S.Zero
        for px in range(2*degree+2):
            for py in range(3*degree+3):
                term = expected_residue(px, py)
                independent += sp.expand(term).coeff(t, degree)/(sp.factorial(px)*sp.factorial(py))
        check_equal(coefficient, independent, "entire_numerator", f"coefficient t^{degree}")
        exponential_coefficients.append(str(sp.factor(coefficient)))

    return {
        "status": "PASS",
        "arithmetic": "Exact symbolic arithmetic over Q(t), with exact algebraic constants",
        "sympy_version": sp.__version__,
        "tests_passed": sum(counts.values()),
        "tests_by_category": dict(sorted(counts.items())),
        "basis": ["1", "y", "y^2", "x", "x*y", "x*y^2"],
        "multiplication_x": str(mx),
        "multiplication_y": str(my),
        "exp_residue_coefficients_t0_through_t8": exponential_coefficients,
        "leading_displacement": {"x_radial_degree": 37, "x_coefficient": str(dx),
                                 "y_radial_degree": 36, "y_coefficient": str(sp.simplify(dy))},
        "limitations": [
            "Finite checks only; not a proof assistant.",
            "Does not verify arbitrary-support Hahn summability or the general analytic proofs.",
            "Does not establish novelty or historical priority."
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("data/checks.json"))
    args = parser.parse_args()
    report = run_checks()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: {report['tests_passed']} exact checks; report: {args.output}")
    for category, count in report["tests_by_category"].items():
        print(f"  {category}: {count}")


if __name__ == "__main__":
    main()
