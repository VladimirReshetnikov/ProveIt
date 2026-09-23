#!/usr/bin/env python3
"""Exact finite checks accompanying the omnific-ideal research manuscript.

This program does NOT formalize surreal numbers or test a proper-class claim.
It checks arithmetic matrices, finite descent ranks, and symbolic identities.
All number-field operations use polynomial arithmetic over QQ, never floats.

Run from any directory:
    python code/verify.py
    python code/verify.py --output /path/to/verification.json
"""
from __future__ import annotations

import argparse
import json
import platform
import random
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Sequence

import sympy as sp

X = sp.Symbol("x")
CHECKS: list[str] = []


def check(condition: bool, label: str) -> None:
    """Raise explicitly so validation is not disabled by Python's -O option."""
    if not condition:
        raise AssertionError(label)
    CHECKS.append(label)


@dataclass
class NumberField:
    """The exact field QQ[x]/(minimal_polynomial), with polynomial representatives."""
    minimal_polynomial: sp.Expr

    def __post_init__(self) -> None:
        self.modulus = sp.Poly(self.minimal_polynomial, X, domain=sp.QQ)
        if self.modulus.degree() < 1 or not self.modulus.is_irreducible:
            raise ValueError("A positive-degree irreducible polynomial over QQ is required")
        self.degree = self.modulus.degree()

    def canonical(self, value: Any) -> sp.Expr:
        polynomial = sp.Poly(sp.expand(value), X, domain=sp.QQ)
        return sp.rem(polynomial, self.modulus).as_expr()

    def inverse(self, value: Any) -> sp.Expr:
        polynomial = sp.Poly(self.canonical(value), X, domain=sp.QQ)
        if polynomial.is_zero:
            raise ZeroDivisionError("Cannot invert zero in a number field")
        return sp.invert(polynomial, self.modulus).as_expr()

    def coordinates(self, value: Any) -> list[sp.Rational]:
        polynomial = sp.Poly(self.canonical(value), X, domain=sp.QQ)
        return [polynomial.nth(j) for j in range(self.degree)]

    def matrix_rank(self, rows: Sequence[Sequence[Any]]) -> int:
        """Gaussian elimination entirely in QQ[x]/(modulus)."""
        if not rows:
            return 0
        width = len(rows[0])
        if any(len(row) != width for row in rows):
            raise ValueError("Ragged matrix")
        matrix = [[self.canonical(entry) for entry in row] for row in rows]
        pivot_row = 0
        for column in range(width):
            pivot = next((j for j in range(pivot_row, len(matrix))
                          if matrix[j][column] != 0), None)
            if pivot is None:
                continue
            matrix[pivot_row], matrix[pivot] = matrix[pivot], matrix[pivot_row]
            inverse = self.inverse(matrix[pivot_row][column])
            matrix[pivot_row] = [self.canonical(entry * inverse)
                                 for entry in matrix[pivot_row]]
            for j in range(len(matrix)):
                if j != pivot_row and matrix[j][column] != 0:
                    multiplier = matrix[j][column]
                    matrix[j] = [self.canonical(a - multiplier * b)
                                 for a, b in zip(matrix[j], matrix[pivot_row])]
            pivot_row += 1
            if pivot_row == len(matrix):
                break
        return pivot_row


def columns_matrix(columns: Sequence[Sequence[Any]]) -> sp.Matrix:
    if not columns:
        raise ValueError("This finite test expects at least one column")
    return sp.Matrix.hstack(*(sp.Matrix(column) for column in columns))


def serialize_matrix(matrix: sp.MatrixBase) -> list[list[str]]:
    return [[str(matrix[i, j]) for j in range(matrix.cols)]
            for i in range(matrix.rows)]


def product_case(name: str, field: NumberField,
                 left: Sequence[sp.Expr], right: Sequence[sp.Expr],
                 expected_product_rank: int) -> dict[str, Any]:
    left_matrix = columns_matrix([field.coordinates(a) for a in left])
    right_matrix = columns_matrix([field.coordinates(a) for a in right])
    check(left_matrix.rank() == len(left), name + ": left coefficient independence")
    check(right_matrix.rank() == len(right), name + ": right coefficient independence")
    matrix = columns_matrix([field.coordinates(a * b) for a in left for b in right])
    rank = matrix.rank()
    kernel = matrix.nullspace()
    check(rank == expected_product_rank, name + ": product-lattice rank")
    check(len(kernel) == len(left) * len(right) - rank,
          name + ": multiplication-kernel rank")
    for j, vector in enumerate(kernel):
        check(matrix * vector == sp.zeros(matrix.rows, 1),
              f"{name}: kernel vector {j}")
    return {
        "name": name,
        "field_polynomial": str(field.modulus.as_expr()),
        "left_basis": [str(a) for a in left],
        "right_basis": [str(a) for a in right],
        "multiplication_matrix_over_Q": serialize_matrix(matrix),
        "product_rank": rank,
        "multiplication_kernel_rank": len(kernel),
        "kernel_basis_over_Q": [[str(x) for x in vector] for vector in kernel],
    }


def descent_case(name: str, field: NumberField, rows: Sequence[Sequence[Any]],
                 expected: tuple[int, int] | None = None) -> dict[str, Any]:
    if not rows:
        raise ValueError("Specify an explicit row, even for the zero matrix")
    n = len(rows[0])
    coefficients = [[field.coordinates(entry) for entry in row] for row in rows]
    stacked = sp.Matrix([[row[j][degree] for j in range(n)]
                         for degree in range(field.degree) for row in coefficients])
    d = n - field.matrix_rank(rows)
    r = n - stacked.rank()
    check(0 <= r <= d <= n, name + ": descent rank bounds")
    if expected is not None:
        check((d, r) == expected, name + ": expected (d,r)")
    for b_index, vector in enumerate(stacked.nullspace()):
        for row_index, row in enumerate(rows):
            value = field.canonical(sum(row[j] * vector[j] for j in range(n)))
            check(value == 0, f"{name}: rational kernel vector {b_index}, row {row_index}")
    return {
        "name": name,
        "matrix": [[str(entry) for entry in row] for row in rows],
        "d": d,
        "r": r,
        "predicted_free_summands": r,
        "predicted_positive_ideal_summands": d - r,
        "note": "Only finite coefficient ranks are checked; the module formula is proved in the article.",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data" / "verification.json")
    args = parser.parse_args()

    q2 = NumberField(X**2 - 2)
    q3 = NumberField(X**3 - 2)
    q4 = NumberField(X**4 - 2)
    mixed = NumberField(X**4 - 10 * X**2 + 1)

    products = [
        product_case("quadratic self", q2, [1, X], [1, X], 2),
        product_case("cubic two-generator self", q3, [1, X], [1, X], 3),
        product_case("full cubic order", q3, [1, X, X**2], [1, X, X**2], 3),
        product_case("full quartic order", q4, [1, X, X**2, X**3],
                     [1, X, X**2, X**3], 4),
        product_case("non-ring quadratic lattice", q2, [1, X / 2], [1, X / 2], 2),
    ]
    sqrt2 = mixed.canonical((X**3 - 9 * X) / 2)
    sqrt3 = mixed.canonical((11 * X - X**3) / 2)
    check(mixed.canonical(sqrt2**2) == 2, "mixed field: square of sqrt(2)")
    check(mixed.canonical(sqrt3**2) == 3, "mixed field: square of sqrt(3)")
    products.append(product_case("distinct quadratic mixed", mixed,
                                 [1, sqrt2], [1, sqrt3], 4))

    quadratic_matrix = sp.Matrix([[1, 0, 0, 2], [0, 1, 1, 0]])
    for vector in [sp.Matrix([0, -1, 1, 0]), sp.Matrix([-2, 0, 0, 1])]:
        check(quadratic_matrix * vector == sp.zeros(2, 1),
              "displayed quadratic tensor relation: " + str(list(vector)))
    check(quadratic_matrix.rank() == 2, "displayed quadratic matrix rank")
    cubic_matrix = sp.Matrix([[1, 0, 0, 0], [0, 1, 1, 0], [0, 0, 0, 1]])
    check(cubic_matrix.rank() == 3, "displayed cubic/transcendental matrix rank")

    # Formal independent variables: distinct monomials are independent over QQ.
    y = sp.Symbol("y")
    generic_basis = [1, X, y]
    monomials = [1, X, y, X**2, X * y, y**2]
    generic_matrix = columns_matrix([
        [sp.Poly(sp.expand(a * b), X, y, domain=sp.QQ).coeff_monomial(m)
         for m in monomials] for a in generic_basis for b in generic_basis
    ])
    check(generic_matrix.rank() == 6, "three-generator formal coefficients: product rank")
    check(len(generic_matrix.nullspace()) == 3,
          "three-generator formal coefficients: minimal self-obstruction rank")

    powers: dict[str, list[int]] = {}
    for label, field in [("degree 2", q2), ("degree 3", q3), ("degree 4", q4)]:
        ranks = []
        for s in range(1, 9):
            matrix = columns_matrix([field.coordinates(X**j) for j in range(s + 1)])
            rank = matrix.rank()
            check(rank == min(s + 1, field.degree), f"{label}: ideal-power rank, s={s}")
            ranks.append(rank)
        powers[label] = ranks
    powers["transcendental (formal monomials)"] = list(range(2, 10))

    unit_matrix = sp.Matrix([[1, 2], [1, 1]])
    check(q2.canonical((1 + X) * (X - 1)) == 1, "quadratic arithmetic unit inverse")
    for exponent in range(13):
        unit = q2.canonical((1 + X)**exponent)
        actual = columns_matrix([q2.coordinates(unit), q2.coordinates(unit * X)])
        check(actual == unit_matrix**exponent, f"arithmetic unit matrix power {exponent}")
        check(actual.det() == (-1)**exponent, f"arithmetic unit determinant {exponent}")

    known = [
        ("rational row", [[1, 2]], (1, 1)),
        ("irrational row", [[1, X]], (1, 0)),
        ("mixed free and positive parts", [[1, X, 0]], (2, 1)),
        ("zero matrix", [[0, 0, 0]], (3, 3)),
        ("full rank", [[1, X], [X, 1]], (0, 0)),
        ("field reduction essential", [[X, 2], [1, X]], (1, 0)),
        ("two independent irrational rows", [[1, X, 0, 0], [0, 0, 1, X]], (2, 0)),
    ]
    descents = [descent_case(name, q2, matrix, expected) for name, matrix, expected in known]
    rng = random.Random(20260923)
    random_cases = []
    for index in range(24):
        rows = [[rng.randint(-2, 2) for _ in range(4)] for _ in range(2)]
        result = descent_case(f"rational random {index}", q2, rows)
        check(result["r"] == result["d"], f"rational random {index}: full descent")
        random_cases.append(result)
    for index in range(24):
        rows = [[rng.randint(-2, 2) + rng.randint(-2, 2) * X
                 for _ in range(4)] for _ in range(2)]
        random_cases.append(descent_case(f"quadratic random {index}", q2, rows))

    # Determinant-one/-one change-of-basis identities in a formal parameter.
    mobius = []
    for index in range(16):
        u = sp.eye(2)
        for _ in range(4):
            t = rng.randint(-3, 3)
            u = u * sp.Matrix([[1, t], [0, 1]]) * sp.Matrix([[0, 1], [1, 0]])
        if index % 2:
            u = u * sp.diag(-1, 1)
        a, b, c, d = u[0, 0], u[0, 1], u[1, 0], u[1, 1]
        scalar = 1 / (c * X + d)
        beta = (a * X + b) / (c * X + d)
        check(u.det() in (1, -1), f"Mobius {index}: unimodular matrix")
        check(sp.cancel(scalar * (c * X + d) - 1) == 0,
              f"Mobius {index}: first basis identity")
        check(sp.cancel(scalar * (a * X + b) - beta) == 0,
              f"Mobius {index}: second basis identity")
        mobius.append(serialize_matrix(u))

    report = {
        "status": "all exact finite checks passed",
        "scope": "Finite coefficient arithmetic only. Not a Lean proof, surreal implementation, or transfinite verification.",
        "python_version": platform.python_version(),
        "sympy_version": sp.__version__,
        "random_seed": 20260923,
        "checks_passed": len(CHECKS),
        "product_cases": products,
        "generic_three_generator_product_matrix": serialize_matrix(generic_matrix),
        "ideal_power_generator_ranks_for_s_1_to_8": powers,
        "known_descent_cases": descents,
        "random_descent_cases": random_cases,
        "mobius_matrices": mobius,
        "check_labels": CHECKS,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: {len(CHECKS)} exact finite checks")
    print(f"Output: {args.output}")
    print("Scope: coefficient arithmetic only; no formal or transfinite verification.")


if __name__ == "__main__":
    main()
