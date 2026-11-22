#!/usr/bin/env python3
"""Exact-rational reference implementation for the quantitative iPRA IFT.

This is executable evidence, not an iPRA or Lean proof. The callable evaluator
is a fixed program supplied by the caller; no universal PR evaluator is used.
Every solve uses its predetermined finite iteration count.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from typing import Callable, Sequence

Vector = tuple[Q, ...]
Matrix = tuple[Vector, ...]
Evaluator = Callable[[Vector, Vector], Vector]
Jacobian = Callable[[Vector, Vector], tuple[Matrix, Matrix]]


def vector(values: Sequence[int | Q]) -> Vector:
    return tuple(Q(value) for value in values)


def add(left: Vector, right: Vector) -> Vector:
    if len(left) != len(right):
        raise ValueError("Vector dimensions differ")
    return tuple(a + b for a, b in zip(left, right))


def sub(left: Vector, right: Vector) -> Vector:
    if len(left) != len(right):
        raise ValueError("Vector dimensions differ")
    return tuple(a - b for a, b in zip(left, right))


def sup(values: Vector) -> Q:
    return max((abs(value) for value in values), default=Q(0))


def distance(left: Vector, right: Vector) -> Q:
    return sup(sub(left, right))


def dyadic(precision: int) -> Q:
    if precision < 0:
        raise ValueError("Precision must be nonnegative")
    return Q(1, 1 << precision)


def floor_dyadic(value: Q, precision: int) -> Q:
    """Floor, including for negative values, to a dyadic grid."""
    scale = 1 << precision
    return Q((value.numerator * scale) // value.denominator, scale)


def clip_box(values: Vector, center: Vector, radius: Q) -> Vector:
    if len(values) != len(center) or radius <= 0:
        raise ValueError("Invalid box")
    return tuple(min(max(value, c - radius), c + radius)
                 for value, c in zip(values, center))


def clock_shift(radius: Q) -> int:
    """Least s >= 0 with 2*r <= 2**s, using an explicit finite search.

    If 2*r = a/b with positive integers a,b, then 2**a >= a >= a/b.
    Consequently range(a + 1) contains a successful candidate.
    """
    if radius <= 0:
        raise ValueError("Radius must be positive")
    target = 2 * radius
    for shift in range(target.numerator + 1):
        if target <= (1 << shift):
            return shift
    raise AssertionError("The proved finite clock bound failed")


@dataclass(frozen=True)
class Problem:
    name: str
    parameter_center: Vector
    root_center: Vector
    parameter_radius: Q
    root_radius: Q
    parameter_gain: Q
    exact: Evaluator
    jacobian: Jacobian
    actual_contraction_bound: Q
    taylor_quadratic_bound: Q

    def in_parameter_box(self, x: Vector) -> bool:
        return (len(x) == len(self.parameter_center)
                and distance(x, self.parameter_center) <= self.parameter_radius)

    def in_root_box(self, y: Vector) -> bool:
        return (len(y) == len(self.root_center)
                and distance(y, self.root_center) <= self.root_radius)


@dataclass(frozen=True)
class Trace:
    problem_name: str
    parameter: Vector
    demand: int
    precision: int
    shift: int
    epsilon: Q
    oracle_mode: str
    states: tuple[Vector, ...]

    @property
    def iterations(self) -> int:
        return len(self.states) - 1

    @property
    def result(self) -> Vector:
        return self.states[-1]


def oracle(problem: Problem, x: Vector, y: Vector,
           precision: int, mode: str) -> Vector:
    """Deterministic error-bounded oracles for validation.

    All four modes are fixed rational programs. Inexact modes exercise the full
    allowed evaluator error, including error signs depending on the current
    rational input. None examines an unknown exact solution.
    """
    exact = problem.exact(x, y)
    unit = dyadic(precision)
    if mode == "exact":
        return exact
    if mode == "plus":
        return tuple(value + unit for value in exact)
    if mode == "minus":
        return tuple(value - unit for value in exact)
    if mode == "signed":
        parity_seed = precision + sum(value.numerator + value.denominator
                                      for value in x + y)
        return tuple(value + (unit if (parity_seed + i) % 2 else -unit)
                     for i, value in enumerate(exact))
    raise ValueError(f"Unknown oracle mode: {mode}")


def solve(problem: Problem, x: Vector, demand: int,
          oracle_mode: str = "exact") -> Trace:
    """Return the predetermined clipped, rounded iteration trace.

    p = k+5, epsilon = 2**(-(k+4)), N = k+s+4, 2*r <= 2**s.
    This routine does not stop on a small observed residual.
    """
    if demand < 0 or not problem.in_parameter_box(x):
        raise ValueError("Invalid demand or parameter outside certified box")
    shift = clock_shift(problem.root_radius)
    precision = demand + 5
    count = demand + shift + 4
    states = [problem.root_center]
    for _ in range(count):
        y = states[-1]
        value = oracle(problem, x, y, precision, oracle_mode)
        rounded = tuple(floor_dyadic(v, precision) for v in sub(y, value))
        states.append(clip_box(rounded, problem.root_center, problem.root_radius))
    return Trace(problem.name, x, demand, precision, shift,
                 dyadic(demand + 4), oracle_mode, tuple(states))


def identity(size: int) -> Matrix:
    return tuple(tuple(Q(int(i == j)) for j in range(size)) for i in range(size))


def matrix_zero(rows: int, columns: int) -> Matrix:
    return tuple(tuple(Q(0) for _ in range(columns)) for _ in range(rows))


def matrix_add(left: Matrix, right: Matrix) -> Matrix:
    if len(left) != len(right):
        raise ValueError("Matrix dimensions differ")
    return tuple(add(a, b) for a, b in zip(left, right))


def matrix_sub(left: Matrix, right: Matrix) -> Matrix:
    if len(left) != len(right):
        raise ValueError("Matrix dimensions differ")
    return tuple(sub(a, b) for a, b in zip(left, right))


def matrix_neg(matrix: Matrix) -> Matrix:
    return tuple(tuple(-value for value in row) for row in matrix)


def matrix_mul(left: Matrix, right: Matrix) -> Matrix:
    rows = len(left)
    inner = len(right)
    columns = len(right[0]) if right else 0
    if any(len(row) != inner for row in left):
        raise ValueError("Incompatible matrix product")
    if any(len(row) != columns for row in right):
        raise ValueError("Ragged right matrix")
    return tuple(tuple(sum((left[i][k] * right[k][j] for k in range(inner)), Q(0))
                       for j in range(columns)) for i in range(rows))


def matrix_apply(matrix: Matrix, value: Vector) -> Vector:
    if any(len(row) != len(value) for row in matrix):
        raise ValueError("Incompatible matrix-vector product")
    return tuple(sum((a * b for a, b in zip(row, value)), Q(0)) for row in matrix)


def matrix_norm(matrix: Matrix) -> Q:
    return max((sum((abs(value) for value in row), Q(0)) for row in matrix),
               default=Q(0))


def neumann(matrix: Matrix, terms: int) -> tuple[Matrix, Matrix]:
    """Return sum_(j<terms) matrix**j and matrix**terms by finite loops."""
    size = len(matrix)
    if terms < 0 or any(len(row) != size for row in matrix):
        raise ValueError("Expected a square matrix and a nonnegative cutoff")
    total = matrix_zero(size, size)
    power = identity(size)
    for _ in range(terms):
        total = matrix_add(total, power)
        power = matrix_mul(power, matrix)
    return total, power


def rational_inverse(matrix: Matrix) -> Matrix:
    """Finite rational Gaussian elimination; used only as an independent check.

    Pivot selection scans a bounded finite list. This is not the algorithm
    used to construct an inverse of a represented real matrix in the paper.
    """
    size = len(matrix)
    if any(len(row) != size for row in matrix):
        raise ValueError("Expected a square matrix")
    unit = identity(size)
    rows = [list(matrix[i] + unit[i]) for i in range(size)]
    for column in range(size):
        candidates = [row for row in range(column, size) if rows[row][column] != 0]
        if not candidates:
            raise ValueError("Matrix is singular")
        pivot = candidates[0]
        rows[column], rows[pivot] = rows[pivot], rows[column]
        divisor = rows[column][column]
        rows[column] = [value / divisor for value in rows[column]]
        for row in range(size):
            if row != column:
                factor = rows[row][column]
                rows[row] = [v - factor * p for v, p in zip(rows[row], rows[column])]
    return tuple(tuple(row[size:]) for row in rows)


def circle_value(x: Vector, y: Vector) -> Vector:
    return ((x[0] * x[0] + y[0] * y[0] - 1) / 2,)


def circle_jacobian(x: Vector, y: Vector) -> tuple[Matrix, Matrix]:
    return (((x[0],),), ((y[0],),))


def system_value(x: Vector, y: Vector) -> Vector:
    return (y[0] + y[0] * y[1] / 4 - x[0],
            y[1] + y[0] * y[0] / 4 - x[0] / 2)


def system_jacobian(x: Vector, y: Vector) -> tuple[Matrix, Matrix]:
    del x
    return (((Q(-1),), (Q(-1, 2),)),
            ((1 + y[1] / 4, y[0] / 4), (y[0] / 2, Q(1))))


CIRCLE = Problem("circle", vector([0]), vector([1]), Q(1, 4), Q(1, 4),
                 Q(1, 4), circle_value, circle_jacobian, Q(1, 4), Q(1))
SYSTEM = Problem("coupled_polynomial", vector([0]), vector([0, 0]), Q(1, 16),
                 Q(1, 4), Q(1), system_value, system_jacobian, Q(1, 8), Q(1, 4))


def example_problems() -> tuple[Problem, ...]:
    return CIRCLE, SYSTEM
