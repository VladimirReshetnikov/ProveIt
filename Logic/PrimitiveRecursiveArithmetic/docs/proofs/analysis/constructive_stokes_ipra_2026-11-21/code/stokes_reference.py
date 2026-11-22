#!/usr/bin/env python3
"""Exact, standard-library reference computations for constructive cubical Stokes.

This is executable validation, not a formal proof of Stokes or an iPRA derivation.
All arithmetic is Fraction arithmetic; no numerical tolerance is used.
Flux convention: omega = sum_i (-1)^i a_i dx_0 ... omit dx_i ... dx_(k-1).
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
from typing import Callable, Iterable


Point = tuple[Q, ...]
Scalar = Callable[[Point], Q]


def eps(p: int) -> Q:
    if p < 0:
        raise ValueError("precision must be nonnegative")
    return Q(1, 1 << p)


def grid(dimension: int, cells: int) -> Iterable[Point]:
    if dimension < 0 or cells < 1:
        raise ValueError("dimension >= 0 and cells >= 1 required")
    for indices in product(range(cells), repeat=dimension):
        yield tuple(Q(i, cells) for i in indices)


def insert_coordinate(point: Point, axis: int, value: Q) -> Point:
    return point[:axis] + (value,) + point[axis:]


def volume_sum(derivatives: list[Scalar], cells: int) -> Q:
    """V = N^-k sum_(x on left grid) sum_i g_i(x)."""
    k = len(derivatives)
    if k < 1:
        raise ValueError("positive dimension required")
    return sum((g(x) for x in grid(k, cells) for g in derivatives), Q(0)) / cells**k


def boundary_sum(coefficients: list[Scalar], cells: int) -> Q:
    """B = N^-(k-1) sum_i sum_y [a_i(y,1)-a_i(y,0)]."""
    k = len(coefficients)
    if k < 1:
        raise ValueError("positive dimension required")
    total = Q(0)
    for axis, coefficient in enumerate(coefficients):
        for y in grid(k - 1, cells):
            total += coefficient(insert_coordinate(y, axis, Q(1)))
            total -= coefficient(insert_coordinate(y, axis, Q(0)))
    return total / cells ** (k - 1)


def telescope_sum(coefficients: list[Scalar], cells: int) -> Q:
    """T = N^-(k-1) sum_i sum_x [a_i(x+e_i/N)-a_i(x)]."""
    k = len(coefficients)
    if k < 1:
        raise ValueError("positive dimension required")
    h = Q(1, cells)
    total = Q(0)
    for x in grid(k, cells):
        for axis, coefficient in enumerate(coefficients):
            upper = x[:axis] + (x[axis] + h,) + x[axis + 1 :]
            total += coefficient(upper) - coefficient(x)
    return total / cells ** (k - 1)


def bridge_bound(dimension: int, cells: int, t: int, p: int) -> Q:
    """Bound proved in the report from the sampled derivative contract."""
    return dimension * eps(t) + dimension * (2 * cells + 1) * eps(p)


def dyadic_floor(value: Q, p: int) -> Q:
    """A deterministic approximation with absolute error strictly below 2^-p."""
    scale = 1 << p
    return Q((value.numerator * scale) // value.denominator, scale)


def rounded(function: Scalar, p: int) -> Scalar:
    return lambda point: dyadic_floor(function(point), p)


@dataclass(frozen=True)
class Poly:
    """Small multivariate rational polynomial, represented by exact coefficients."""

    dim: int
    terms: tuple[tuple[tuple[int, ...], Q], ...]

    @staticmethod
    def make(dim: int, terms: dict[tuple[int, ...], Q | int]) -> "Poly":
        if any(len(exponents) != dim or min(exponents, default=0) < 0 for exponents in terms):
            raise ValueError("invalid exponent vector")
        return Poly(dim, tuple(sorted((e, Q(c)) for e, c in terms.items() if c)))

    @staticmethod
    def constant(dim: int, value: Q | int) -> "Poly":
        return Poly.make(dim, {(0,) * dim: value})

    @staticmethod
    def variable(dim: int, axis: int) -> "Poly":
        return Poly.make(dim, {tuple(int(i == axis) for i in range(dim)): 1})

    def coerce(self, other: "Poly | Q | int") -> "Poly":
        if not isinstance(other, Poly):
            return Poly.constant(self.dim, other)
        if other.dim != self.dim:
            raise ValueError("dimension mismatch")
        return other

    def __add__(self, other: "Poly | Q | int") -> "Poly":
        other = self.coerce(other)
        result = dict(self.terms)
        for exponents, coefficient in other.terms:
            result[exponents] = result.get(exponents, Q(0)) + coefficient
        return Poly.make(self.dim, result)

    __radd__ = __add__

    def __neg__(self) -> "Poly":
        return Poly.make(self.dim, {e: -c for e, c in self.terms})

    def __sub__(self, other: "Poly | Q | int") -> "Poly":
        return self + -self.coerce(other)

    def __rsub__(self, other: "Poly | Q | int") -> "Poly":
        return self.coerce(other) - self

    def __mul__(self, other: "Poly | Q | int") -> "Poly":
        other = self.coerce(other)
        result: dict[tuple[int, ...], Q] = {}
        for e, c in self.terms:
            for f, d in other.terms:
                exponent = tuple(a + b for a, b in zip(e, f))
                result[exponent] = result.get(exponent, Q(0)) + c * d
        return Poly.make(self.dim, result)

    __rmul__ = __mul__

    def __pow__(self, exponent: int) -> "Poly":
        if exponent < 0:
            raise ValueError("polynomial exponent must be nonnegative")
        result = Poly.constant(self.dim, 1)
        for _ in range(exponent):
            result = result * self
        return result

    def __call__(self, point: Point) -> Q:
        if len(point) != self.dim:
            raise ValueError("point dimension mismatch")
        total = Q(0)
        for exponents, coefficient in self.terms:
            term = coefficient
            for x, power in zip(point, exponents):
                term *= x**power
            total += term
        return total

    def derivative(self, axis: int) -> "Poly":
        result = {}
        for exponents, coefficient in self.terms:
            if exponents[axis]:
                reduced = list(exponents)
                reduced[axis] -= 1
                result[tuple(reduced)] = coefficient * exponents[axis]
        return Poly.make(self.dim, result)

    def compose(self, substitutions: list["Poly"]) -> "Poly":
        if len(substitutions) != self.dim or not substitutions:
            raise ValueError("one substitution per source coordinate required")
        target = substitutions[0].dim
        result = Poly.constant(target, 0)
        for exponents, coefficient in self.terms:
            term = Poly.constant(target, coefficient)
            for substitution, power in zip(substitutions, exponents):
                term = term * substitution**power
            result = result + term
        return result

    def face(self, axis: int, value: int) -> "Poly":
        result: dict[tuple[int, ...], Q] = {}
        for exponents, coefficient in self.terms:
            reduced = exponents[:axis] + exponents[axis + 1 :]
            result[reduced] = result.get(reduced, Q(0)) + coefficient * value ** exponents[axis]
        return Poly.make(self.dim - 1, result)

    def integral_unit_cube(self) -> Q:
        total = Q(0)
        for exponents, coefficient in self.terms:
            term = coefficient
            for power in exponents:
                term /= power + 1
            total += term
        return total

    def coefficient_l1(self) -> Q:
        """On [0,1]^k this bounds the absolute value of the polynomial."""
        return sum((abs(c) for _, c in self.terms), Q(0))

    def lipschitz_l1_bound(self) -> Q:
        """Sum of coefficient bounds for partials, valid for the max norm."""
        return sum((self.derivative(i).coefficient_l1() for i in range(self.dim)), Q(0))

    def as_json(self) -> dict:
        return {"dimension": self.dim, "terms": [{"exponents": list(e), "coefficient": str(c)} for e, c in self.terms]}


def curved_example() -> tuple[list[Poly], list[Poly], dict]:
    """Derive the pullback and curl integrand by exact polynomial arithmetic."""
    x, y, z = (Poly.variable(3, i) for i in range(3))
    u, v = (Poly.variable(2, i) for i in range(2))
    sigma = [u, v, u * v]
    field = [Poly.constant(3, 0), x * z, x**2 * y]
    field_sigma = [component.compose(sigma) for component in field]
    su = [component.derivative(0) for component in sigma]
    sv = [component.derivative(1) for component in sigma]
    P = sum((field_sigma[i] * su[i] for i in range(3)), Poly.constant(2, 0))
    Qcoef = sum((field_sigma[i] * sv[i] for i in range(3)), Poly.constant(2, 0))
    curl = [field[2].derivative(1) - field[1].derivative(2), field[0].derivative(2) - field[2].derivative(0), field[1].derivative(0) - field[0].derivative(1)]
    cross = [su[1] * sv[2] - su[2] * sv[1], su[2] * sv[0] - su[0] * sv[2], su[0] * sv[1] - su[1] * sv[0]]
    curl_flux = sum((curl[i].compose(sigma) * cross[i] for i in range(3)), Poly.constant(2, 0))
    coefficients = [Qcoef, -P]
    derivatives = [a.derivative(i) for i, a in enumerate(coefficients)]
    expected_P = u**2 * v**2
    expected_Q = u**2 * v * (1 + u)
    expected_flux = u * v * (u + 2)
    assert P == expected_P and Qcoef == expected_Q
    assert sum(derivatives, Poly.constant(2, 0)) == curl_flux == expected_flux
    edge_integrals = {
        "bottom_v0_u_increases": P.face(1, 0).integral_unit_cube(),
        "right_u1_v_increases": Qcoef.face(0, 1).integral_unit_cube(),
        "top_v1_u_decreases": -P.face(1, 1).integral_unit_cube(),
        "left_u0_v_decreases": -Qcoef.face(0, 0).integral_unit_cube(),
    }
    assert sum(edge_integrals.values(), Q(0)) == curl_flux.integral_unit_cube() == Q(2, 3)
    metadata = {
        "sigma": [p.as_json() for p in sigma],
        "field": [p.as_json() for p in field],
        "P": P.as_json(), "Q": Qcoef.as_json(),
        "curl_flux": curl_flux.as_json(),
        "edge_integrals": {key: str(value) for key, value in edge_integrals.items()},
        "exact_integral": "2/3",
        "max_norm_lipschitz_bounds": [str(p.lipschitz_l1_bound()) for p in coefficients + derivatives],
    }
    return coefficients, derivatives, metadata


def curved_closed_sums(cells: int) -> tuple[Q, Q, Q]:
    if cells < 1:
        raise ValueError("positive grid size required")
    n = cells
    volume = Q((n - 1) ** 2 * (8 * n - 1), 12 * n**3)
    boundary = Q((n - 1) * (4 * n + 1), 6 * n**2)
    defect = Q((n - 1) * (11 * n - 1), 12 * n**3)
    assert boundary - volume == defect
    return volume, boundary, defect


def polynomial_family(k: int) -> tuple[list[Poly], list[Poly]]:
    """a_i = (-1)^i (i+1)/k x_i^2 product_(j!=i) ((1+x_j)/2).

    The diagonal first-order remainder is at most h^2 on the unit cube.
    Thus tau(t)=t suffices when h<=2^-t.
    """
    variables = [Poly.variable(k, i) for i in range(k)]
    coefficients = []
    for i in range(k):
        a = Q((-1) ** i * (i + 1), k) * variables[i] ** 2
        for j in range(k):
            if j != i:
                a = a * (Q(1, 2) * (1 + variables[j]))
        coefficients.append(a)
    return coefficients, [a.derivative(i) for i, a in enumerate(coefficients)]


Cell = tuple[int | None, ...]


def cubical_boundary(cell: Cell) -> dict[Cell, int]:
    """Boundary with the outward-normal-first sign, preserving free-axis order."""
    result: dict[Cell, int] = {}
    free_axis_number = 0
    for axis, fixed in enumerate(cell):
        if fixed is not None:
            continue
        for side in (0, 1):
            face = cell[:axis] + (side,) + cell[axis + 1 :]
            coefficient = (-1) ** free_axis_number * (1 if side else -1)
            result[face] = result.get(face, 0) + coefficient
        free_axis_number += 1
    return result


def boundary_of_chain(chain: dict[Cell, int]) -> dict[Cell, int]:
    result: dict[Cell, int] = {}
    for cell, coefficient in chain.items():
        for face, incidence in cubical_boundary(cell).items():
            result[face] = result.get(face, 0) + coefficient * incidence
    return result


if __name__ == "__main__":
    a, g, data = curved_example()
    print("Curved example exact integral:", data["exact_integral"])
    for n in (1, 2, 4, 8, 16):
        V, B = volume_sum(g, n), boundary_sum(a, n)
        assert telescope_sum(a, n) == B
        print(f"N={n}: V={V}, B={B}, B-V={B-V}")
