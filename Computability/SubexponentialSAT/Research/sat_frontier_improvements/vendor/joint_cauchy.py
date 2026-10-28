#!/usr/bin/env python3
"""Exact joint Cauchy modes for the ETH contraction packet.

This is a local algebraic prototype, not an end-to-end SAT solver.
Only Python's standard library is required. Arithmetic is exact over Q or
Q[U]/(U^2+U+1); no floating-point calculation is used.

For R=2^i and s_j=(j mod R)+2R floor(j/R), the Cauchy identity is

  C(T)/(C'(0)(T+s_j-s_k)) = sum_b target_b(j) source_b(k).

Both normalized row and source factors are integral at 2. The target has
valuation at least a+1-i+2*(q+v_2(q!)), q=floor(b/R). All divisions by powers
of two in their construction are exact, explicit valuation cancellations.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import inf
from typing import Union


def rational_v2(value: Fraction | int) -> int | float:
    value = Fraction(value)
    if value == 0:
        return inf
    numerator = abs(value.numerator)
    denominator = value.denominator
    return ((numerator & -numerator).bit_length() - 1
            - ((denominator & -denominator).bit_length() - 1))


@dataclass(frozen=True)
class Quadratic:
    """a+b*U with U^2+U+1=0; reduction modulo 2 is the field F_4."""

    a: Fraction = Fraction(0)
    b: Fraction = Fraction(0)

    def __post_init__(self) -> None:
        object.__setattr__(self, "a", Fraction(self.a))
        object.__setattr__(self, "b", Fraction(self.b))

    @staticmethod
    def coerce(other: Scalar) -> Quadratic:
        return other if isinstance(other, Quadratic) else Quadratic(Fraction(other))

    def __add__(self, other: Scalar) -> Quadratic:
        other = self.coerce(other)
        return Quadratic(self.a + other.a, self.b + other.b)

    __radd__ = __add__

    def __neg__(self) -> Quadratic:
        return Quadratic(-self.a, -self.b)

    def __sub__(self, other: Scalar) -> Quadratic:
        return self + -self.coerce(other)

    def __rsub__(self, other: Scalar) -> Quadratic:
        return self.coerce(other) + -self

    def __mul__(self, other: Scalar) -> Quadratic:
        other = self.coerce(other)
        return Quadratic(self.a * other.a - self.b * other.b,
                         self.a * other.b + self.b * other.a - self.b * other.b)

    __rmul__ = __mul__

    def inverse(self) -> Quadratic:
        norm = self.a * self.a - self.a * self.b + self.b * self.b
        if norm == 0:
            raise ZeroDivisionError("zero element of the quadratic field")
        return Quadratic((self.a - self.b) / norm, -self.b / norm)

    def __truediv__(self, other: Scalar) -> Quadratic:
        return self * self.coerce(other).inverse()

    def __rtruediv__(self, other: Scalar) -> Quadratic:
        return self.coerce(other) * self.inverse()

    def __pow__(self, exponent: int) -> Quadratic:
        if exponent < 0:
            return self.inverse() ** (-exponent)
        result, base = Quadratic(1), self
        while exponent:
            if exponent & 1:
                result = result * base
            base = base * base
            exponent //= 2
        return result

    def __bool__(self) -> bool:
        return bool(self.a or self.b)

    def __eq__(self, other: object) -> bool:
        if isinstance(other, (int, Fraction)):
            return self.b == 0 and self.a == other
        if isinstance(other, Quadratic):
            return self.a == other.a and self.b == other.b
        return NotImplemented


Scalar = Union[int, Fraction, Quadratic]


def v2(value: Scalar) -> int | float:
    if isinstance(value, Quadratic):
        return min(rational_v2(value.a), rational_v2(value.b))
    return rational_v2(value)


def exact_divide(numerator: Scalar, denominator: Scalar) -> Scalar:
    if isinstance(numerator, Quadratic) or isinstance(denominator, Quadratic):
        return Quadratic.coerce(numerator) / denominator
    return Fraction(numerator) / Fraction(denominator)


def power_of_two(exponent: int) -> Fraction:
    return Fraction(1 << exponent) if exponent >= 0 else Fraction(1, 1 << -exponent)


def factored_ratio(numerator: Scalar, denominator: Scalar) -> tuple[int, Scalar]:
    """Return (v,unit) with numerator/denominator=2^v*unit, v>=0.

    The numerator must be nonzero. Denominator powers of two are removed
    before inversion. For integral inputs every inversion is of a 2-adic unit.
    """
    nv, dv = v2(numerator), v2(denominator)
    if nv == inf or dv == inf:
        raise ValueError("factored_ratio requires nonzero arguments")
    nv, dv = int(nv), int(dv)
    if nv < dv:
        raise ValueError("ratio is not 2-integral")
    numerator_unit = exact_divide(numerator, power_of_two(nv))
    denominator_unit = exact_divide(denominator, power_of_two(dv))
    unit = exact_divide(numerator_unit, denominator_unit)
    if v2(unit) != 0:
        raise ArithmeticError("unit normalization failed")
    return nv - dv, unit


def residue(value: Scalar, precision: int) -> tuple[int, int]:
    """Reduce an integral scalar to (a,b) modulo 2^precision in F_4's lift."""
    if precision < 1:
        raise ValueError("precision must be positive")
    modulus = 1 << precision
    value = Quadratic.coerce(value)
    result = []
    for coordinate in (value.a, value.b):
        if coordinate.denominator % 2 == 0:
            raise ValueError("coordinate has a nonintegral 2-adic denominator")
        result.append(coordinate.numerator * pow(coordinate.denominator, -1, modulus)
                      % modulus)
    return result[0], result[1]


def residue_add(x: tuple[int, int], y: tuple[int, int], modulus: int) -> tuple[int, int]:
    return ((x[0] + y[0]) % modulus, (x[1] + y[1]) % modulus)


def residue_multiply(x: tuple[int, int], y: tuple[int, int], modulus: int) -> tuple[int, int]:
    a, b = x
    c, d = y
    return ((a * c - b * d) % modulus, (a * d + b * c - b * d) % modulus)


@dataclass(frozen=True)
class JointCauchyKernel:
    """One full crossing orientation of a padded packet.

    The other orientation adds R to every row and column slot, so has the
    identical difference kernel. Source and target groups remain distinct.
    """

    a: int
    i: int
    t: int
    zeta: Scalar = Fraction(1)

    def __post_init__(self) -> None:
        if self.a < 1 or not (0 <= self.i < self.a):
            raise ValueError("require a>=1 and 0<=i<a")
        if not (-self.L <= self.t < self.L) or v2(self.t) != self.i:
            raise ValueError("t must be a nonzero grid point of valuation i")
        if v2(self.zeta) < 0:
            raise ValueError("zeta must be integral at 2")
        if not isinstance(self.zeta, Quadratic):
            object.__setattr__(self, "zeta", Fraction(self.zeta))

    @property
    def L(self) -> int:
        return 1 << self.a

    @property
    def R(self) -> int:
        return 1 << self.i

    @property
    def size(self) -> int:
        return self.L // 2

    @property
    def T(self) -> Scalar:
        return self.t + (1 << (self.a + 1)) * self.zeta

    def slot(self, index: int, orientation: int = 0) -> int:
        if not 0 <= index < self.size or orientation not in (0, 1):
            raise ValueError("invalid packet slot or orientation")
        return index % self.R + 2 * self.R * (index // self.R) + orientation * self.R

    def E(self, mode: int) -> int:
        if not 0 <= mode < self.size:
            raise ValueError("invalid mode")
        q = mode // self.R
        return 2 * q - q.bit_count()  # q+v_2(q!)

    def weight(self, mode: int) -> int:
        return self.a + 1 - self.i + 2 * self.E(mode)

    def prefactor(self) -> Scalar:
        """C(T)/(C'(0)T), with exact 2-adic cancellation in Q or Q(U)."""
        value: Scalar = Fraction(1)
        denominator = 1
        for q in range(-self.L, self.L):
            value = value * (self.T - q)
            if q:
                denominator *= -q
        return exact_divide(value, denominator * self.T)

    def normalized_factor(self, mode: int, index: int, side: str) -> Scalar:
        """Return f_b(s_j)/2^E or g_b(s_j)/2^E using only unit inversions."""
        if side not in ("row", "source"):
            raise ValueError("side must be row or source")
        self.E(mode)
        x = self.slot(index)
        if index < mode:
            return Fraction(0)
        pivot = self.slot(mode)
        denominator = self.T + x - pivot if side == "row" else self.T + pivot - x
        valuation, unit = factored_ratio(self.T, denominator)
        for h in range(mode):
            node = self.slot(h)
            difference = x - node if side == "row" else node - x
            factor_valuation, factor_unit = factored_ratio(difference, self.T + difference)
            valuation += factor_valuation
            unit = unit * factor_unit
        valuation -= self.E(mode)
        if valuation < 0:
            raise ArithmeticError("proved factorial divisibility failed")
        return power_of_two(valuation) * unit

    def row_factor(self, mode: int, index: int) -> Scalar:
        return self.normalized_factor(mode, index, "row")

    def source_factor(self, mode: int, index: int) -> Scalar:
        return self.normalized_factor(mode, index, "source")

    def target_factor(self, mode: int, index: int) -> Scalar:
        return self.prefactor() * power_of_two(2 * self.E(mode)) * self.row_factor(mode, index)

    def entry(self, row: int, column: int) -> Scalar:
        return exact_divide(self.prefactor() * self.T,
                            self.T + self.slot(row) - self.slot(column))

    def feature_tables(self) -> tuple[tuple[tuple[Scalar, ...], ...],
                                      tuple[tuple[Scalar, ...], ...]]:
        """Immutable [mode][row/column] tables with all valuations paid."""
        prefactor = self.prefactor()
        target = tuple(tuple(prefactor * power_of_two(2 * self.E(b)) * self.row_factor(b, j)
                             for j in range(self.size)) for b in range(self.size))
        source = tuple(tuple(self.source_factor(b, j) for j in range(self.size))
                       for b in range(self.size))
        return target, source

    def reconstruct(self, row: int, column: int) -> Scalar:
        target, source = self.feature_tables()
        return sum((target[b][row] * source[b][column] for b in range(self.size)), Fraction(0))

