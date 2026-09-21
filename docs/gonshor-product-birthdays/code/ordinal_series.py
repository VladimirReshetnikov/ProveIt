"""Exact finite-support checks for ordinal-index surreal series.

An index alpha denotes the surreal monomial omega**(-alpha), NOT omega**alpha.
Supported ordinal indices are below omega**omega. Coefficients are exact rational
numbers. This is NOT a general surreal implementation and cannot represent an
infinite normal-form support. No floating-point arithmetic is used.

Python 3.10+, standard library only.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import total_ordering
from typing import Mapping


@total_ordering
@dataclass(frozen=True)
class Ordinal:
    """Cantor polynomial below omega**omega; coefficients in ascending order."""
    coefficients: tuple[int, ...] = ()

    def __post_init__(self) -> None:
        values = tuple(self.coefficients)
        if any(type(c) is not int or c < 0 for c in values):
            raise ValueError("Ordinal coefficients must be nonnegative integers")
        while values and values[-1] == 0:
            values = values[:-1]
        object.__setattr__(self, "coefficients", values)

    @staticmethod
    def finite(n: int) -> Ordinal:
        return Ordinal((n,))

    @staticmethod
    def omega_power(n: int, coefficient: int = 1) -> Ordinal:
        if type(n) is not int or n < 0:
            raise ValueError("Only finite nonnegative Cantor exponents are supported")
        return Ordinal((0,) * n + (coefficient,))

    def __bool__(self) -> bool:
        return bool(self.coefficients)

    def __lt__(self, other: object) -> bool:
        if not isinstance(other, Ordinal):
            return NotImplemented
        return (len(self.coefficients), self.coefficients[::-1]) < (
            len(other.coefficients), other.coefficients[::-1]
        )

    def coefficient(self, i: int) -> int:
        return self.coefficients[i] if i < len(self.coefficients) else 0

    @property
    def degree(self) -> int:
        if not self:
            raise ValueError("The zero ordinal has no leading Cantor exponent")
        return len(self.coefficients) - 1

    def ordinary_add(self, other: Ordinal) -> Ordinal:
        """Ordinary ordinal addition; generally noncommutative."""
        if not other:
            return self
        d = other.degree
        result = [self.coefficient(i) for i in range(max(
            len(self.coefficients), len(other.coefficients)
        ))]
        result[:d] = other.coefficients[:d]
        result[d] = self.coefficient(d) + other.coefficient(d)
        return Ordinal(tuple(result))

    def natural_add(self, other: Ordinal) -> Ordinal:
        return Ordinal(tuple(self.coefficient(i) + other.coefficient(i)
                             for i in range(max(len(self.coefficients),
                                                len(other.coefficients)))))

    def natural_multiply(self, other: Ordinal) -> Ordinal:
        """Natural product. Finite Cantor exponents add as ordinary integers."""
        if not self or not other:
            return ZERO
        result = [0] * (self.degree + other.degree + 1)
        for i, a in enumerate(self.coefficients):
            for j, b in enumerate(other.coefficients):
                result[i + j] += a * b
        return Ordinal(tuple(result))

    def omega_left_multiply(self) -> Ordinal:
        """Ordinary omega * self (finite Cantor exponents only)."""
        return Ordinal((0,) + self.coefficients) if self else ZERO

    def interval_to(self, upper: Ordinal) -> Ordinal:
        """Order type of [self, upper), so self + result = upper."""
        if upper < self:
            raise ValueError("The upper endpoint must not be below the lower one")
        if self == upper:
            return ZERO
        d = max(len(self.coefficients), len(upper.coefficients)) - 1
        while self.coefficient(d) == upper.coefficient(d):
            d -= 1
        return Ordinal(upper.coefficients[:d] + (
            upper.coefficient(d) - self.coefficient(d),
        ))

    def as_text(self) -> str:
        terms = []
        for d in range(len(self.coefficients) - 1, -1, -1):
            c = self.coefficients[d]
            if not c:
                continue
            if d == 0:
                terms.append(str(c))
            else:
                term = "omega" if d == 1 else f"omega^{d}"
                terms.append(term if c == 1 else f"{term}*{c}")
        return " + ".join(terms) or "0"


ZERO = Ordinal()
ONE = Ordinal.finite(1)
OMEGA = Ordinal.omega_power(1)
Series = dict[Ordinal, Fraction]


def is_dyadic(c: Fraction) -> bool:
    d = c.denominator
    return d & (d - 1) == 0


def dyadic_birthday(c: Fraction) -> int:
    if not is_dyadic(c):
        raise ValueError("Expected a dyadic rational")
    if not c:
        return 0
    c = abs(c)
    k = c.denominator.bit_length() - 1
    return (c.numerator + c.denominator - 1) // c.denominator + k


def real_birthday(c: Fraction) -> Ordinal:
    return Ordinal.finite(dyadic_birthday(c)) if is_dyadic(c) else OMEGA


def normalize(terms: Mapping[Ordinal, Fraction | int]) -> Series:
    if any(not isinstance(a, Ordinal) for a in terms):
        raise TypeError("Series keys must be Ordinal objects")
    if any(not isinstance(c, (int, Fraction)) for c in terms.values()):
        raise TypeError("Coefficients must be integers or exact Fraction objects")
    return {a: Fraction(c) for a, c in terms.items() if c}


def birthday_endpoint(terms: Mapping[Ordinal, Fraction | int]) -> Ordinal:
    """The article's endpoint formula, specialized to FINITE support."""
    series = normalize(terms)
    if not series:
        return ZERO
    support = sorted(series)
    a = support[-1]
    c = series[a]
    if not is_dyadic(c):
        return a.ordinary_add(ONE).omega_left_multiply()
    correction = int(a == ZERO)
    if len(support) >= 2:
        b = support[-2]
        correction = int(b.ordinary_add(ONE) == a and not is_dyadic(series[b]))
    tail = dyadic_birthday(c) - 1 + correction
    return a.omega_left_multiply().ordinary_add(Ordinal.finite(tail))


def birthday_blocks(terms: Mapping[Ordinal, Fraction | int]) -> Ordinal:
    """Independent reduced-sign-block construction for FINITE support.

    For the all-minus exponent -alpha, delete shared minus positions; at a
    successor term with non-dyadic previous coefficient delete one more minus.
    Every retained minus produces an omega-block. Append the coefficient tail.
    """
    series = normalize(terms)
    result = ZERO
    previous_index = ZERO
    previous_coefficient: Fraction | None = None
    for a in sorted(series):
        c = series[a]
        retained = previous_index.interval_to(a)
        if previous_coefficient is not None and not is_dyadic(previous_coefficient):
            if not retained:
                raise AssertionError("Strictly increasing support must add a minus")
            retained = ONE.interval_to(retained)
        block = ONE.ordinary_add(retained.omega_left_multiply())
        tail = (Ordinal.finite(dyadic_birthday(c) - 1)
                if is_dyadic(c) else OMEGA)
        result = result.ordinary_add(block.ordinary_add(tail))
        previous_index, previous_coefficient = a, c
    return result


def add(left: Mapping[Ordinal, Fraction | int],
        right: Mapping[Ordinal, Fraction | int]) -> Series:
    result = normalize(left)
    for a, c in right.items():
        result[a] = result.get(a, Fraction(0)) + Fraction(c)
    return normalize(result)


def multiply(left: Mapping[Ordinal, Fraction | int],
             right: Mapping[Ordinal, Fraction | int]) -> Series:
    result: Series = {}
    for a, c in normalize(left).items():
        for b, d in normalize(right).items():
            index = a.natural_add(b)
            result[index] = result.get(index, Fraction(0)) + c * d
    return normalize(result)


def is_integer_real(terms: Mapping[Ordinal, Fraction | int]) -> bool:
    series = normalize(terms)
    return not series or (set(series) == {ZERO} and series[ZERO].denominator == 1)


def is_signed_one(terms: Mapping[Ordinal, Fraction | int]) -> bool:
    series = normalize(terms)
    return set(series) == {ZERO} and abs(series[ZERO]) == 1


def predicted_equality(left: Mapping[Ordinal, Fraction | int],
                       right: Mapping[Ordinal, Fraction | int]) -> bool:
    return (not normalize(left) or not normalize(right)
            or is_signed_one(left) or is_signed_one(right)
            or (is_integer_real(left) and is_integer_real(right)))


def support_bound(left: Mapping[Ordinal, Fraction | int],
                  right: Mapping[Ordinal, Fraction | int]) -> Ordinal:
    a, b = normalize(left), normalize(right)
    if not a or not b:
        return ZERO
    return max(a).natural_add(max(b)).ordinary_add(ONE).omega_left_multiply()


def dyadic_signs(c: Fraction) -> tuple[int, ...]:
    """Canonical finite sign string by dyadic bisection, for a separate check."""
    if not is_dyadic(c):
        raise ValueError("A finite sign string requires a dyadic rational")
    value, step = Fraction(0), Fraction(1)
    previous, fractional = 0, False
    result: list[int] = []
    while value != c:
        sign = 1 if c > value else -1
        if fractional or (previous and sign != previous):
            step /= 2
            fractional = True
        value += sign * step
        result.append(sign)
        previous = sign
        if len(result) > 100_000:
            raise ValueError("Sign-string safety limit exceeded")
    return tuple(result)


def predecessor(a: Ordinal) -> Ordinal | None:
    """Immediate ordinal predecessor, or None at zero and limit ordinals."""
    if not a or a.coefficient(0) == 0:
        return None
    return Ordinal((a.coefficient(0) - 1,) + a.coefficients[1:])


def birthday_product_fast(left: Mapping[Ordinal, Fraction | int],
                          right: Mapping[Ordinal, Fraction | int]) -> Ordinal:
    """Finite-support product birthday without constructing its convolution.

    Apart from locating maxima, only the leading and predecessor coefficients
    of each factor are used. The theorem here does NOT handle infinite supports.
    """
    x, y = normalize(left), normalize(right)
    if not x or not y:
        return ZERO
    a, b = max(x), max(y)
    gamma = a.natural_add(b)
    p = x[a] * y[b]
    if not is_dyadic(p):
        return gamma.ordinary_add(ONE).omega_left_multiply()
    correction = int(not gamma)
    if predecessor(gamma) is not None:
        ap, bp = predecessor(a), predecessor(b)
        q = ((x.get(ap, Fraction(0)) * y[b] if ap is not None else Fraction(0))
             + (x[a] * y.get(bp, Fraction(0)) if bp is not None else Fraction(0)))
        correction = int(not is_dyadic(q))
    return gamma.omega_left_multiply().ordinary_add(
        Ordinal.finite(dyadic_birthday(p) - 1 + correction))
