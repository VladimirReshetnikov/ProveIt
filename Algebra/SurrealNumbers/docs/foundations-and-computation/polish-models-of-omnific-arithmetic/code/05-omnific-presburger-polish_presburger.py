"""Exact arithmetic and Baire-space codes for a Polish Presburger model.

Mathematical carrier: ((Q^N)_lex x Z)_{>=0}. A Baire code is a function
N -> N. Every code is valid; the conversion is a homeomorphism.
This is executable supporting material, NOT a formal proof of the article.
Only the Python standard library is required (Python 3.10 or later).
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from math import isqrt
from typing import Callable

Code = Callable[[int], int]
Coefficients = Callable[[int], Fraction]


def _natural(n: int) -> int:
    if not isinstance(n, int) or isinstance(n, bool) or n < 0:
        raise ValueError(f"Expected a nonnegative integer, got {n!r}")
    return n


def pair(a: int, b: int) -> int:
    """Cantor's computable pairing bijection N^2 -> N."""
    a, b = _natural(a), _natural(b)
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n: int) -> tuple[int, int]:
    n = _natural(n)
    w = (isqrt(8 * n + 1) - 1) // 2
    b = n - w * (w + 1) // 2
    return w - b, b


def positive_rational(n: int) -> Fraction:
    """Calkin--Wilf enumeration, indexed from 0: 1, 1/2, 2, ... ."""
    n = _natural(n)
    a = b = 1
    for bit in bin(n + 1)[3:]:
        if bit == "0":
            b += a
        else:
            a += b
    return Fraction(a, b)


def positive_index(q: Fraction) -> int:
    """Inverse enumeration, using quotient-accelerated Euclidean steps."""
    q = Fraction(q)
    if q <= 0:
        raise ValueError("Expected a positive rational")
    a, b = q.numerator, q.denominator
    runs: list[tuple[int, int]] = []
    while a != b:
        if a < b:
            count = (b - 1) // a
            runs.append((0, count))
            b -= count * a
        else:
            count = (a - 1) // b
            runs.append((1, count))
            a -= count * b
    n = 1
    for bit, count in reversed(runs):
        n <<= count
        if bit:
            n |= (1 << count) - 1
    return n - 1


def rational(n: int) -> Fraction:
    n = _natural(n)
    if n == 0:
        return Fraction(0)
    return positive_rational((n - 1) // 2) * (1 if n % 2 else -1)


def rational_index(q: Fraction) -> int:
    q = Fraction(q)
    if not q:
        return 0
    return 2 * positive_index(abs(q)) + (1 if q > 0 else 2)


def nonnegative_rational(n: int) -> Fraction:
    n = _natural(n)
    return Fraction(0) if n == 0 else positive_rational(n - 1)


def nonnegative_index(q: Fraction) -> int:
    q = Fraction(q)
    if q < 0:
        raise ValueError("Expected a nonnegative rational")
    return 0 if q == 0 else positive_index(q) + 1


def memo_code(code: Code) -> Code:
    """Check that every requested oracle output is a natural number."""
    @lru_cache(maxsize=None)
    def result(i: int) -> int:
        return _natural(code(_natural(i)))
    return result


def decode(code: Code) -> tuple[int, Coefficients]:
    """Decode a total Baire code to its integer and rational coordinates.

    Even tag 2*z (z >= 0): the tail is a branching-tree code for the
    nonnegative lexicographic cone. Odd tag encodes (a,k,b), meaning
    z=-a-1, first positive coordinate k with value positive_rational(b).
    """
    code = memo_code(code)
    tag = code(0)
    if tag % 2 == 0:
        integer = tag // 2
        values: list[Fraction] = []
        seen_positive = False

        def coefficient(i: int) -> Fraction:
            nonlocal seen_positive
            i = _natural(i)
            while len(values) <= i:
                digit = code(len(values) + 1)
                value = (rational(digit) if seen_positive
                         else nonnegative_rational(digit))
                values.append(value)
                if value != 0:
                    seen_positive = True
            return values[i]
        return integer, coefficient

    a, packed = unpair((tag - 1) // 2)
    k, b = unpair(packed)
    integer = -a - 1

    @lru_cache(maxsize=None)
    def coefficient(i: int) -> Fraction:
        i = _natural(i)
        if i < k:
            return Fraction(0)
        if i == k:
            return positive_rational(b)
        return rational(code(i - k))
    return integer, coefficient


def encode(integer: int, coefficients: Coefficients) -> Code:
    """Encode a VALID model element; for negative integer coordinate its
    rational sequence must be strictly lex-positive. For nonnegative
    integer coordinate it must be lex-nonnegative.

    A violated positive-cone promise can raise ValueError; searching for
    a first nonzero coordinate cannot terminate on the invalid input
    consisting of a zero sequence and a negative integer coordinate.
    The public operations below always satisfy this promise.
    """
    if not isinstance(integer, int) or isinstance(integer, bool):
        raise ValueError("The integer coordinate must be an integer")
    coefficients = lru_cache(maxsize=None)(coefficients)
    if integer >= 0:
        digits: list[int] = []
        seen_positive = False

        @lru_cache(maxsize=None)
        def result(i: int) -> int:
            nonlocal seen_positive
            i = _natural(i)
            if i == 0:
                return 2 * integer
            while len(digits) < i:
                value = Fraction(coefficients(len(digits)))
                digit = (rational_index(value) if seen_positive
                         else nonnegative_index(value))
                digits.append(digit)
                if value != 0:
                    seen_positive = True
            return digits[i - 1]
        return result

    k = 0
    while coefficients(k) == 0:
        k += 1
    first = Fraction(coefficients(k))
    if first < 0:
        raise ValueError("Invalid element: negative leading coefficient")
    tag = 2 * pair(-integer - 1, pair(k, positive_index(first))) + 1

    @lru_cache(maxsize=None)
    def result(i: int) -> int:
        i = _natural(i)
        if i == 0:
            return tag
        return rational_index(Fraction(coefficients(k + i)))
    return result


def add_codes(left: Code, right: Code) -> Code:
    """A total Type-2 algorithm for addition on Baire space."""
    n, a = decode(left)
    m, b = decode(right)
    return encode(n + m, lambda i: a(i) + b(i))


def quotient_code(code: Code, modulus: int) -> tuple[Code, int]:
    """Continuous Euclidean quotient and standard remainder."""
    if not isinstance(modulus, int) or isinstance(modulus, bool) or modulus < 1:
        raise ValueError("The modulus must be a positive integer")
    n, a = decode(code)
    q, r = divmod(n, modulus)
    return encode(q, lambda i: a(i) / modulus), r


def numeral(n: int) -> Code:
    n = _natural(n)
    return lambda i: 2 * n if _natural(i) == 0 else 0


def compare_approx(left: Code, right: Code, stage: int) -> int:
    """Limit approximation to comparison (-1, 0, +1).

    For fixed inputs the output changes at most once as stage increases.
    There is no uniform stopping test for the comparison of arbitrary
    infinite streams; this deliberately does NOT claim one.
    """
    stage = _natural(stage)
    n, a = decode(left)
    m, b = decode(right)
    for i in range(stage):
        difference = a(i) - b(i)
        if difference:
            return 1 if difference > 0 else -1
    return (n > m) - (n < m)


@dataclass(frozen=True)
class FiniteLex:
    """An exact finite-rank rational test element (NOT all of Q^N)."""
    coefficients: tuple[Fraction, ...]
    integer: int

    def __post_init__(self) -> None:
        object.__setattr__(self, "coefficients",
                           tuple(Fraction(x) for x in self.coefficients))
        if not isinstance(self.integer, int) or isinstance(self.integer, bool):
            raise ValueError("The constant coordinate must be an integer")

    def _same_rank(self, other: FiniteLex) -> None:
        if len(self.coefficients) != len(other.coefficients):
            raise ValueError("Ranks must agree")

    def __add__(self, other: FiniteLex) -> FiniteLex:
        self._same_rank(other)
        return FiniteLex(tuple(a + b for a, b in
                               zip(self.coefficients, other.coefficients)),
                         self.integer + other.integer)

    def __neg__(self) -> FiniteLex:
        return FiniteLex(tuple(-a for a in self.coefficients), -self.integer)

    def __sub__(self, other: FiniteLex) -> FiniteLex:
        return self + (-other)

    def scale(self, n: int) -> FiniteLex:
        if not isinstance(n, int) or isinstance(n, bool):
            raise ValueError("Scalar must be an integer")
        return FiniteLex(tuple(n * a for a in self.coefficients), n * self.integer)

    def compare(self, other: FiniteLex) -> int:
        self._same_rank(other)
        a = self.coefficients + (Fraction(self.integer),)
        b = other.coefficients + (Fraction(other.integer),)
        return (a > b) - (a < b)

    def positive(self) -> bool:
        return self.compare(FiniteLex((Fraction(0),) * len(self.coefficients), 0)) > 0

    def nonnegative(self) -> bool:
        return self.compare(FiniteLex((Fraction(0),) * len(self.coefficients), 0)) >= 0

    def divmod(self, modulus: int) -> tuple[FiniteLex, int]:
        if not isinstance(modulus, int) or isinstance(modulus, bool) or modulus < 1:
            raise ValueError("Modulus must be a positive integer")
        q, r = divmod(self.integer, modulus)
        return FiniteLex(tuple(a / modulus for a in self.coefficients), q), r

    @classmethod
    def constant(cls, rank: int, n: int) -> FiniteLex:
        return cls((Fraction(0),) * _natural(rank), n)
