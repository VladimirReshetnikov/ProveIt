#!/usr/bin/env python3
"""Exact arithmetic for the accompanying Hankel determinant research note.

Python >= 3.10; standard library only. Matrix size is m, not the OEIS index n:
the OEIS index is n = m - 1. An empty determinant is 1.
"""
from __future__ import annotations

from fractions import Fraction
from math import comb, factorial, gcd, prod
from typing import Sequence


def _integer(value: int, name: str, minimum: int = 0) -> None:
    if isinstance(value, bool) or not isinstance(value, int) or value < minimum:
        raise ValueError(f"{name} must be an integer >= {minimum}")


def factor_integer(number: int) -> dict[int, int]:
    """Trial division. Intended for small parameters, not huge determinants."""
    _integer(number, "number", 1)
    result: dict[int, int] = {}
    p = 2
    while p * p <= number:
        while number % p == 0:
            result[p] = result.get(p, 0) + 1
            number //= p
        p = 3 if p == 2 else p + 2
    if number > 1:
        result[number] = 1
    return result


def valuation(number: int, p: int) -> int:
    """Exponent of a prime p in a nonzero integer (p is not primality-tested)."""
    _integer(p, "p", 2)
    if not isinstance(number, int) or number == 0:
        raise ValueError("number must be a nonzero integer")
    number = abs(number)
    result = 0
    while number % p == 0:
        result += 1
        number //= p
    return result


def remove_primes(number: int, base: int) -> int:
    """Largest divisor of number coprime to base; never factors number."""
    _integer(number, "number", 1)
    _integer(base, "base", 1)
    common = gcd(number, base)
    while common > 1:
        number //= common
        common = gcd(number, base)
    return number


def superfactorial_valuation(m: int, p: int) -> int:
    """v_p(product(j!, j=0..m-1)), in O(log_p(m)) arithmetic steps."""
    _integer(m, "m")
    _integer(p, "p", 2)
    result, power = 0, p
    while power < m:
        quotient, remainder = divmod(m, power)
        result += power * quotient * (quotient - 1) // 2 + quotient * remainder
        power *= p
    return result


def numerator_formula(m: int, d: int, b: int = 1) -> int:
    """Reduced numerator, including nonprimitive parameters by scaling."""
    _integer(m, "m")
    _integer(d, "d", 1)
    _integer(b, "b", 1)
    common = gcd(d, b)
    primitive_d = d // common
    result = 1
    for p, e in factor_integer(primitive_d).items():
        exponent = e * m * (m - 1) + 2 * superfactorial_valuation(m, p)
        exponent -= m * valuation(common, p)
        result *= p ** max(0, exponent)
    return result


def hankel_product(m: int, d: int, b: int = 1) -> Fraction:
    """Cauchy product, reduced by Fraction; independent of numerator_formula."""
    _integer(m, "m")
    _integer(d, "d", 1)
    _integer(b, "b", 1)
    numerator = d ** (m * (m - 1)) * prod(factorial(j) ** 2 for j in range(m))
    denominator = prod(b + d * (i + j) for i in range(m) for j in range(m))
    return Fraction(numerator, denominator)


def hankel_sequence(max_m: int, d: int, b: int = 1) -> list[Fraction]:
    """All determinants through max_m, using the exact size-ratio identity."""
    _integer(max_m, "max_m")
    _integer(d, "d", 1)
    _integer(b, "b", 1)
    result = [Fraction(1)]
    for j in range(max_m):
        top = d ** (2 * j) * factorial(j) ** 2
        bottom = (b + 2 * d * j) * prod(b + d * k for k in range(j, 2 * j)) ** 2
        result.append(result[-1] * Fraction(top, bottom))
    return result


def rational_determinant(matrix: Sequence[Sequence[Fraction | int]]) -> Fraction:
    """Direct exact Gaussian elimination, without any Cauchy identities."""
    m = len(matrix)
    if any(len(row) != m for row in matrix):
        raise ValueError("matrix must be square")
    a = [[Fraction(x) for x in row] for row in matrix]
    result = Fraction(1)
    for col in range(m):
        pivot = next((row for row in range(col, m) if a[row][col] != 0), None)
        if pivot is None:
            return Fraction(0)
        if pivot != col:
            a[col], a[pivot] = a[pivot], a[col]
            result = -result
        pivot_value = a[col][col]
        result *= pivot_value
        for row in range(col + 1, m):
            multiplier = a[row][col] / pivot_value
            a[row][col] = Fraction(0)
            for k in range(col + 1, m):
                a[row][k] -= multiplier * a[col][k]
    return result


def hankel_direct(m: int, d: int, b: int = 1) -> Fraction:
    _integer(m, "m")
    _integer(d, "d", 1)
    _integer(b, "b", 1)
    return rational_determinant([
        [Fraction(1, b + d * (i + j)) for j in range(m)] for i in range(m)
    ])


def triangle_count(remainder: int, total: int) -> int:
    """Number of ordered pairs in [0,remainder)^2 with sum total."""
    return max(0, remainder - abs(total - (remainder - 1)))


def residue_tail(modulus: int, remainder: int, residue: int) -> int:
    _integer(modulus, "modulus", 1)
    if not 0 <= remainder < modulus or not 0 <= residue < modulus:
        raise ValueError("remainder and residue must be in [0, modulus)")
    return triangle_count(remainder, residue) + triangle_count(remainder, residue + modulus)


def denominator_valuation(m: int, d: int, b: int, p: int) -> int:
    """Exact v_p of the reduced denominator for gcd(d,b)=1 and prime p."""
    _integer(m, "m")
    _integer(d, "d", 1)
    _integer(b, "b", 1)
    _integer(p, "p", 2)
    if gcd(d, b) != 1:
        raise ValueError("denominator_valuation requires gcd(d,b)=1")
    if d % p == 0 or m == 0:
        return 0
    largest_entry_denominator = b + 2 * d * (m - 1)
    result, power = 0, p
    while power <= largest_entry_denominator:
        quotient, remainder = divmod(m, power)
        residue = (-b * pow(d, -1, power)) % power
        result += power * quotient + residue_tail(power, remainder, residue)
        power *= p
    return result


def hilbert_denominator(m: int) -> int:
    _integer(m, "m")
    return prod((2 * j + 1) * comb(2 * j, j) ** 2 for j in range(m))


def universal_denominator(m: int, d: int) -> int:
    """Gcd of reduced denominators over all positive b coprime to d."""
    return remove_primes(hilbert_denominator(m), d)


def gcd_certificate(m: int, d: int) -> dict[str, int]:
    """Construct two shifts whose denominators have the universal gcd.

    Avoids factoring the (potentially huge) base determinant denominator:
    its primes are found among the small individual entry denominators.
    """
    _integer(m, "m")
    _integer(d, "d", 1)
    first = hankel_product(m, d, 1).denominator
    primes: set[int] = set()
    for s in range(max(0, 2 * m - 1)):
        primes.update(factor_integer(1 + d * s))
    modulus = 1
    for p in sorted(primes):
        if first % p:
            continue
        power = p
        while power <= 2 * m - 1:
            power *= p
        modulus *= power
    if d == 1:
        shift = 1
    else:
        multiplier = ((1 - d) * pow(modulus, -1, d)) % d
        shift = d + modulus * multiplier
    second = hankel_product(m, d, shift).denominator
    return {
        "m": m, "d": d, "b1": 1, "b2": shift,
        "denominator1": first, "denominator2": second,
        "gcd": gcd(first, second), "predicted_gcd": universal_denominator(m, d),
    }


def rational_binomial(value: Fraction, k: int) -> Fraction:
    _integer(k, "k")
    return prod((value - j for j in range(k)), start=Fraction(1)) / factorial(k)


def inverse_formula(m: int, d: int, b: int = 1) -> list[list[Fraction]]:
    """Exact inverse entries in the generalized-binomial factorization."""
    _integer(m, "m")
    _integer(d, "d", 1)
    _integer(b, "b", 1)
    alpha = Fraction(b, d)
    result: list[list[Fraction]] = []
    for i in range(m):
        row = []
        for j in range(m):
            entry = d * (-1) ** (i + j) * (alpha + i + j)
            entry *= rational_binomial(m + alpha + i - 1, m - j - 1)
            entry *= rational_binomial(m + alpha + j - 1, m - i - 1)
            entry *= rational_binomial(alpha + i + j - 1, i)
            entry *= rational_binomial(alpha + i + j - 1, j)
            row.append(entry)
        result.append(row)
    return result


def biarithmetic_product(m: int, a: int, b: int, c: int) -> Fraction:
    _integer(m, "m")
    for value, name in [(a, "a"), (b, "b"), (c, "c")]:
        _integer(value, name, 1)
    top = (a * b) ** (m * (m - 1) // 2) * prod(factorial(j) ** 2 for j in range(m))
    bottom = prod(c + a * i + b * j for i in range(m) for j in range(m))
    return Fraction(top, bottom)


if __name__ == "__main__":
    for p in (2, 3, 5):
        print(f"prime {p}; OEIS n=0..8:")
        print([numerator_formula(n + 1, p) for n in range(9)])
