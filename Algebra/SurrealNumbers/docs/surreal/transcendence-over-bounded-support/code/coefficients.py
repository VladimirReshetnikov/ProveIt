#!/usr/bin/env python3
"""Explicit positive-integer coefficients for the countable coding construction.

This computes coefficients and finite formal prefixes, not infinite Hahn sums.
The enumeration is a surjective finite-table code with a repetition coordinate.
Each prescribed finite pattern occurs at infinitely many indices, which is the
only property needed by the theorem. Python 3.10+; standard library only.
"""
from __future__ import annotations
from math import factorial, isqrt
from typing import Callable, Sequence


def pair(a: int, b: int) -> int:
    """Cantor pairing of nonnegative integers."""
    if not isinstance(a, int) or not isinstance(b, int) or min(a, b) < 0:
        raise ValueError("pair expects two nonnegative integers")
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n: int) -> tuple[int, int]:
    """Exact inverse of Cantor pairing, including arbitrarily large integers."""
    if not isinstance(n, int) or n < 0:
        raise ValueError("index must be a nonnegative integer")
    w = (isqrt(8 * n + 1) - 1) // 2
    b = n - w * (w + 1) // 2
    return w - b, b


def positions(mask: int) -> list[int]:
    if not isinstance(mask, int) or mask < 0:
        raise ValueError("mask must be a nonnegative integer")
    return [j for j in range(mask.bit_length()) if (mask >> j) & 1]


def code_coefficient(member: Callable[[int], bool], index: int) -> int:
    """Return c_A(index), asking only finitely many membership questions.

    `member(j)` specifies membership of j in A. This routine supplies a concrete
    realization of the countable finite-pattern lemma. It is not a decision
    procedure for any algebraicity question.
    """
    packed, _repetition = unpair(index)
    mask, table_code = unpair(packed)
    base_minus_two, digits = unpair(table_code)
    base = base_minus_two + 2
    subset_index = sum(1 << j for j, a in enumerate(positions(mask)) if member(a))
    # If the requested digit is beyond the representation, it is zero. Avoid
    # forming an enormous power when the answer is already determined.
    if digits == 0 or subset_index > digits.bit_length():
        return 1
    return (digits // pow(base, subset_index)) % base + 1


def encode_table(mask: int, table: Sequence[int], repetition: int = 0) -> int:
    """Return an index realizing a specified finite table and repetition."""
    size = 1 << len(positions(mask))
    if len(table) != size or any(not isinstance(q, int) or q < 1 for q in table):
        raise ValueError("table needs 2**popcount(mask) positive-integer entries")
    if not isinstance(repetition, int) or repetition < 0:
        raise ValueError("repetition must be a nonnegative integer")
    base = max(2, max(table))
    digits = sum((q - 1) * pow(base, j) for j, q in enumerate(table))
    table_code = pair(base - 2, digits)
    return pair(pair(mask, table_code), repetition)


def factorial_prefix(member: Callable[[int], bool], terms: int) -> list[tuple[int, int]]:
    """Return (exponent, coefficient) for n=2,...,terms+1 in W_A."""
    if not isinstance(terms, int) or terms < 0:
        raise ValueError("terms must be a nonnegative integer")
    return [(factorial(n), code_coefficient(member, n - 2))
            for n in range(2, terms + 2)]


if __name__ == "__main__":
    print("A = the even nonnegative integers; formal Hahn prefix:")
    print(factorial_prefix(lambda n: n % 2 == 0, 12))
