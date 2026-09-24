"""Finite arithmetic used in coarse_jump_spectra.tex.

These routines do not compute a Turing jump, decide an unbounded search,
or certify a claim about infinite Turing degrees. All callbacks supplied to
these finite routines must terminate on the requested inputs.
"""
from __future__ import annotations

from collections.abc import Callable, Sequence
from fractions import Fraction

BitOracle = Callable[[int], int]
Approximation = Callable[[int, int], int]


def _natural(n: int, name: str) -> None:
    if not isinstance(n, int) or isinstance(n, bool) or n < 0:
        raise ValueError(f"{name} must be a nonnegative integer")


def _bit(value: int) -> int:
    if value not in (0, 1):
        raise ValueError(f"expected a bit, received {value!r}")
    return int(value)


def column(n: int) -> int:
    """The unique k with n+1 = 2**k * (an odd integer)."""
    _natural(n, "n")
    m = n + 1
    return (m & -m).bit_length() - 1


def column_element(k: int, j: int) -> int:
    """The j-th member of column k, with j starting at zero."""
    _natural(k, "k")
    _natural(j, "j")
    return (1 << k) * (2 * j + 1) - 1


def column_count(k: int, n: int) -> int:
    """Number of members of column k in [0,n)."""
    _natural(k, "k")
    _natural(n, "n")
    return n // (1 << k) - n // (1 << (k + 1))


def tail_count(k: int, n: int) -> int:
    """Number of x<n with column(x)>=k; exactly floor(n / 2**k)."""
    _natural(k, "k")
    _natural(n, "n")
    return n // (1 << k)


def replication_prefix(oracle: BitOracle, n: int) -> tuple[int, ...]:
    _natural(n, "n")
    return tuple(_bit(oracle(column(x))) for x in range(n))


def approximation_prefix(approx: Approximation, n: int) -> tuple[int, ...]:
    """Finite prefix of D(x)=a(column(x),x). Convergence is not checked."""
    _natural(n, "n")
    return tuple(_bit(approx(column(x), x)) for x in range(n))


def power_index(n: int) -> int | None:
    """Return j if n=2**j, and None otherwise (in particular at n=0)."""
    _natural(n, "n")
    if n and n & (n - 1) == 0:
        return n.bit_length() - 1
    return None


def sparse_encode_prefix(
    base: BitOracle, extra: BitOracle, n: int
) -> tuple[int, ...]:
    """Overwrite the powers of two with successive bits of extra."""
    _natural(n, "n")
    answer = []
    for x in range(n):
        j = power_index(x)
        answer.append(_bit(base(x) if j is None else extra(j)))
    return tuple(answer)


def error_count(left: Sequence[int], right: Sequence[int]) -> int:
    if len(left) != len(right):
        raise ValueError("the prefixes must have the same length")
    return sum(x != y for x, y in zip(left, right))


def error_bound(n: int, k: int, lock_length: int) -> Fraction:
    """Bound M/n + 2**(-k), assuming errors after M use only columns >=k."""
    _natural(n, "n")
    _natural(k, "k")
    _natural(lock_length, "lock_length")
    if n == 0:
        raise ValueError("n must be positive")
    return Fraction(lock_length, n) + Fraction(1, 1 << k)


def majority_on_column(
    description: BitOracle, k: int, sample_size: int
) -> int:
    """Majority on the first sample_size members; ties are resolved as zero."""
    _natural(k, "k")
    _natural(sample_size, "sample_size")
    if sample_size == 0:
        raise ValueError("sample_size must be positive")
    ones = sum(_bit(description(column_element(k, j)))
               for j in range(sample_size))
    return int(2 * ones > sample_size)
