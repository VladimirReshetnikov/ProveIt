"""Exact Rueppel Hankel formulas and an independent integer determinant engine.

Only the Python standard library is required. Indices of determinants are matrix
sizes: hankel(a, n) is n by n, and the empty determinant is 1.
"""
from __future__ import annotations
from collections.abc import Sequence


def _index(n: int) -> None:
    if not isinstance(n, int) or isinstance(n, bool) or n < 0:
        raise ValueError("The index must be a nonnegative integer.")


def sign(exponent: int) -> int:
    return -1 if exponent % 2 else 1


def rueppel(n: int) -> int:
    """Characteristic function of {2**j - 1 : j >= 0}."""
    _index(n)
    return int((n & (n + 1)) == 0)


def binary_runs(n: int) -> int:
    """Number of maximal constant-bit runs; the representation of 0 is empty."""
    _index(n)
    return (n ^ (n >> 1)).bit_count()


def one_runs(n: int) -> int:
    _index(n)
    return (binary_runs(n) + 1) // 2


def gray_statistics(n: int) -> tuple[int, int]:
    """Return (number of non-lowest Gray-code ones, lowest Gray-code bit)."""
    _index(n)
    gray = n ^ (n >> 1)
    return (gray >> 1).bit_count(), gray & 1


def D(n: int) -> int:
    _index(n)
    return sign(n * (n - 1) // 2)


def E(n: int) -> int:
    _index(n)
    return sign(n * (n + 1) // 2 + one_runs(n))


def E_by_recursion(n: int) -> int:
    """Iterative use of E(n) = D(ceil(n/2)) E(floor(n/2))."""
    _index(n)
    result = 1
    while n:
        result *= D((n + 1) // 2)
        n //= 2
    return result


def T(n: int) -> int:
    _index(n)
    return 0 if n % 2 else sign(n // 2)


def B(n: int) -> int:
    _index(n)
    return 1 if n == 0 else -E(n - 1) * binary_runs(n - 1)


def parameter_coefficients(n: int) -> tuple[int, int]:
    """Return (c0,c2) with H_n(t*x + 1/r(x*x)) = c0 + c2*t*t."""
    _index(n)
    if n == 0:
        return 1, 0
    a, b = gray_statistics(n)
    sigma = sign(1 + b + (a + b) // 2)
    return sigma * b, sigma * a


def parameter_hankel(n: int, t: int = 1) -> int:
    c0, c2 = parameter_coefficients(n)
    return c0 + c2 * t * t


def linear_hankel(n: int, u: int = 1, v: int = 1) -> int:
    """H_n(u + v*x*r(x)), as a polynomial formula in u and v."""
    _index(n)
    if n == 0:
        return 1
    return v ** (n - 1) * E(n - 1) * (u - v * binary_runs(n - 1))


def reciprocal_hankel(n: int, v: int = 1) -> int:
    """H_n(1/(1 + v*x*r(x)))."""
    _index(n)
    return 1 if n == 0 else (-v) ** (n - 1) * E(n - 1)


def periodic_hankel(n: int, u: int = 1, v: int = -1) -> int:
    """H_n(u + v*x/r(x*x)); n=0 is handled separately."""
    _index(n)
    if n == 0:
        return 1
    m = n // 2
    if n % 2:
        return sign(m) * u * v ** (2 * m)
    return sign(m) * v ** (2 * m) if m % 2 else 0


def reciprocal_coefficients(a: Sequence[int], length: int | None = None) -> list[int]:
    """Truncated reciprocal, for an integer series with constant coefficient 1."""
    if not a or a[0] != 1:
        raise ValueError("The series must have constant coefficient 1.")
    if length is None:
        length = len(a)
    _index(length)
    if length > len(a):
        raise ValueError("Insufficient input coefficients.")
    if length == 0:
        return []
    out = [1] + [0] * (length - 1)
    support = [(j, a[j]) for j in range(1, length) if a[j]]
    for n in range(1, length):
        out[n] = -sum(value * out[n - j] for j, value in support if j <= n)
    return out


def parameter_moments(length: int, t: int = 1) -> list[int]:
    _index(length)
    if not length:
        return []
    reciprocal = reciprocal_coefficients([rueppel(j) for j in range((length + 1) // 2)])
    out = [reciprocal[j // 2] if j % 2 == 0 else 0 for j in range(length)]
    if length > 1:
        out[1] = t
    return out


def periodic_moments(length: int, u: int = 1, v: int = -1) -> list[int]:
    _index(length)
    if not length:
        return []
    reciprocal = reciprocal_coefficients([rueppel(j) for j in range((length + 1) // 2)])
    return [u] + [v * reciprocal[(j - 1) // 2] if j % 2 else 0
                  for j in range(1, length)]


def linear_moments(length: int, u: int = 1, v: int = 1) -> list[int]:
    _index(length)
    return [] if not length else [u] + [v * rueppel(j - 1) for j in range(1, length)]


def determinant(matrix: Sequence[Sequence[int]]) -> int:
    """Fraction-free Bareiss determinant with row pivoting and exact division.

    This routine does not use any Rueppel identity. It also handles singular
    matrices and leading zero pivots; no floating-point arithmetic is used.
    """
    n = len(matrix)
    if any(len(row) != n for row in matrix):
        raise ValueError("The matrix must be square.")
    if any(not isinstance(x, int) for row in matrix for x in row):
        raise TypeError("This determinant engine accepts integer entries only.")
    if n == 0:
        return 1
    a = [list(row) for row in matrix]
    parity, previous = 1, 1
    for k in range(n - 1):
        if a[k][k] == 0:
            pivot_row = next((i for i in range(k + 1, n) if a[i][k] != 0), None)
            if pivot_row is None:
                return 0
            a[k], a[pivot_row] = a[pivot_row], a[k]
            parity = -parity
        pivot = a[k][k]
        row_k = a[k]
        for i in range(k + 1, n):
            row_i, multiplier = a[i], a[i][k]
            for j in range(k + 1, n):
                numerator = pivot * row_i[j] - multiplier * row_k[j]
                quotient, remainder = divmod(numerator, previous)
                if remainder:
                    raise ArithmeticError("Nonexact Bareiss division.")
                row_i[j] = quotient
            row_i[k] = 0
        previous = pivot
    return parity * a[-1][-1]


def hankel(moments: Sequence[int], n: int, shift: int = 0) -> int:
    """Negative moment indices are zero; the determinant of size zero is one."""
    _index(n)
    if not isinstance(shift, int):
        raise TypeError("The shift must be an integer.")
    if n == 0:
        return 1
    if shift + 2 * n - 2 >= len(moments):
        raise ValueError("Insufficient moments for this determinant.")
    return determinant([[moments[shift + i + j] if shift + i + j >= 0 else 0
                         for j in range(n)] for i in range(n)])
