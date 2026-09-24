"""Exact formal series for F = x + c F^[r] F^[s].

A superscript in square brackets denotes composition, not ordinary power.
All arrays are in ascending degree order.  No third-party dependencies.
"""
from __future__ import annotations
from math import gcd
from typing import Optional


def solve(r: int, s: int, degree: int, c: int = 1,
          modulus: Optional[int] = None) -> list[int]:
    """Return coefficients through degree, using a triangular O(N^3) algorithm.

    For K=max(r,s,1), time is O(N^3+K*N^2) arithmetic operations,
    not bit operations, and memory is O(N^2+K*N) ring elements.
    r,s must be nonnegative; c can be any integer.  If supplied, modulus > 0.
    """
    for name, value in (("r", r), ("s", s), ("degree", degree)):
        if not isinstance(value, int) or value < 0:
            raise ValueError(f"{name} must be a nonnegative integer")
    if not isinstance(c, int):
        raise TypeError("c must be an integer")
    if modulus is not None and (not isinstance(modulus, int) or modulus < 1):
        raise ValueError("modulus must be a positive integer")
    nmax = degree
    a = [0] * (nmax + 1)
    powers = [[0] * (nmax + 1) for _ in range(nmax + 1)]
    powers[0][0] = 1
    it = [[0] * (nmax + 1) for _ in range(max(r, s, 1) + 1)]
    if nmax:
        it[0][1] = 1
    red = (lambda v: v) if modulus is None else (lambda v: v % modulus)
    for n in range(1, nmax + 1):
        a[n] = red((1 if n == 1 else 0)
                   + c * sum(it[r][i] * it[s][n-i] for i in range(1, n)))
        powers[1][n] = a[n]
        for k in range(2, n + 1):
            powers[k][n] = red(sum(a[i] * powers[k-1][n-i]
                                   for i in range(1, n-k+2)))
        it[1][n] = a[n]
        for j in range(2, len(it)):
            it[j][n] = red(sum(it[j-1][k] * powers[k][n]
                              for k in range(1, n+1)))
    return a


def multiply(a: list[int], b: list[int], n: int,
             modulus: Optional[int] = None) -> list[int]:
    out = [0] * (n + 1)
    for i, ai in enumerate(a[:n+1]):
        if ai:
            for j in range(min(len(b), n-i+1)):
                out[i+j] += ai * b[j]
    return out if modulus is None else [x % modulus for x in out]


def compose(a: list[int], b: list[int], n: int,
            modulus: Optional[int] = None) -> list[int]:
    """Independent Horner implementation of a(b(x)) modulo x^(n+1)."""
    if b[0] != 0:
        raise ValueError("inner series must have zero constant coefficient")
    out = [0] * (n + 1)
    for ai in reversed(a[:n+1]):
        out = multiply(out, b, n, modulus)
        out[0] = ai if modulus is None else ai % modulus
    return out


def inverse(a: list[int], n: int, modulus: Optional[int] = None) -> list[int]:
    """Compositional inverse by triangular coefficient cancellation."""
    if not isinstance(n, int) or n < 0:
        raise ValueError("n must be a nonnegative integer")
    if n == 0:
        return [0]
    if len(a) < 2 or a[0] != 0 or a[1] != 1:
        raise ValueError("expected a(x)=x+O(x^2)")
    g = [0] * (n + 1)
    if n:
        g[1] = 1
    for d in range(2, n + 1):
        value = -compose(a[:d+1], g[:d+1], d, modulus)[d]
        g[d] = value if modulus is None else value % modulus
    return g


def iterate(a: list[int], k: int, n: int,
            modulus: Optional[int] = None) -> list[int]:
    """Positive or negative integer iterate, by binary composition."""
    if not isinstance(k, int):
        raise TypeError("k must be an integer")
    if not isinstance(n, int) or n < 0:
        raise ValueError("n must be a nonnegative integer")
    if n == 0:
        return [0]
    out = [0] * (n + 1)
    if n:
        out[1] = 1
    base = a[:n+1] + [0] * max(0, n+1-len(a))
    if k < 0:
        base = inverse(base, n, modulus)
        k = -k
    while k:
        if k & 1:
            out = compose(out, base, n, modulus)
        k >>= 1
        if k:
            base = compose(base, base, n, modulus)
    return out


def rational_coefficients(num: list[int], den: list[int], n: int,
                          modulus: int) -> list[int]:
    """Expansion of num/den modulo modulus; den[0] must be a unit."""
    if gcd(den[0], modulus) != 1:
        raise ValueError("denominator constant is not a unit")
    inv = pow(den[0], -1, modulus)
    a = [0] * (n+1)
    for i in range(n+1):
        a[i] = inv * ((num[i] if i < len(num) else 0)
                      - sum(den[j]*a[i-j]
                            for j in range(1, min(i, len(den)-1)+1))) % modulus
    return a


def correction_coefficients(n: int) -> tuple[list[int], list[int]]:
    h2 = rational_coefficients([0, 0, 0, 1], [1, 0, 0, 1], n, 2)
    # H5 = x^3(2-x)(1+x+x^2+x^3) /
    #       ((1-x)^2(1-x^4+2x^5)); reduced modulo 5.
    h5 = rational_coefficients([0, 0, 0, 2, 1, 1, 1, -1],
                               [1, -2, 1, 0, -1, 4, -5, 2], n, 5)
    return h2, h5


def last_two_digits(n: int) -> list[int]:
    """Return a(0)=0 and all last-two-digit residues through index n."""
    if not isinstance(n, int) or n < 0:
        raise ValueError("n must be a nonnegative integer")
    h2, h5 = correction_coefficients(n)
    return [0] + [(1 + 50*h2[i] + 80*h5[i]) % 100 for i in range(1, n+1)]


def last_two_digits_at(n: int) -> int:
    """Return a(n) mod 100 for a positive index, using the proved period.

    The rational recurrence is evaluated at most through degree 46860,
    regardless of the magnitude of n. No full integer a(n) is constructed.
    """
    if not isinstance(n, int) or n < 1:
        raise ValueError("n must be a positive integer")
    reduced_index = (n - 1) % 46860 + 1
    return last_two_digits(reduced_index)[-1]
