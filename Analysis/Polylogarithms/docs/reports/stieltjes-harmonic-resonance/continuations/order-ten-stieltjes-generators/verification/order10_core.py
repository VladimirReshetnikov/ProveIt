#!/usr/bin/env python3
"""Exact modular arithmetic for the order-ten harmonic-tail certificate.

The proof uses the prime P=1,000,003.  All Bernoulli and factorial
arguments occurring for 6 <= b < 1920 are strictly smaller than P-1,
so every displayed rational denominator is a P-adic unit.
"""
from __future__ import annotations

from dataclasses import dataclass
from hashlib import sha256
from math import factorial, isqrt
from typing import Iterable, List, Sequence

PRIME = 1_000_003
A = 5
B_MIN = 6
B_RETAINED_MIN = 10
B_MAX = 1919
MAX_MATRIX_FACTORIAL = 2 * B_MAX
MAX_FACTORIAL = 2 * B_MAX + 1  # one extra row for C(2m+1,2j) in the Bernoulli recurrence


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d <= isqrt(n):
        if n % d == 0:
            return False
        d += 2
    return True


def build_factorials(p: int = PRIME, limit: int = MAX_FACTORIAL) -> tuple[list[int], list[int]]:
    if limit >= p:
        raise ValueError("factorial table must stay below the modulus")
    fact = [1] * (limit + 1)
    for n in range(1, limit + 1):
        fact[n] = fact[n - 1] * n % p
    invfact = [1] * (limit + 1)
    invfact[limit] = pow(fact[limit], p - 2, p)
    for n in range(limit, 0, -1):
        invfact[n - 1] = invfact[n] * n % p
    return fact, invfact


def binom_mod(n: int, k: int, fact: Sequence[int], invfact: Sequence[int], p: int = PRIME) -> int:
    if k < 0 or k > n:
        return 0
    return fact[n] * invfact[k] % p * invfact[n - k] % p


def falling_mod(x: int, k: int, p: int = PRIME) -> int:
    out = 1
    for r in range(k):
        out = out * (x - r) % p
    return out


def even_bernoulli_mod(
    max_m: int,
    fact: Sequence[int],
    invfact: Sequence[int],
    p: int = PRIME,
) -> list[int]:
    """Return B_{2m} mod p for 0 <= m <= max_m.

    Uses the exact Bernoulli recurrence with B_1=-1/2:
      B_{2m}=((2m-1)/2 - sum_{j=1}^{m-1} C(2m+1,2j)B_{2j})/(2m+1).
    Since 2m+1 < p throughout the certificate range, every division is valid.
    """
    if 2 * max_m + 1 >= p:
        raise ValueError("Bernoulli recurrence crosses the modulus")
    inv2 = (p + 1) // 2
    vals = [0] * (max_m + 1)
    vals[0] = 1
    for m in range(1, max_m + 1):
        n = 2 * m
        acc = 0
        for j in range(1, m):
            acc = (acc + binom_mod(n + 1, 2 * j, fact, invfact, p) * vals[j]) % p
        vals[m] = (((n - 1) * inv2 - acc) % p) * pow(n + 1, p - 2, p) % p
    return vals


def determinant_mod(matrix: Sequence[Sequence[int]], p: int = PRIME) -> int:
    a = [[int(x) % p for x in row] for row in matrix]
    n = len(a)
    if any(len(row) != n for row in a):
        raise ValueError("matrix must be square")
    det = 1
    for k in range(n):
        pivot = next((r for r in range(k, n) if a[r][k] % p), None)
        if pivot is None:
            return 0
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            det = -det % p
        pv = a[k][k] % p
        det = det * pv % p
        inv = pow(pv, p - 2, p)
        for i in range(k + 1, n):
            factor = a[i][k] * inv % p
            if factor:
                for j in range(k + 1, n):
                    a[i][j] = (a[i][j] - factor * a[k][j]) % p
            a[i][k] = 0
    return det % p


def _factorial_ratio(num: int, den: int, fact: Sequence[int], invfact: Sequence[int], p: int = PRIME) -> int:
    if num < 0 or den < 0:
        raise ValueError("negative factorial argument")
    return fact[num] * invfact[den] % p


def direct_matrix_order_ten(
    b: int,
    bernoulli_even: Sequence[int],
    fact: Sequence[int],
    invfact: Sequence[int],
    p: int = PRIME,
) -> list[list[int]]:
    """The exact source matrix M_{5,b}, used for 6 <= b < 10."""
    if b < 6:
        raise ValueError("order ten requires b >= 6")
    out: list[list[int]] = []
    for t in range(b):
        row: list[int] = []
        for k in range(b):
            idx = t + k - A + 1
            if idx < 0:
                mu = 0
            elif idx == 0:
                mu = 1
            else:
                mu = bernoulli_even[idx] * invfact[2 * idx] % p
            term1 = _factorial_ratio(2 * b + 2 * t - 2 * A + 1, 2 * b - 2 * k, fact, invfact, p)
            term2 = 0
            if k < A:
                term2 = _factorial_ratio(2 * t + 1, 2 * A - 2 * k, fact, invfact, p)
            row.append(mu * (term1 + term2) % p)
        out.append(row)
    return out


def retained_matrix_order_ten(
    b: int,
    bernoulli_even: Sequence[int],
    fact: Sequence[int],
    invfact: Sequence[int],
    p: int = PRIME,
) -> list[list[int]]:
    """The normalized 5x5 retained matrix A^[5] for b >= 10.

    This is the matrix from the source small-determinant theorem after the
    Padé row transformation, retained-column reversal, and row normalization.
    Its determinant is nonzero iff det M_{5,b} is nonzero.
    """
    if b < B_RETAINED_MIN:
        raise ValueError("retained formula requires b >= 10")
    out: list[list[int]] = []
    for i in range(A):
        n = b - A + i
        row: list[int] = []
        for ell in range(A):
            N = 2 * (n - ell) + 1
            R = 2 * b - 2 * A + 2 + 2 * ell

            prod = 1
            for r in range(2 * ell):
                prod = prod * (2 * n - r) % p
                prod = prod * (2 * n + 3 + r) % p
            F = prod * invfact[2 * ell + 1] % p

            spectral = 0
            for h in range(1, 2 * i + 2, 2):
                delta = 0
                for j in range(h + 1):
                    z = N - j
                    W = (z + 2 * ell + 1) * falling_mod(2 * n + 2 * ell + z + 1, 2 * i, p)
                    delta += (-1) ** (h - j) * binom_mod(h, j, fact, invfact, p) * W
                d = delta % p * invfact[h] % p
                index = A - i + ell + (h - 1) // 2
                U = 2 * bernoulli_even[b - index] % p
                spectral = (spectral + d * falling_mod(N, h, p) * U) % p

            denominator = (
                (2 * n + 1)
                * (2 * n + 2)
                * fact[2 * ell + 2]
                % p
                * fact[N]
            ) % p
            coefficient = fact[R] * pow(denominator, p - 2, p) % p
            row.append((2 * F + coefficient * spectral) % p)
        out.append(row)
    return out


def residue_for_b(
    b: int,
    bernoulli_even: Sequence[int],
    fact: Sequence[int],
    invfact: Sequence[int],
    p: int = PRIME,
) -> int:
    if b < B_RETAINED_MIN:
        matrix = direct_matrix_order_ten(b, bernoulli_even, fact, invfact, p)
    else:
        matrix = retained_matrix_order_ten(b, bernoulli_even, fact, invfact, p)
    return determinant_mod(matrix, p)


def residue_digest(residues: Sequence[int]) -> str:
    payload = ",".join(str(int(x)) for x in residues).encode("ascii")
    return sha256(payload).hexdigest()


def compute_all_residues(p: int = PRIME) -> list[int]:
    if p != PRIME:
        raise ValueError("the published certificate fixes p=1,000,003")
    if not is_prime(p):
        raise AssertionError("certificate modulus is not prime")
    fact, invfact = build_factorials(p, MAX_FACTORIAL)
    bernoulli_even = even_bernoulli_mod(B_MAX, fact, invfact, p)
    return [residue_for_b(b, bernoulli_even, fact, invfact, p) for b in range(B_MIN, B_MAX + 1)]
