#!/usr/bin/env python3
"""Exact arithmetic for reciprocal-arithmetic-progression Hankel determinants.

Only the Python standard library is required. Matrix indices are 0,...,n;
therefore a Hankel determinant with index n has size n+1, not size n.
All public numerical functions use exact integers or fractions.Fraction.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from math import comb, factorial, gcd, prod
from typing import Sequence


def _natural(value: int, name: str, *, positive: bool = False) -> None:
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError(f"{name} must be an integer")
    if value < (1 if positive else 0):
        raise ValueError(f"{name} must be {'positive' if positive else 'nonnegative'}")


def factor_integer(value: int) -> dict[int, int]:
    """Trial-division factorization; intended for moderate parameter values."""
    _natural(value, "value", positive=True)
    result: dict[int, int] = {}
    divisor = 2
    while divisor * divisor <= value:
        while value % divisor == 0:
            result[divisor] = result.get(divisor, 0) + 1
            value //= divisor
        divisor = 3 if divisor == 2 else divisor + 2
    if value > 1:
        result[value] = result.get(value, 0) + 1
    return result


def _prime(p: int) -> None:
    _natural(p, "p", positive=True)
    if p < 2 or factor_integer(p) != {p: 1}:
        raise ValueError("p must be prime")


def valuation(value: int, p: int) -> int:
    """v_p of a nonzero integer; p is required to be prime."""
    _prime(p)
    if not isinstance(value, int) or value == 0:
        raise ValueError("valuation requires a nonzero integer")
    value = abs(value)
    result = 0
    while value % p == 0:
        result += 1
        value //= p
    return result


def factorial_valuation(n: int, p: int) -> int:
    _natural(n, "n")
    _prime(p)
    total = 0
    while n:
        n //= p
        total += n
    return total


def floor_sum(n: int, d: int) -> int:
    """Sum_{k=0}^n floor(k/d), evaluated in O(1) integer operations."""
    _natural(n, "n")
    _natural(d, "d", positive=True)
    t, b = divmod(n + 1, d)
    return d * t * (t - 1) // 2 + t * b


def superfactorial_valuation(n: int, p: int) -> int:
    """v_p(product_{k=0}^n k!), without constructing the factorials."""
    _natural(n, "n")
    _prime(p)
    total, d = 0, p
    while d <= n:
        total += floor_sum(n, d)
        d *= p
    return total


def prime_exponent_sequence(n: int, p: int) -> int:
    """E_p(n), so the conjectured prime-parameter numerator is p^(2 E_p(n))."""
    _natural(n, "n")
    _prime(p)
    return n * (n + 1) // 2 + superfactorial_valuation(n, p)


def numerator_factorization(n: int, m: int, a: int = 1) -> dict[int, int]:
    """Proved numerator formula, including noncoprime a and m."""
    _natural(n, "n")
    _natural(m, "m", positive=True)
    _natural(a, "a", positive=True)
    common = gcd(m, a)
    reduced_m = m // common
    result = {}
    for p, exponent in factor_integer(reduced_m).items():
        power = (n * (n + 1) * exponent
                 + 2 * superfactorial_valuation(n, p)
                 - (n + 1) * valuation(common, p))
        if power > 0:
            result[p] = power
    return result


def predicted_numerator(n: int, m: int, a: int = 1) -> int:
    return prod(p ** exponent for p, exponent in numerator_factorization(n, m, a).items())


def hankel_matrix(n: int, m: int, a: int = 1) -> list[list[Fraction]]:
    _natural(n, "n")
    _natural(m, "m", positive=True)
    _natural(a, "a", positive=True)
    return [[Fraction(1, a + m * (i + j)) for j in range(n + 1)]
            for i in range(n + 1)]


def determinant(matrix: Sequence[Sequence[Fraction | int]]) -> Fraction:
    """Exact Gaussian elimination, independent of the determinant product."""
    size = len(matrix)
    if any(len(row) != size for row in matrix):
        raise ValueError("matrix must be square")
    work = [[Fraction(x) for x in row] for row in matrix]
    answer = Fraction(1)
    for k in range(size):
        pivot_row = next((i for i in range(k, size) if work[i][k]), None)
        if pivot_row is None:
            return Fraction(0)
        if pivot_row != k:
            work[k], work[pivot_row] = work[pivot_row], work[k]
            answer = -answer
        pivot = work[k][k]
        answer *= pivot
        for i in range(k + 1, size):
            multiplier = work[i][k] / pivot
            work[i][k] = Fraction(0)
            for j in range(k + 1, size):
                work[i][j] -= multiplier * work[k][j]
    return answer


def determinant_product(n: int, m: int, a: int = 1) -> Fraction:
    """Cauchy's formula, compressed to the 2n+1 different denominator factors."""
    _natural(n, "n")
    _natural(m, "m", positive=True)
    _natural(a, "a", positive=True)
    numerator = m ** (n * (n + 1)) * prod(factorial(k) ** 2 for k in range(n + 1))
    denominator = prod((a + m * s) ** min(s + 1, 2 * n + 1 - s)
                       for s in range(2 * n + 1))
    return Fraction(numerator, denominator)


def hankel_ratio_sequence(max_n: int, m: int, a: int = 1) -> list[Fraction]:
    """All determinants H_0..H_max_n by the size-ratio recursion of eq. (Hratio).

    A third evaluation route, independent of both Gaussian elimination and the
    compressed Cauchy product: each step multiplies by the closed-form quotient
    H_n/H_(n-1), so an error in the product formula cannot hide here.
    """
    _natural(max_n, "max_n")
    _natural(m, "m", positive=True)
    _natural(a, "a", positive=True)
    result = [Fraction(1, a)]
    for n in range(1, max_n + 1):
        top = m ** (2 * n) * factorial(n) ** 2
        bottom = (a + 2 * m * n) * prod(a + m * (n + j) for j in range(n)) ** 2
        result.append(result[-1] * Fraction(top, bottom))
    return result


def triangular_count(b: int, s: int) -> int:
    """Number of (u,v) in [0,b)^2 with u+v=s."""
    if b <= 0 or s < 0 or s > 2 * b - 2:
        return 0
    return min(s + 1, 2 * b - 1 - s, b)


def residual_count(d: int, b: int, r: int) -> int:
    _natural(d, "d", positive=True)
    if not (0 <= b < d and 0 <= r < d):
        raise ValueError("require 0 <= b,r < d")
    return triangular_count(b, r) + triangular_count(b, r + d)


def residue_square_count(N: int, d: int, r: int) -> int:
    _natural(N, "N", positive=True)
    _natural(d, "d", positive=True)
    if not 0 <= r < d:
        raise ValueError("require 0 <= r < d")
    t, b = divmod(N, d)
    return d * t * t + 2 * t * b + residual_count(d, b, r)


def denominator_valuation(n: int, m: int, a: int, q: int) -> int:
    """Prime-power counting formula, for coprime a,m only."""
    _natural(n, "n")
    _natural(m, "m", positive=True)
    _natural(a, "a", positive=True)
    _prime(q)
    if gcd(a, m) != 1:
        raise ValueError("this valuation formula requires gcd(a,m)=1")
    if m % q == 0:
        return 0
    total, d, N = 0, q, n + 1
    while d <= a + 2 * m * n:
        r = (-a * pow(m, -1, d)) % d
        total += d * (N // d) + residual_count(d, N % d, r)
        d *= q
    return total


def hilbert_denominator(n: int) -> int:
    _natural(n, "n")
    return prod((2 * k + 1) * comb(2 * k, k) ** 2 for k in range(n + 1))


def remove_supported_primes(value: int, m: int) -> int:
    _natural(value, "value", positive=True)
    _natural(m, "m", positive=True)
    for p in factor_integer(m):
        while value % p == 0:
            value //= p
    return value


def universal_denominator(n: int, m: int) -> int:
    return remove_supported_primes(hilbert_denominator(n), m)


def biarithmetic_matrix(n: int, m1: int, m2: int, a: int = 1) -> list[list[Fraction]]:
    """Entries 1/(a + m1*i + m2*j); unequal row and column steps."""
    _natural(n, "n")
    _natural(m1, "m1", positive=True)
    _natural(m2, "m2", positive=True)
    _natural(a, "a", positive=True)
    return [[Fraction(1, a + m1 * i + m2 * j) for j in range(n + 1)]
            for i in range(n + 1)]


def biarithmetic_product(n: int, m1: int, m2: int, a: int = 1) -> Fraction:
    """Cauchy evaluation of det(1/(a + m1*i + m2*j)) for 0 <= i,j <= n.

    Same indexing convention as the rest of this module: the matrix has size
    n+1. No coprimality is assumed; the numerator support is bounded by the
    primes of m1*m2 (unequal-step theorem).
    """
    _natural(n, "n")
    _natural(m1, "m1", positive=True)
    _natural(m2, "m2", positive=True)
    _natural(a, "a", positive=True)
    size = n + 1
    numerator = ((m1 * m2) ** (size * (size - 1) // 2)
                 * prod(factorial(k) ** 2 for k in range(size)))
    denominator = prod(a + m1 * i + m2 * j
                       for i in range(size) for j in range(size))
    return Fraction(numerator, denominator)


def two_shift_certificate(n: int, m: int) -> dict[str, int]:
    """Two offsets whose denominators already have the universal gcd.

    Returns the offsets 1 and a_* of the constructive corollary, the two
    denominators, their gcd, and the predicted value (L_n)_{perp m}. The
    primes of the (possibly enormous) denominator at offset 1 are found by
    factoring only the 2n+1 small entry denominators 1+m*s, so no large
    determinant denominator is ever factored.
    """
    _natural(n, "n")
    _natural(m, "m", positive=True)
    first = determinant_product(n, m, 1).denominator
    modulus = 1
    for p in sorted({p for s in range(2 * n + 1)
                     for p in factor_integer(1 + m * s)}):
        if first % p:
            continue
        power = p
        while power <= 2 * n + 1:
            power *= p
        modulus *= power
    if m == 1:
        offset = 1
    else:
        offset = m + modulus * (((1 - m) * pow(modulus, -1, m)) % m)
    second = determinant_product(n, m, offset).denominator
    return {"n": n, "m": m, "a1": 1, "a2": offset,
            "denominator1": first, "denominator2": second,
            "gcd": gcd(first, second),
            "predicted_gcd": universal_denominator(n, m)}


def sharpness_witness(n: int, m: int, q: int) -> int:
    """Positive a coprime to m attaining the minimum q-adic denominator exponent."""
    _natural(n, "n")
    _natural(m, "m", positive=True)
    _prime(q)
    if m % q == 0:
        raise ValueError("q must not divide m")
    modulus = q
    while modulus <= 2 * n + 1:
        modulus *= q
    t = ((1 - m) * pow(modulus, -1, m)) % m if m > 1 else 0
    return m + modulus * t


def generalized_binomial(x: Fraction | int, k: int) -> Fraction:
    _natural(k, "k")
    x = Fraction(x)
    answer = Fraction(1)
    for j in range(k):
        answer *= (x - j) / (j + 1)
    return answer


def inverse_formula(n: int, m: int, a: int = 1) -> list[list[Fraction]]:
    """Four-binomial version of the Cauchy inverse formula."""
    _natural(n, "n")
    _natural(m, "m", positive=True)
    _natural(a, "a", positive=True)
    alpha = Fraction(a, m)
    return [[(-1) ** (i + j) * m * (alpha + i + j)
             * generalized_binomial(alpha + n + i, n - j)
             * generalized_binomial(alpha + n + j, n - i)
             * generalized_binomial(alpha + i + j - 1, i)
             * generalized_binomial(alpha + i + j - 1, j)
             for j in range(n + 1)] for i in range(n + 1)]


def plane_partition_polynomial(N: int, height: Fraction | int) -> Fraction:
    """MacMahon's N by N box polynomial evaluated at any rational height."""
    _natural(N, "N", positive=True)
    height = Fraction(height)
    return prod((height + i + j - 1) / (i + j - 1)
                for i in range(1, N + 1) for j in range(1, N + 1))


def digit_sum(value: int, base: int) -> int:
    _natural(value, "value")
    _natural(base, "base", positive=True)
    if base < 2:
        raise ValueError("base must be at least two")
    total = 0
    while value:
        value, digit = divmod(value, base)
        total += digit
    return total


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int, help="Hankel index (matrix size is n+1)")
    parser.add_argument("m", type=int, help="positive progression step")
    parser.add_argument("a", type=int, nargs="?", default=1, help="positive offset (default: 1)")
    parser.add_argument("--matrix-check", action="store_true", help="also use exact Gaussian elimination")
    args = parser.parse_args()
    try:
        result = determinant_product(args.n, args.m, args.a)
        prediction = predicted_numerator(args.n, args.m, args.a)
        if prediction != result.numerator:
            raise ArithmeticError("numerator formula disagrees with the product")
        print(f"H_{args.n}({args.m},{args.a}) = {result}")
        print(f"numerator factorization: {numerator_factorization(args.n, args.m, args.a)}")
        print(f"denominator: {result.denominator}")
        if args.matrix_check:
            if determinant(hankel_matrix(args.n, args.m, args.a)) != result:
                raise ArithmeticError("independent Gaussian elimination disagrees")
            print("Independent exact matrix check: PASS")
    except (TypeError, ValueError, ArithmeticError) as error:
        parser.error(str(error))


if __name__ == "__main__":
    main()
