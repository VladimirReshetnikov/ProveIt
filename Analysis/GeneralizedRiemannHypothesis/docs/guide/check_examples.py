#!/usr/bin/env python3
"""Exact arithmetic for worked examples in the expanded exposition. Python 3."""
from fractions import Fraction
from math import isqrt


def check(condition, description):
    if not condition:
        raise ValueError(description)


def is_prime(n):
    return n >= 2 and all(n % k for k in range(2, isqrt(n) + 1))


def legendre(n, p):
    value = pow(n % p, (p - 1) // 2, p)
    return -1 if value == p - 1 else value


def kernel(n, limit):
    return max(0, Fraction(1, n) - Fraction(1, limit))


def primes_and_cutoffs():
    modulus, d = 18480, 9239
    check(is_prime(d) and d % modulus == modulus // 2 - 1, "auxiliary prime")
    for p, residue, symbol in [(18481, 1, 1), (19, 19, -1), (258721, 1, -1)]:
        check(is_prime(p) and p % modulus == residue, f"prime and residue of {p}")
        check(legendre(p, d) == symbol, f"quadratic character at {p}")
    check(19 % 5 == 4 and modulus % 5 == 0, "odd powers of 19 miss the progression")
    p, weight = 19, 1
    y = 2 * p**3 * weight
    terms = [max(0, Fraction(y, p**e) - weight) for e in (1, 3, 5)]
    check(terms == [721, 1, 0] and sum(terms) == 722, "local gain at 19")
    print("The three prime examples and the 19-adic calculation agree.")

    A, B = [1, 6, 11, 16, 21], {4, 9}
    for n, expected in [(11, [14, 9, 4, 24, 19]), (2, [23, 13, 3, 18, 8])]:
        partners = [(-n * tau) % 25 for tau in A]
        check(partners == expected, "table of partners modulo 25")
        raw = sum(kernel(n, 5 if t in B else 20) for t in partners)
        correction = len(B) * (kernel(n, 5) - kernel(n, 20)) if n % 5 == 1 else 0
        check(raw == len(A) * kernel(n, 20) + correction, "two-cutoff identity")
    print("Both rows of the fibre example satisfy the exact two-cutoff identity.")


def volumes_and_ranks():
    def matmul(A, B):
        return [[sum(x * y for x, y in zip(row, col)) for col in zip(*B)] for row in A]

    def det2(A):
        return A[0][0] * A[1][1] - A[0][1] * A[1][0]

    identity = [[1, 0], [0, 1]]
    Y = [[Fraction(1, 3), 0], [0, Fraction(1, 5)]]
    U = [[3, 0], [0, 5]]
    check(matmul(Y, U) == identity and det2(Y)**2 * det2(U)**2 == 1,
          "clearing the two denominators gives equality in squared volume")
    T = [[1, 2], [2, 4]]
    P = [[Fraction(x, 5) for x in row] for row in T]
    check(matmul(P, P) == P and matmul(P, [[1], [0]]) == [[Fraction(1, 5)], [Fraction(2, 5)]],
          "projecting onto the 5-eigenspace")
    overlaps = [sum((j + s) % 8 == i for i in range(2) for j in range(2)) for s in range(8)]
    check(overlaps == [2, 1, 0, 0, 0, 0, 0, 1] and sum(overlaps) == 4,
          "cyclic second moment")
    covered = {(j + s) % 8 for s in (0, 2, 4, 6) for j in range(2)}
    check(len(covered) == 8, "four disjoint translates span the target")
    print("The determinant, projection and cyclic second-moment examples agree.")


def exponents():
    eta, eps = Fraction(1, 400), Fraction(1, 50)
    check(eta / 12 == Fraction(1, 4800) and 9600 * eta / 12 == 2,
          "decay at the distant cutoff")
    check(6 * eta == Fraction(3, 200) and eps - 6 * eta == Fraction(1, 200),
          "slack in the final exponent")
    print("The cutoff and exponent calculations agree exactly.")


if __name__ == "__main__":
    primes_and_cutoffs()
    volumes_and_ranks()
    exponents()
