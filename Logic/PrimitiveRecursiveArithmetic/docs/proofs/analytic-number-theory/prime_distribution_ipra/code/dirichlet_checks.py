#!/usr/bin/env python3
"""Exact finite checks for the explicit Dirichlet proof.

These diagnostics check finite character tables, divisor coefficients,
reciprocal-sum encoding, and the rational constants in the proof. They are
not an iPRA proof checker and do not evaluate the astronomical cutoff Y.
Only the Python standard library is used.
"""

from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import factorial, gcd, isqrt
import json


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def polynomial_trim(xs):
    result = list(xs)
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return result


def polynomial_divmod(f, g):
    f = polynomial_trim(f)
    g = polynomial_trim(g)
    assert g[-1] == 1
    quotient = [0] * max(1, len(f) - len(g) + 1)
    while len(f) >= len(g) and any(f):
        shift = len(f) - len(g)
        leading = f[-1]
        quotient[shift] = leading
        for j, coefficient in enumerate(g):
            f[shift + j] -= leading * coefficient
        f = polynomial_trim(f)
    return polynomial_trim(quotient), f


@lru_cache(None)
def cyclotomic(n):
    assert n >= 1
    poly = [-1] + [0] * (n - 1) + [1]
    for d in range(1, n):
        if n % d == 0:
            poly, remainder = polynomial_divmod(poly, cyclotomic(d))
            assert not any(remainder)
    return tuple(poly)


def character_tables(q):
    """Literal bounded enumeration; used only for small stated moduli."""
    units = [a for a in range(q) if gcd(a, q) == 1]
    h = len(units)
    result = []
    for row in product(range(h), repeat=h):
        table = dict(zip(units, row))
        if all(table[(a * b) % q] == (table[a] + table[b]) % h
               for a in units for b in units):
            result.append(table)
    return units, result


def check_characters():
    moduli = [1, 2, 3, 4, 5, 6, 8, 10, 12]
    orthogonality = 0
    positivity = 0
    squares = 0
    real_characters = 0
    for q in moduli:
        units, tables = character_tables(q)
        h = len(units)
        assert len(tables) == h
        for a in units:
            for b in units:
                polynomial = [0] * h
                for table in tables:
                    polynomial[(table[a] - table[b]) % h] += 1
                polynomial[0] -= h if a == b else 0
                _, remainder = polynomial_divmod(polynomial, cyclotomic(h))
                assert not any(remainder)
                orthogonality += 1
        for table in tables:
            if all(exponent == 0 for exponent in table.values()):
                continue
            if not all((2 * exponent) % h == 0 for exponent in table.values()):
                continue
            real_characters += 1

            def chi(n):
                residue = n % q
                if residue not in table:
                    return 0
                return 1 if table[residue] == 0 else -1

            assert sum(chi(n) for n in range(1, q + 1)) == 0
            for n in range(1, 401):
                coefficient = sum(chi(d) for d in range(1, n + 1) if n % d == 0)
                assert coefficient >= 0
                positivity += 1
                if isqrt(n) ** 2 == n:
                    assert coefficient >= 1
                    squares += 1
    return {
        "moduli": moduli,
        "orthogonality_instances": orthogonality,
        "real_nonprincipal_characters": real_characters,
        "nonnegative_divisor_coefficients": positivity,
        "positive_square_coefficients": squares,
    }


def check_constants():
    u = F(7, 8)
    assert 4 * u / (1 - u) ** 2 + 6 / (1 - u) == 272
    r = F(7, 4)
    for k in range(80):
        assert sum((r ** j for j in range(k + 1)), F(0)) < 2 ** (k + 1)
    # Exact rational verification of the elementary pi > 3 certificate.
    atan_lower = sum((F((-1) ** j, 2 * j + 1) for j in range(8)), F(0))
    assert 4 * atan_lower > 3
    for q in range(1, 101):
        m = 2 ** 20 * (q + 1) ** 2
        k = 16 * m
        d = 2 ** 25 * (q + 1) ** 2
        assert d == 2 * k
        assert 512 * (q + 1) - 272 * q > 1
        assert k >= 14 * m
        # No construction of 2**D, T, or Y is performed.
        tau = F(1, 4096 * q ** 5)
        assert tau ** 3 / (8 * q) >= (4 * q * tau) ** 4
    return {"constant_cases": 100, "geometric_sum": "272", "pi_lower_certificate": str(4 * atan_lower)}


def check_factorial_encoding():
    cases = 0
    for n in range(1, 61):
        f = factorial(n)
        for q in range(1, 9):
            for a in range(q):
                if gcd(a, q) != 1:
                    continue
                primes = [p for p in range(2, n + 1) if prime(p) and p % q == a]
                numerator = sum(f // p for p in primes)
                total = sum((F(1, p) for p in primes), F(0))
                assert F(numerator, f) == total
                cases += 1
    return cases


def next_prime_finite(q, a, b, cap):
    assert q >= 1
    for n in range(b + 1, cap + 1):
        if prime(n) and n % q == a % q:
            return n
    return 0


def main():
    result = {
        "status": "passed",
        "arithmetic": "exact Python integers and fractions.Fraction",
        "characters": check_characters(),
        "constants": check_constants(),
        "factorial_encoding_cases": check_factorial_encoding(),
        "small_search_examples": [
            {"q": q, "a": a, "lower_bound": b,
             "prime_found": next_prime_finite(q, a, b, 10000),
             "tested_cap": 10000}
            for q, a, b in [(1, 0, 100), (4, 3, 100), (5, 2, 1000), (12, 11, 1000)]
        ],
        "scope": "Finite diagnostics; not proofs of the universal theorem or an embedded iPRA derivation.",
        "theoretical_bound_evaluated": False,
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
