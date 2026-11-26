#!/usr/bin/env python3
"""Hasse trace certificates for the elliptic bound; standard library only."""

from math import gcd, isqrt, prod


def primes_through(limit):
    sieve = bytearray([1]) * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for divisor in range(2, isqrt(limit) + 1):
        if sieve[divisor]:
            multiples = range(divisor**2, limit + 1, divisor)
            sieve[divisor**2::divisor] = b"\x00" * len(multiples)
    return [n for n in range(limit + 1) if sieve[n]]


def power_trace(exponent, trace, norm):
    previous, current = 2, trace
    for _ in range(1, exponent):
        previous, current = current, trace * current - norm * previous
    return current


def differences(p, exponent, weight):
    for norm in (p, p**3):
        bound = isqrt(4 * norm)
        for trace in range(-bound, bound + 1):
            difference = (norm**weight + norm**(exponent - weight)
                          - power_trace(exponent, trace, norm))
            assert difference > 0
            yield difference


def certify_balance(small_primes):
    largest = 0
    for exponent in (1, 2, 3, 4, 6, 9, 12, 18):
        row = set()
        for weight in range((exponent + 1) // 2):
            common = 0
            for prime in (2, 3, 5, 7, 11, 13):
                common = gcd(common, prod(differences(prime, exponent, weight)))
            assert common > 0
            for factor in small_primes:
                if common % factor == 0:
                    row.add(factor)
                    while common % factor == 0:
                        common //= factor
            assert common == 1
        largest = max(largest, max(row))
        print(f"e={exponent:2d}, largest prime across unbalanced weights: {max(row)}")
    assert largest == 211


def is_square(value, ell):
    return pow(value, (ell - 1) // 2, ell) == 1


def possible_trace(exponent, modulus, norm):
    residue = (pow(norm, exponent, modulus)
               + pow(norm, (1 - exponent) % (modulus - 1), modulus)) % modulus
    return min(residue, modulus - residue) <= isqrt(4 * norm)


def main():
    primes = primes_through(253507)
    certify_balance([p for p in primes if p <= 211])
    lower_candidates = []
    survivors = []
    for ell in primes:
        if ell > 211:
            if ell % 4 != 3:
                continue
            # For a split p with 4p^3 < ell the quadratic obstruction applies.
            excluded = False
            for p in primes:
                if 4 * p**3 >= ell:
                    break
                if is_square(p, ell):
                    excluded = True
                    break
            if excluded:
                continue
            lower_candidates.append(ell)
            exponents = {i for i in range(ell - 1)
                         if 6 * (2 * i - 1) % (ell - 1) == 0}
        else:
            exponents = set(range(ell - 1))
            if ell > 5:
                exponents = {i for i in exponents if
                             any((e * i) % (ell - 1) <= e
                                 for e in (1, 2, 3, 4, 6, 9, 12, 18))}

        for p in primes:
            if p == ell:
                continue
            if isqrt(4 * p**3) >= ell // 2:
                break
            exponents = {i for i in exponents if
                         possible_trace(i, ell, p) or possible_trace(i, ell, p**3)}
            if not exponents:
                break
        if exponents:
            survivors.append(ell)
    print("Primes >211 passing the 4p^3 quadratic-residue test:")
    print(", ".join(map(str, lower_candidates)))
    print("Primes passing the additional global-exponent trace test:")
    print(", ".join(map(str, survivors)))
    assert survivors == [2, 3, 5, 7, 11, 13, 19, 23, 29, 31, 37, 43, 59,
                         67, 83, 107, 139, 163, 211, 283, 307, 331, 379,
                         499, 547, 643, 883, 907, 4027]
    assert 4 * 138**6 < 30_000_000_000_000
    # exp(32)>30e12 follows from its positive Taylor expansion.
    from fractions import Fraction
    from math import factorial
    assert sum(Fraction(32**j, factorial(j)) for j in range(100)) > 30_000_000_000_000


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run Python with assertions enabled.")
    main()
