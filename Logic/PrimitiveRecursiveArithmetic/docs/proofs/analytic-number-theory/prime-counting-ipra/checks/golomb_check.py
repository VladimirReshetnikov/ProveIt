#!/usr/bin/env python3
"""Check all solutions of x = k*pi(x), x >= 2, for k from 2 to 7.

The wheel bound in the paper proves completeness beyond each finite interval.
Only Python's standard library is required.
"""
from fractions import Fraction
from math import isqrt

# k: (number of sieving primes, first excluded bound, all solutions)
CASES = {
    2: (2, 25, (2, 4, 6, 8)),
    3: (3, 106, (27, 30, 33)),
    4: (5, 498, (96, 100, 120)),
    5: (7, 3646, (330, 335, 340, 350, 355, 360)),
    6: (10, 59867, (1008, 1080, 1092, 1116, 1122, 1128, 1134)),
    7: (15, 3948665, (3059, 3066, 3073, 3080, 3087, 3094)),
}


def prime_flags(limit):
    flags = bytearray([1]) * (limit + 1)
    flags[:2] = b'\x00\x00'
    for p in range(2, isqrt(limit) + 1):
        if flags[p]:
            count = (limit - p*p) // p + 1
            flags[p*p::p] = bytes(count)
    return flags


def check():
    flags = prime_flags(max(bound for _, bound, _ in CASES.values()))
    primes = [p for p in range(2, 48) if flags[p]]

    for k, (a, bound, _) in CASES.items():
        density = Fraction(1)
        for p in primes[:a]:
            density *= Fraction(p - 1, p)
        if len(primes) < a or not 0 < k*density < 1:
            raise ValueError(f"invalid wheel for k={k}")
        threshold = k * (a + 2**(a - 1)) / (1 - k*density)
        if threshold.numerator // threshold.denominator + 1 != bound:
            raise ValueError(f"wrong cutoff for k={k}")

    found = {k: [] for k in CASES}
    pi = 0
    for x in range(2, len(flags)):
        pi += flags[x]
        k, remainder = divmod(x, pi)
        if remainder == 0 and k in found:
            found[k].append(x)
    for k, (_, bound, expected) in CASES.items():
        if tuple(found[k]) != expected:
            raise ValueError(f"wrong list for k={k}: {found[k]}")
        print(f"k={k}  cutoff={bound}  values={', '.join(map(str, found[k]))}")


if __name__ == '__main__':
    check()
