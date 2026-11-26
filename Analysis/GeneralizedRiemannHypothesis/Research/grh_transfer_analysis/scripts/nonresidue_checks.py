#!/usr/bin/env python3
"""Exact finite checks relevant to LLS Corollary 1.1.

This does NOT prove GRH or an infinite nonresidue bound.  It verifies the
small-prime range 5 <= p < 3000 using exact integer and rational arithmetic.
For the logarithm, use log(y)=2 sum_{j>=0} t^(2j+1)/(2j+1), t=(y-1)/(y+1).
Positive partial sums give strict lower bounds when y>1.  Reduce p to
p=2^k*u, 1<=u<2, so every t is <=1/3 and only 24 terms are needed.
"""
from fractions import Fraction
import json
import math


def primes_below(limit):
    sieve = bytearray(b'\x01') * limit
    sieve[:2] = b'\x00\x00'
    for p in range(2, math.isqrt(limit - 1) + 1):
        if sieve[p]:
            for n in range(p * p, limit, p):
                sieve[n] = 0
    return [p for p in range(2, limit) if sieve[p]]


def log_lower(y, terms=24):
    y = Fraction(y)
    assert y >= 1
    t = (y - 1) / (y + 1)
    return 2 * sum((t ** (2 * j + 1) / (2 * j + 1)
                    for j in range(terms)), Fraction(0))


def main():
    log_two_lower = log_lower(2)
    rows = []
    for p in primes_below(3000):
        if p < 5:
            continue
        n = next(a for a in range(2, p)
                 if pow(a, (p - 1) // 2, p) == p - 1)
        # Euler's criterion and exhaustive smaller a certify minimality.
        assert all(pow(a, (p - 1) // 2, p) == 1 for a in range(1, n))
        k = p.bit_length() - 1
        lower = k * log_two_lower + log_lower(Fraction(p, 2 ** k))
        assert lower > 0 and lower * lower > n
        rows.append({'p': p, 'least_nonresidue': n,
                     'rational_log_lower_squared_exceeds_n': True})
    print(json.dumps({
        'claim_checked': 'n(p) < (log p)^2 for every prime 5 <= p < 3000',
        'arithmetic': 'exact integers and fractions; no floating-point decision',
        'method': 'Euler criterion plus 24 positive atanh-series terms after binary scaling',
        'prime_count': len(rows),
        'exception_p3': {'p': 3, 'least_nonresidue': 2},
        'infinite_claim_proved_by_this_script': False,
        'results': rows,
    }, indent=2))


if __name__ == '__main__':
    main()
