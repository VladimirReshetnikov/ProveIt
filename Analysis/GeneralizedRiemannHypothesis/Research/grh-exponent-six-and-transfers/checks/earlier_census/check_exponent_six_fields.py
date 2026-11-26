#!/usr/bin/env python3
"""Compute all fundamental discriminants of exponent 6 up to the largest EKN example."""
from collections import Counter
import csv
from math import gcd, isqrt
import sys

from check_exponent_five import fundamental_discriminants, power_is_principal

LIMIT = 5761140


def prime_test_data():
    """At an odd split prime use a form of leading coefficient p as a witness."""
    primes = [n for n in range(3, 101, 2)
              if all(n % k for k in range(2, isqrt(n) + 1))]
    return [(p, {r*r % p: r for r in range(1, p)}, 4*p**6) for p in primes]


def possible_exponent_six(d, tests):
    if (-d) % 8 == 1 and 4*2**6 < d:
        return False
    for p, roots, norm_cutoff in tests:
        b = roots.get(-d % p)
        if b is None:
            continue
        if norm_cutoff < d:
            return False
        if (b - d) % 2:
            b += p
        c = (b*b + d) // (4*p)
        if not power_is_principal((p, b, c), 6):
            return False
    return True


def reduced_forms(d):
    for a in range(1, isqrt(d//3) + 1):
        for b in range(1 - a + (d - (1-a)) % 2, a+1, 2):
            c, remainder = divmod(b*b+d, 4*a)
            if remainder == 0 and c >= a and (a < c or b >= 0) and gcd(a,gcd(b,c)) == 1:
                yield a,b,c


def distinct_primes(n):
    res = []
    divisor = 2
    while divisor*divisor <= n:
        if n % divisor == 0:
            res.append(divisor)
            while n % divisor == 0:
                n //= divisor
        divisor += 1
    if n > 1:
        res.append(n)
    return res


def main():
    tests = prime_test_data()
    frequencies = Counter()
    remaining = 0
    max_cofactor = 0
    maximum = 0
    out = csv.writer(sys.stdout, lineterminator='\n')
    out.writerow(['fundamental_discriminant','class_number','exponent','distinct_prime_factors','largest_prime_factor','cofactor'])
    for d in sorted(fundamental_discriminants(LIMIT)):
        if not possible_exponent_six(d, tests):
            continue
        remaining += 1
        forms = list(reduced_forms(d))
        # Cauchy's theorem: if the exponent divides 6 and 6|h then the
        # exponent is 6. Check every ideal class for the exponent bound.
        if len(forms) % 6 or not all(power_is_principal(f, 6) for f in forms):
            continue
        primes = distinct_primes(d)
        frequencies[len(primes)] += 1
        max_cofactor = max(max_cofactor, d//primes[-1])
        maximum = d
        out.writerow([-d,len(forms),6,len(primes),primes[-1],d//primes[-1]])
    assert sum(frequencies.values()) == 432 and maximum == LIMIT
    print(f'{remaining} survived the small-prime tests; {sum(frequencies.values())} fields of exponent 6. '
          f'Largest |D|={maximum}, largest cofactor={max_cofactor}. '
          f'Counts by number of prime factors: {sorted(frequencies.items())}', file=sys.stderr)


if __name__ == '__main__':
    main()
