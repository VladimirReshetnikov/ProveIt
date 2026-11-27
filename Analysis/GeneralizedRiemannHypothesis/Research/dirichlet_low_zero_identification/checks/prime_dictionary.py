#!/usr/bin/env python3
"""Check a three-prime measuring set for every character modulo 101.

Only integer arithmetic is used, including outward rounding to denominator
10^7. The log-window has h=1/8 and |K(v)|<=min(1,64/(R v)^2).
"""
from bisect import bisect_left, bisect_right
from math import isqrt

X = 10_000
R = 80_000
MODULUS = 101
DICTIONARY = (11_197, 14_107, 11_027)
DENOMINATOR = 10_000_000


def sieve(limit):
    is_prime = bytearray(b'\1') * (limit+1)
    is_prime[:2] = b'\0\0'
    for d in range(2, isqrt(limit)+1):
        if is_prime[d]:
            is_prime[d*d::d] = b'\0' * len(is_prime[d*d::d])
    powers = []
    for p in range(2, limit+1):
        if is_prime[p]:
            n = p
            while n <= limit:
                powers.append(n)
                n *= p
    return is_prime, sorted(powers)


def leakage_upper(p, powers):
    # exp(-1/8)>4/5 and exp(1/8)<5/4. For n in the expanded box,
    # Lambda(n)*sqrt(p/n)/log(p)<=2 and |log(n/p)|>=|n-p|/max(n,p).
    first = bisect_left(powers, (4*p+4)//5)
    last = bisect_right(powers, 5*p//4)
    total = 0
    for n in powers[first:last]:
        if n == p:
            continue
        denominator = (R*(n-p))**2
        numerator = 128 * max(n,p)**2 * DENOMINATOR
        rounded = (numerator + denominator-1)//denominator
        total += min(2*DENOMINATOR, rounded)
    return total


def verify():
    primes, powers = sieve(5*X//2)
    exponent = {pow(2, j, MODULUS): j for j in range(MODULUS-1)}
    assert primes[MODULUS] and len(exponent) == MODULUS-1
    unresolved = set(range(1, MODULUS-1))
    print(f'X={X}, R={R}, h=1/8, q={MODULUS}; 2 generates the units modulo q.')
    print('p      ind_2(p)    certified leakage <=      newly separated differences')
    for p in DICTIONARY:
        assert X <= p <= 2*X and primes[p]
        bound = leakage_upper(p, powers)
        assert 16*bound < DENOMINATOR
        j = exponent[p % MODULUS]
        # |1-exp(2 pi i k j/100)|>=1 iff (k j mod 100)/100 is in [1/6,5/6].
        covered = {k for k in unresolved if 100 <= 6*((k*j) % 100) <= 500}
        unresolved -= covered
        print(f'{p:5}     {j:2}            {bound}/{DENOMINATOR}                  {len(covered)}')
    assert not unresolved
    print('All 99 nonzero character-exponent differences are separated by chord >= 1.')
    print('Each individual normalized prime-power leakage is < 1/16.')


if __name__ == '__main__':
    verify()
