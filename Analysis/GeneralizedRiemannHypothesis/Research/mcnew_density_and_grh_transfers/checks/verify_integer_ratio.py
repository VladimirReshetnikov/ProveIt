"""Verify the integral-ratio construction, using Python integers only.

Run next to integral_ratio_support.txt. The output is a rigorous lower bound on the
ordinary density. The solver used to discover the witness is not required.
"""
from math import isqrt
from pathlib import Path

PRIMES = (2, 3, 5, 7, 11, 13, 17, 19)
SCALE = 10**18
CUTOFF = 200_000


def primes_up_to(n):
    sieve = bytearray(b'\x01') * (n + 1)
    sieve[:2] = b'\x00\x00'
    for p in range(2, isqrt(n) + 1):
        if sieve[p]:
            sieve[p * p::p] = bytes((n - p * p) // p + 1)
    return [p for p, prime in enumerate(sieve) if prime]


def smooth_values(limit):
    values = [1]
    for p in PRIMES:
        for copart in list(values):
            n = p * copart
            while n <= limit:
                values.append(n)
                n *= p
    return sorted(values)


def main():
    path = Path(__file__).with_name('integral_ratio_support.txt')
    terms = list(map(int, path.read_text().split()))
    support = set(terms)
    assert len(terms) == len(support) == 8197 and min(terms) == 1
    for n in terms:
        rest = n
        for p in PRIMES:
            while rest % p == 0:
                rest //= p
        assert rest == 1
    largest = max(terms)
    sorted_support = sorted(support)
    for ratio in smooth_values(isqrt(largest))[1:]:
        for a in sorted_support:
            if a * ratio * ratio > largest:
                break
            assert a * ratio not in support or a * ratio * ratio not in support

    # A lower sum for the weights of the supported components at primes in P.
    bound = sum(SCALE // n for n in support)
    for p in PRIMES:
        bound = bound * (p - 1) // p
    # At an outside prime the exact factor is (1-p^-2) prod_{j>=1}(1+p^(-3^j)).
    for p in primes_up_to(CUTOFF):
        if p not in PRIMES:
            bound = bound * (p*p - 1) * (p**3 + 1) // (p**5)
    # prod_{p>B}(1-p^-2) >= prod_{n>B}(1-n^-2) = B/(B+1).
    bound = bound * CUTOFF // (CUTOFF + 1)
    print(f'{len(support)} smooth integers, maximum {largest}')
    print(f'No integer-ratio progression, density at least {bound // SCALE}.{bound % SCALE:018d}')
    assert bound > 72388 * (SCALE // 100000)


if __name__ == '__main__':
    main()
