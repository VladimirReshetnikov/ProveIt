"""Compute the cubic-field test as rational coefficients of log(p).

With no arguments, check the unramified splitting rules against direct root
counts for small primes, print two finite examples, and verify the rational
rounding used in the simplicity-defect bound. Python 3 standard library.
"""

import argparse
from fractions import Fraction
from math import fsum, isqrt, log


def primes_through(limit):
    sieve = bytearray(b'\x01') * (limit + 1)
    sieve[:2] = b'\x00\x00'
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            count = (limit - p * p) // p + 1
            sieve[p * p::p] = b'\x00' * count
    return [p for p in range(2, limit + 1) if sieve[p]]


def cubic_degrees(p):
    """Residue degrees, with each prime ideal appearing once, for Q(cuberoot(2))."""
    if p in (2, 3):
        return (1,)
    if p % 3 == 2:
        return (1, 2)
    if pow(2, (p - 1) // 3, p) == 1:
        return (1, 1, 1)
    return (3,)


def ramp_coefficient(p, cutoff):
    degrees = cubic_degrees(p)
    power, exponent = p, 1
    total = Fraction(0)
    while power <= cutoff:
        weight = sum(f for f in degrees if exponent % f == 0)
        total += weight * (Fraction(1, power) - Fraction(1, cutoff))
        power *= p
        exponent += 1
    return total


def difference(m, k):
    """Return D_k(m) exactly as a dictionary of coefficients of log(prime)."""
    if min(m, k) < 1:
        raise ValueError('m and k must be positive integers')
    lower, upper = m**k, (2*m)**k
    terms = {}
    for p in primes_through(upper):
        coefficient = ramp_coefficient(p, lower) - ramp_coefficient(p, upper)
        if p == 2:
            coefficient += k
        if coefficient:
            terms[p] = coefficient
    return terms


def check_rounding():
    # A rational Taylor lower bound proves exp(28.73)>H, so log H<28.73.
    height = 3 * 10**12
    log_upper = Fraction(2873, 100)
    term = Fraction(1)
    exp_lower = term
    for j in range(1, 100):
        term *= log_upper / j
        exp_lower += term
    assert exp_lower > height
    upper = (log_upper**2/3 + 2*log_upper/9 + Fraction(2, 27)) * Fraction(16, height**3)
    assert upper < Fraction(167, 10**36)
    print('PASS: rational arithmetic proves the analytic tail bound is below 1.67e-34.')


def print_example(m, k):
    terms = difference(m, k)
    print(f'm={m}, k={k}, rational coefficients of log(p):')
    print(' '.join(f'{p}={c}' for p, c in terms.items()))
    print('D_k(m) (floating-point display):', format(fsum(float(c)*log(p) for p, c in terms.items()), '.12g'))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cubic', nargs=2, type=int, metavar=('M', 'K'))
    args = parser.parse_args()
    if args.cubic:
        print_example(*args.cubic)
        return
    checked = 0
    for p in primes_through(499):
        if p in (2, 3):
            continue
        roots = sum(pow(a, 3, p) == 2 % p for a in range(p))
        assert roots == cubic_degrees(p).count(1)
        checked += 1
    assert difference(1, 1) == {2: Fraction(1)}
    assert difference(2, 1) == {2: Fraction(3, 4), 3: Fraction(-1, 12)}
    print(f'PASS: residue degrees match brute-force root counts for {checked} unramified primes.')
    check_rounding()
    print_example(2, 1)
    print_example(2, 2)


if __name__ == '__main__':
    main()
