"""Exact Euler-factor agreement at exponent seven, conductor dividing 29*43.

Run with Python 3. No external data or third-party packages are required.
Each vector (a,b) represents chi_29**a times chi_43**b. Here chi_l(t) is
zeta_7 raised to the discrete logarithm modulo l, reduced modulo seven.
"""

from collections import Counter
from fractions import Fraction
from math import gcd, isqrt


P = 7
MODULI = (29, 43)
Q = MODULI[0] * MODULI[1]
PRIME_LIMIT = 1_000_000

# In F_49=F_7[i], i^2=-1, A is the order-four subgroup <i> and B=(2+2i)A.
A = ((1, 0), (0, 1), (6, 0), (0, 6))
B = ((2, 2), (5, 2), (5, 5), (2, 5))


def logarithms(modulus):
    """Return the least primitive root and its discrete logarithm table mod p."""
    for base in range(2, modulus):
        table = {}
        value = 1
        while value not in table:
            table[value] = len(table) % P
            value = value * base % modulus
        if len(table) == modulus - 1:
            return base, table
    raise ValueError("No primitive root")


def histogram(packet, position):
    x, y = position
    return Counter((a * x + b * y) % P for a, b in packet)


def primes_up_to(limit):
    sieve = bytearray([1]) * (limit + 1)
    sieve[0:2] = bytes(2)
    for divisor in range(2, isqrt(limit) + 1):
        if sieve[divisor]:
            start = divisor * divisor
            sieve[start::divisor] = bytes((limit - start) // divisor + 1)
    return (n for n in range(2, limit + 1) if sieve[n])


def main():
    roots_and_logs = [logarithms(modulus) for modulus in MODULI]
    (g1, log1), (g2, log2) = roots_and_logs
    agree = {
        (x, y)
        for x in range(P)
        for y in range(P)
        if histogram(A, (x, y)) == histogram(B, (x, y))
    }
    projective_representatives = [(1, y) for y in range(P)] + [(0, 1)]
    good = [v for v in projective_representatives if v in agree]
    assert len(good) == 4 and len(agree) == 25

    classes = Counter()
    for unit in range(1, Q):
        if gcd(unit, Q) == 1:
            classes[log1[unit % 29], log2[unit % 43]] += 1
    assert len(classes) == P * P and set(classes.values()) == {24}
    total = sum(classes.values())
    matched = sum(classes[position] for position in agree)
    assert (matched, total - matched, total) == (600, 576, 1176)
    assert Fraction(total - matched, total) == Fraction(24, 49)

    counts = Counter()
    for prime in primes_up_to(PRIME_LIMIT):
        if prime not in MODULI:
            point = (log1[prime % 29], log2[prime % 43])
            counts[point in agree] += 1
    print(f"Primitive roots modulo 29 and 43: {g1}, {g2}")
    print(f"Good evaluation directions in projective coordinates: {good}")
    print(f"Agreeing/disagreeing evaluation vectors: {len(agree)}/{49-len(agree)}")
    print(f"Agreeing/disagreeing residue classes modulo {Q}: {matched}/{total-matched}")
    print(f"Exact disagreement density: {Fraction(total-matched, total)}")
    print(f"Primes up to {PRIME_LIMIT} excluding 29, 43: "
          f"{counts[True]} agreeing, {counts[False]} disagreeing")


if __name__ == "__main__":
    main()
