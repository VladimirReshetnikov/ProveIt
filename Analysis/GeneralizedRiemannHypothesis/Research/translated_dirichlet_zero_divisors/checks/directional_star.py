#!/usr/bin/env python3
"""Exact certificate for the signed multiplicity test at modulus 8.

Take the four primitive characters of conductors 1, 4, 8, 8, restricted
to odd integers. For every real contrast alpha of Euclidean norm one
and coordinate sum zero, certify a gap on each side of zero for the
limiting Hermitian matrix. All calculations use integers or fractions.
"""

from fractions import Fraction
from math import isqrt


RESIDUES = (1, 3, 5, 7)
# Columns are the characters 1, (-4/.), (8/.), and (-8/.).
ROWS = {
    1: (1, 1, 1, 1),
    3: (1, -1, -1, 1),
    5: (1, 1, -1, -1),
    7: (1, -1, 1, -1),
}
PRIME_LIMIT = 47


def dot(left, right):
    return sum(a * b for a, b in zip(left, right))


def check():
    for a in RESIDUES:
        for b in RESIDUES:
            # These orthogonal rows give sum_a |row(a).alpha|^2 = 4.
            assert dot(ROWS[a], ROWS[b]) == (4 if a == b else 0)
            assert ROWS[(a * b) % 8] == tuple(
                u * v for u, v in zip(ROWS[a], ROWS[b])
            )

    primes = [
        p for p in range(3, PRIME_LIMIT + 1, 2)
        if p % 8 != 1 and all(p % n for n in range(2, isqrt(p) + 1))
    ]
    lower_weights = {a: Fraction(0) for a in RESIDUES if a != 1}
    for p in primes:
        k = p.bit_length() - 1
        assert 2 ** k <= p < 2 ** (k + 1)
        # log(p)^2 / p >= (log 2)^2 * k^2 / p.
        lower_weights[p % 8] += Fraction(k * k, p)

    # Row 1 pairs to zero with a balanced contrast. Orthogonality gives
    # ||b||^2 > 4*(9/4)*(log 2)^2 for every unit balanced contrast.
    assert min(lower_weights.values()) > Fraction(9, 4)
    powers = (0, 2, 3, 3)  # conductors are powers of 2
    mean = Fraction(sum(powers), len(powers))
    centered = [k - mean for k in powers]
    assert dot(centered, centered) == 6
    # |c| <= sqrt(6) log 2 < (5/2) log 2.
    assert 6 < Fraction(5, 2) ** 2

    # In |a_0 + sum a_p p^(it)|^2, no distinct prime frequencies
    # couple to each other through an integer or its reciprocal.
    for p in primes:
        for q in primes:
            if p != q:
                ratio = Fraction(p, q)
                assert ratio.numerator > 1 and ratio.denominator > 1

    print('Primitive conductors 1, 4, 8, 8. Hardware-independent exact arithmetic.')
    print('Primes:', ' '.join(map(str, primes)))
    print('Lower bounds for sum (log(p)/log(2))^2/p in each residue class:')
    for a, lower in lower_weights.items():
        print(f'  {a} modulo 8: {lower} > 9/4')
    print('For every unit real contrast alpha with sum(alpha)=0:')
    print('  ||b|| > 3 log(2),  |c| <= sqrt(6) log(2).')
    print('  c + ||b|| > log(2)/2 and c - ||b|| < -log(2)/2.')
    print('Here c = sum alpha_j log(q_j) and b_p = log(p)/sqrt(p) sum alpha_j chi_j(p).')
    print('With the explicit-formula factor 1/(2 pi), both margins exceed log(2)/(4 pi).')


if __name__ == '__main__':
    check()
