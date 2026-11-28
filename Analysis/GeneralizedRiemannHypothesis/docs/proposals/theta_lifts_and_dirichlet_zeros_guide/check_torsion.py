#!/usr/bin/env python3
"""Verify the torsion-point example exactly in cyclotomic fields, using integer coefficients."""
from fractions import Fraction
from math import comb, gcd


def shifted_cyclotomic(k, j):
    """Coefficients of Φ_(3^k)((1+T)^j), returned in ascending order."""
    n = 3 ** (k - 1) * j
    return [int(a == 0) + (comb(n, a) if a <= n else 0) + comb(2 * n, a)
            for a in range(2 * n + 1)]


def remainder(poly, monic):
    """Compute the remainder of poly by a monic integer polynomial."""
    assert monic[-1] == 1
    rem = poly.copy()
    while len(rem) >= len(monic):
        leading = rem[-1]
        shift = len(rem) - len(monic)
        for a, c in enumerate(monic):
            rem[a + shift] -= leading * c
        rem.pop()
    return rem


def ord3(n):
    assert n
    e = 0
    while n % 3 == 0:
        n //= 3
        e += 1
    return e


def evaluated_valuation(h, j, k):
    # T = ζ_(3^h) - 1 is a uniformizer. In the standard basis the
    # valuations of nonzero terms have different fractional parts.
    minimal = shifted_cyclotomic(h, 1)
    coeffs = remainder(shifted_cyclotomic(k, j), minimal)
    degree = len(minimal) - 1
    return min((ord3(c) + Fraction(a, degree) for a, c in enumerate(coeffs) if c),
               default=None)


def main():
    assert evaluated_valuation(2, 1, 2) is None
    assert evaluated_valuation(3, 3, 2) is None
    rows = [(81 // gcd(j, 81), evaluated_valuation(4, j, 1), evaluated_valuation(4, j, 2))
            for j in (1, 2, 3)]
    assert rows == [(81, Fraction(1, 27), Fraction(1, 9)),
                    (81, Fraction(1, 27), Fraction(1, 9)),
                    (27, Fraction(1, 9), Fraction(1, 3))]
    print("Matched two vanishing tests and the six finite valuations at order 81.")


if __name__ == "__main__":
    main()
