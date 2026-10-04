#!/usr/bin/env python3
"""Exact finite checks of the ordinal-sequence code's rational formulas.

This is an auxiliary check of Section 5, not a formal proof. Integers
stand in for finite ordinals only; no computation here implements the
surreal omega map, infinite Hahn sums, or arbitrary ordinals.
"""

from fractions import Fraction


def slot(index: int, value: int) -> Fraction:
    q = Fraction(1, 2 ** (index + 1))
    return q + q * Fraction(value, 4 * (value + 1))


def main() -> None:
    values = (*range(65), 127, 1024, 10**6, 10**30)
    indices = range(16)
    inverse_checks = 0
    ordering_checks = 0

    for n in indices:
        q = Fraction(1, 2 ** (n + 1))
        for a in values:
            exponent = slot(n, a)
            assert q <= exponent < Fraction(5, 4) * q
            assert 0 < exponent < 1
            decoded_u = 4 * (exponent / q - 1)
            assert 0 <= decoded_u < 1
            assert decoded_u / (1 - decoded_u) == a
            inverse_checks += 1

            for b in values:
                next_exponent = slot(n + 1, b)
                # This checks adjacent slots independently of the order
                # of the encoded values a and b.
                assert next_exponent < Fraction(5, 8) * q < exponent
                ordering_checks += 1

    print(f"PASS: {inverse_checks} exact slot-bound and inverse checks")
    print(f"PASS: {ordering_checks} exact adjacent-slot order checks")
    print("Scope: finite natural-number inputs only; see the article for proofs.")


if __name__ == "__main__":
    main()

