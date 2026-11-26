#!/usr/bin/env python3
"""Check the integer boundary cases of the sharp selection threshold."""
from fractions import Fraction
from check_minimax import least_blocking_m, phi_power


def critical_h(p, epsilon):
    h = 2
    while Fraction(1, p ** (h - 1)) > epsilon:
        h += 1
    return h


def first_good(p, threshold, tolerance):
    total = Fraction()
    h = 0
    while total <= threshold:
        h += 1
        total += Fraction(least_blocking_m(p, h, tolerance), phi_power(p, h))
    return h


def main():
    tested = 0
    for p in (2, 3, 5, 7):
        threshold = Fraction(p, p - 1)
        for denominator in range(2, 81):
            for numerator in range(1, denominator):
                tolerance = Fraction(numerator, denominator)
                expected = critical_h(p, tolerance) + int(p == 2)
                observed = first_good(p, threshold, tolerance)
                assert observed == expected, (p, tolerance, expected, observed)
                tested += 1
        for h in range(1, 15):
            count = least_blocking_m(p, h, 0)
            assert count == p - 1
    print(f"Critical-budget cutoff checked at {tested} parameter triples.")
    print("Zero-tolerance shell costs checked at 56 parameter pairs.")


if __name__ == "__main__":
    main()
