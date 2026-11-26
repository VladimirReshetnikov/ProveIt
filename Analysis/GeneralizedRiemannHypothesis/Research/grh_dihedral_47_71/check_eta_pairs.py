"""Verify the finite Hecke obstructions among normalized pairs summing to 24."""
from collections import Counter
from fractions import Fraction
from math import gcd


def expansion(a, b, last):
    powers = [0, 1] + [0] * (last - 1)
    # The eta product starts with q. Multiply by both sets of Euler factors.
    for step in (a, b):
        for exponent in range(step, last, step):
            for j in range(last, exponent - 1, -1):
                powers[j] -= powers[j - exponent]
    return powers


def main():
    # The seven positive cases are given by a published eigenform theorem.
    known = {1, 2, 3, 5, 7, 11, 23}
    failures = Counter()
    for a in range(1, 13):
        b = 24 - a
        ratio = Fraction(b, a)
        if ratio in known:
            print(f"({a:2}, {b:2}) ratio {ratio}: listed eigenform")
            continue
        coeffs = expansion(a, b, 9)
        for p in (2, 3):
            if gcd(p, a * b) == 1 and coeffs[p] == coeffs[p*p] == 0:
                failures[p] += 1
                print(f"({a:2}, {b:2}) ratio {ratio}: obstruction at {p}")
                break
        else:
            raise AssertionError((a, b))
    assert failures == {2: 4, 3: 1}


if __name__ == "__main__":
    main()
