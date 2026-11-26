#!/usr/bin/env python3
"""Finite checks of the low-digit construction and one-prime optima."""
from fractions import Fraction
from itertools import combinations, product
from math import prod


def low_digit_cap(satellites):
    root = (1,) * satellites
    allowed = set(product((0, 1), repeat=satellites + 1))
    for marker in (0, 1):
        allowed.remove((marker,) + root)
    allowed.add((2,) + root)
    for q in range(satellites):
        row = list(root)
        row[q] = 2
        allowed.add((2, *row))
    return allowed


def check_cap(primes):
    cap = low_digit_cap(len(primes) - 1)
    for x, y in combinations(cap, 2):
        z = tuple((-a - b) % 3 for a, b in zip(x, y))
        assert z not in cap, (x, y, z)
    weights = [Fraction(1, p) for p in primes]
    cube = set(product((0, 1), repeat=len(primes)))
    def mass(rows):
        return sum(prod(u**a for u, a in zip(weights, row)) for row in rows)
    w, *sat = weights
    assert mass(cap) - mass(cube) == prod(sat) * (w*w*(1+sum(sat)) - 1 - w)
    return len(cap)


def check_one_prime(p, max_exponent):
    weights = [Fraction(1, p**a) for a in range(max_exponent + 1)]
    best = Fraction(0)
    for mask in range(1 << (max_exponent + 1)):
        exponents = {a for a in range(max_exponent + 1) if mask >> a & 1}
        if any(2*b-a in exponents for a, b in combinations(sorted(exponents), 2)):
            continue
        best = max(best, sum(weights[a] for a in exponents))
    def good(a):
        while a:
            a, digit = divmod(a, 3)
            if digit == 2:
                return False
        return True
    assert best == sum(weights[a] for a in range(max_exponent + 1) if good(a))
    return best


if __name__ == "__main__":
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23]
    for n in range(2, len(primes)+1):
        print(f"{n-1} satellites: {check_cap(primes[:n])} rows, no modular line, mass formula exact")
    for p in (2, 3, 5):
        print(f"p={p}, exponents 0..12: optimal unnormalized mass {check_one_prime(p, 12)}")
