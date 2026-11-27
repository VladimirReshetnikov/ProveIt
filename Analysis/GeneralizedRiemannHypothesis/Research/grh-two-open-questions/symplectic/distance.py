#!/usr/bin/env python3
"""Exact total variation distance for a nondegenerate symplectic compression.

Example: python distance.py 2 6 4 10
Arguments: field order q (a prime power), target dimension a, source
dimension b, and ambient dimension 2n. All dimensions are even.
"""
import argparse
from fractions import Fraction
from math import prod


def rank_law(q, a, b):
    """Half-rank probabilities of the residual of a uniform a by b matrix."""
    if q < 2 or min(a, b) <= 0 or a % 2 or b % 2:
        raise ValueError("q must be at least two, with positive even a and b")
    h = b // 2
    inverse = Fraction(1, q)
    up, down = [], []
    for i in range(h + 1):
        e = b - 2 * i
        up.append((1 - inverse ** e) * (1 - inverse ** (e - 1)))
        down.append(inverse ** (2 * e + 1) * (1 - inverse ** (2 * i)))
    mass = [Fraction(0)] * h + [Fraction(1)]
    for _ in range(a // 2):
        updated = [p * (1 - up[i] - down[i]) for i, p in enumerate(mass)]
        for i in range(h):
            updated[i + 1] += mass[i] * up[i]
            updated[i] += mass[i + 1] * down[i + 1]
        mass = updated
    return mass


def distance(q, a, b, ambient):
    if ambient < max(a, b) or ambient % 2:
        raise ValueError("ambient dimension must be even and contain both frames")
    mass = rank_law(q, a, b)
    h = b // 2
    c = (ambient - a) // 2
    if c < h:
        return sum(mass[c + 1:])
    s = c - h
    inverse = Fraction(1, q)
    alpha = prod((1 - inverse ** (2 * (s + i))) /
                 (1 - inverse ** (a + 2 * (s + i))) for i in range(1, h + 1))
    return (1 - alpha) * mass[h]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("q", "a", "b", "ambient"):
        parser.add_argument(name, type=int)
    args = parser.parse_args()
    value = distance(args.q, args.a, args.b, args.ambient)
    print(value)
    print(f"{float(value):.12g}")
