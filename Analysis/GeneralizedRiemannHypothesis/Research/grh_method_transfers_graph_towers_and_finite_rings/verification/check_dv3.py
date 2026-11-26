#!/usr/bin/env python3
"""Compute Example 3 shell contributions without numeric approximations or dependencies."""
from collections import Counter
from math import comb

STEPS = ((1, 5), (0, 3), (1, 2), (0, 1))


def direction_order(s, a, b):
    """Return e * v_2(F(zeta**a, zeta**b)), where zeta has order 2**s."""
    e = 2 ** (s - 1)
    coefficients = [0] * e
    coefficients[0] = 2 * len(STEPS)
    for u, v in STEPS:
        power = a * u + b * v
        for signed_power in (power, -power):
            residue = signed_power % (2 * e)
            coefficients[residue % e] -= 1 if residue < e else -1
    # zeta**e = -1.  Write the reduced representative in powers of pi = zeta-1.
    nonzero = [(i, c) for i, c in enumerate(coefficients) if c]
    best = None
    for j in range(e):
        if best is not None and j >= best:
            break
        coefficient = sum(c * comb(i, j) for i, c in nonzero if i >= j)
        if coefficient:
            v2 = (abs(coefficient) & -abs(coefficient)).bit_length() - 1
            order = j + e * v2
            best = order if best is None else min(best, order)
    # Orders are pairwise distinct modulo e, so the minimum is exact.
    assert best is not None
    return best


def shell(s):
    modulus = 2 ** s
    # One representative of each Galois orbit. Each orbit has size modulus/2.
    directions = [(a, 1) for a in range(modulus)]
    directions += [(1, b) for b in range(0, modulus, 2)]
    return Counter(direction_order(s, a, b) for a, b in directions)


if __name__ == '__main__':
    tree_order = 0
    for s in range(1, 13):
        target = (5, 19, 65)[s - 1] if s < 4 else (4*s + 33)*2**(s-2) - 4*s - 1
        histogram = shell(s)
        weight = sum(order * count for order, count in histogram.items())
        tree_order += weight - 2
        assert tree_order == target
        print(f's={s}  orders={sorted(histogram.items())}  shell={weight}  tree={tree_order}')
