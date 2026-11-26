#!/usr/bin/env python3
"""Finite checks for polynomial progressions in products of finite fields.

Python standard library.  Polynomials below are coefficient words represented
in base q, with the constant coefficient as the least significant digit.
The shift by x is integer multiplication by q regardless of the field model.
"""
from fractions import Fraction
from itertools import combinations, product
from math import prod


def partition(q, n):
    """Build complete x-orbit triples and verify the finite counting formula."""
    size = q ** (n + 1)
    assigned = set()
    triples = []
    for seed in range(1, size):
        if seed % q == 0:
            continue
        low = seed
        while low * q**2 < size:
            cells = (low, q * low, q**2 * low)
            assert len(set(cells)) == 3 and assigned.isdisjoint(cells)
            assigned.update(cells)
            triples.append(cells)
            low *= q**3
    count = sum((q - 1) * q ** (n - e - 2) for e in range(0, n - 1, 3))
    assert len(triples) == count
    return triples


def check_lines():
    fields = [2, 3, 4]
    cutoffs = [5, 4, 4]
    cells = [partition(q, n)[-1] for q, n in zip(fields, cutoffs)]
    coordinates = tuple(range(len(fields)))
    line_count = 0
    for k in range(1, len(fields) + 1):
        for moving in combinations(coordinates, k):
            fixed = [i for i in coordinates if i not in moving]
            for letters in product(range(3), repeat=len(fixed)):
                base = dict(zip(fixed, letters))
                points = [tuple(cells[i][base[i] if i in base else a]
                                for i in coordinates) for a in range(3)]
                assert len(set(points)) == 3
                for left, right in zip(points, points[1:]):
                    assert right == tuple(left[i] * (fields[i] if i in moving else 1)
                                          for i in coordinates)
                line_count += 1
    assert line_count == (4**len(fields) - 3**len(fields))
    return line_count


def upper_bound(fields):
    """Use exact c_{k,3} for 0<=k<=6 and slicing at k=6 above it.

    D.H.J. Polymath, Density Hales-Jewett and Moser numbers, arXiv:1002.0374.
    """
    counts = [1, 2, 6, 18, 52, 150, 450]
    masses = [Fraction(1)]
    for q in fields:
        theta = Fraction(3, q**2 + q + 1)
        nxt = [Fraction(0)] * (len(masses) + 1)
        for k, mass in enumerate(masses):
            nxt[k] += mass * (1 - theta)
            nxt[k + 1] += mass * theta
        masses = nxt
    assert sum(masses) == 1
    return sum(mass * Fraction(counts[min(k, 6)], 3**min(k, 6))
               for k, mass in enumerate(masses))


def main():
    for q in (2, 3, 4, 5):
        for n in range(7):
            partition(q, n)
    print("Disjoint triples and exact counts passed for q=2,3,4,5 and 0<=n<=6.")
    print(f"All {check_lines()} combinatorial lines in a ternary 3-cube passed.")
    print("For each row, L <= Delta <= U. Quotients are exact.")
    for fields in ([2], [2, 2], [2, 3, 5], [2]*4, [2]*8):
        lower = prod(1 - Fraction(1, q**2) for q in fields)
        upper = upper_bound(fields)
        assert lower <= upper <= 1
        print(f"q={','.join(map(str,fields))}: L={lower}, U={upper}, "
              f"decimal interval [{float(lower):.9f}, {float(upper):.9f}]")


if __name__ == "__main__":
    main()
