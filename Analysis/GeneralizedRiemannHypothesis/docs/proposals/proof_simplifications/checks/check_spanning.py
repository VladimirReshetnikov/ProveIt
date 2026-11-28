#!/usr/bin/env python3
"""Exact checks for the affine rank recurrence and the sharp-order example.

Uses only Python's standard library. A coordinate subspace is a bit mask.
Enumerating all 1,024 coordinate subspaces of the target avoids dependence
on any one greedy path. The proof in the paper handles arbitrary subspaces.
"""
from fractions import Fraction
from itertools import combinations
from math import comb


def subsets_with_point_masks(n, k):
    coordinates = list(combinations(range(n), k))
    return [
        sum(1 << i for i, entry in enumerate(coordinates) if point in entry)
        for point in range(n)
    ]


def affine_step_check():
    n, k = 5, 2
    d, h = comb(n, k), comb(n - 1, k - 1)
    full_images = subsets_with_point_masks(n, k)
    restricted = {
        mask ^ (1 << i)
        for mask in full_images for i in range(d) if mask & (1 << i)
    }
    r = h - 1
    t = Fraction(h, 2 * d)
    tau = Fraction(h - r, h)
    fixed_point = 2 * tau
    mean_overlap = Fraction(
        sum((mask & full_images[0]).bit_count() for mask in full_images), n
    )
    assert mean_overlap == Fraction(h * h, d)
    for occupied in range(1 << d):
        c = d - occupied.bit_count()
        best_gain = max((mask & ~occupied).bit_count() for mask in restricted)
        missing_next = Fraction(c - best_gain, d)
        assert missing_next <= (1 - t) * Fraction(c, d) + t * fixed_point

    occupied = 0
    for steps in range(n + 1):
        missing = Fraction(d - occupied.bit_count(), d)
        assert missing <= fixed_point + (1 - fixed_point) * (1 - t) ** steps
        best = max(restricted, key=lambda entry: (entry & ~occupied).bit_count())
        occupied |= best
    assert occupied.bit_count() == d
    print(f"Affine step holds on all {1 << d} coordinate subspaces (h={h}, r={r}, d={d}).")


def incidence_check():
    for n in range(3, 11):
        for k in range(1, n):
            images = subsets_with_point_masks(n, k)
            d = comb(n, k)
            h = comb(n - 1, k - 1)
            assert Fraction(h, d) == Fraction(k, n)
            occupied = 0
            for j in range(n + 1):
                assert d - occupied.bit_count() == comb(n - j, k)
                if j < n:
                    occupied |= images[j]
    print("Binomial uncovered-coordinate formula holds for every 3 <= N <= 10, 1 <= k < N.")


def constants_check():
    for b in range(8, 201):
        epsilon = Fraction(9, b**4)
        tau = Fraction(1, b**8)
        missing = 3 * epsilon + 2 * tau + Fraction(1, b**5)
        separate_errors = Fraction(19, b**4) + 2 * tau + Fraction(1, b**5)
        assert separate_errors <= Fraction(20, b**4) <= Fraction(4, b**2)
        assert missing <= Fraction(29, b**4) <= Fraction(4, b**2)
        assert 1 - Fraction(5, b**4) >= Fraction(1, 2)
    print("Exact codimension and dimension comparisons hold at each integer 8 <= b <= 200.")


if __name__ == "__main__":
    affine_step_check()
    incidence_check()
    constants_check()
