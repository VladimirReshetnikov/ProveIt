"""Finite-net values of inf_{a,b,c} sup_x min(d(x,a),d(x,b),d(x,c)).

Compares independent exhaustive minimax evaluation against the block-cover
formula. All distances in the computation are integer grid steps.
"""
from fractions import Fraction
from itertools import combinations_with_replacement


def exhaustive(intervals: int, centres: int) -> tuple[int, tuple[int, ...]]:
    grid = range(intervals + 1)
    return min(
        (max(min(abs(x - c) for c in candidate) for x in grid), candidate)
        for candidate in combinations_with_replacement(grid, centres)
    )


def block_radius(intervals: int, centres: int) -> int:
    shortage = max(intervals + 1 - centres, 0)
    return (shortage + 2 * centres - 1) // (2 * centres)


if __name__ == "__main__":
    print("intervals | first optimal triple (grid units) | minimax value")
    for intervals in (1, 2, 4, 8, 16, 32):
        radius, witness = exhaustive(intervals, 3)
        assert radius == block_radius(intervals, 3)
        print(f"{intervals:9} | {str(witness):32} | {Fraction(radius, intervals)}")
