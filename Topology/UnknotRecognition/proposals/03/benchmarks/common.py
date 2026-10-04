"""Deterministic diagram families shared by tests and benchmarks."""
from __future__ import annotations


def connected_sum(a, b, Diagram):
    if not a.crossings:
        return b
    if not b.crossings:
        return a
    # Cut edge 0 of each diagram; cross-connect the two pairs of free ends.
    left = [list(row) for row in a.pd]
    shift = 2 * a.crossings
    right = [[e + shift for e in row] for row in b.pd]
    occurrences = [(row, j) for row in right for j, e in enumerate(row) if e == shift]
    left_occ = [(row, j) for row in left for j, e in enumerate(row) if e == 0]
    occurrences[0][0][occurrences[0][1]] = 0
    left_occ[1][0][left_occ[1][1]] = shift
    return Diagram.from_pd(left + right)


def sum_family(k, Diagram, trefoil=True):
    block = Diagram.from_braid(2, [1] * (3 if trefoil else 1))
    result = Diagram.from_pd([])
    for _ in range(k):
        result = connected_sum(result, block, Diagram)
    return result
