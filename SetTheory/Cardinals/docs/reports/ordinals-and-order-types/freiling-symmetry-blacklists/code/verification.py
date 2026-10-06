#!/usr/bin/env python3
"""Finite checks for the sparse symmetry-avoidance report.

The exhaustive part enumerates all 1-bounded blacklist systems on n <= 7
vertices (n^n systems before conflict-graph deduplication) and checks the
reported minima.  It also verifies the 40 critical systems at (k,r,n)=(1,3,6).

No third-party packages are required.
"""

from __future__ import annotations

from itertools import combinations, product
from math import comb
from typing import Iterable, Optional, Sequence


def pair_index(n: int) -> dict[tuple[int, int], int]:
    out: dict[tuple[int, int], int] = {}
    bit = 0
    for i in range(n):
        for j in range(i + 1, n):
            out[(i, j)] = bit
            bit += 1
    return out


def conflict_mask(F: Sequence[Optional[int]], n: int) -> int:
    idx = pair_index(n)
    mask = 0
    for i, j in enumerate(F):
        if j is None:
            continue
        a, b = sorted((i, j))
        mask |= 1 << idx[(a, b)]
    return mask


def adjacency(mask: int, n: int) -> list[int]:
    adj = [0] * n
    bit = 0
    for i in range(n):
        for j in range(i + 1, n):
            if (mask >> bit) & 1:
                adj[i] |= 1 << j
                adj[j] |= 1 << i
            bit += 1
    return adj


def independent_counts(mask: int, n: int) -> list[int]:
    adj = adjacency(mask, n)
    counts = [0] * (n + 1)
    for subset in range(1 << n):
        remaining = subset
        independent = True
        while remaining:
            low = remaining & -remaining
            v = low.bit_length() - 1
            if adj[v] & (subset ^ low):
                independent = False
                break
            remaining ^= low
        if independent:
            counts[subset.bit_count()] += 1
    return counts


def systems_k1(n: int) -> Iterable[tuple[Optional[int], ...]]:
    choices = [[None] + [j for j in range(n) if j != i] for i in range(n)]
    return product(*choices)


def exhaustive_minima_k1(n: int) -> tuple[int, list[int]]:
    graphs = {conflict_mask(F, n) for F in systems_k1(n)}
    minima = [10**100] * (n + 1)
    for mask in graphs:
        counts = independent_counts(mask, n)
        minima = [min(a, b) for a, b in zip(minima, counts)]
    return len(graphs), minima


def exact_pairs(n: int, k: int) -> int:
    return max(0, comb(n, 2) - k * n)


def triple_correction_k1(n: int) -> int:
    a, rem = divmod(n, 3)
    if rem == 0:
        return 2 * a
    if rem == 1:
        return 2 * a + 2
    return 2 * a + 3


def exact_triples_k1(n: int) -> int:
    if n < 3:
        return 0
    return comb(n, 3) - n * (n - 2) + triple_correction_k1(n)


def has_independent_r(F: Sequence[Optional[int]], n: int, r: int) -> bool:
    adj = adjacency(conflict_mask(F, n), n)
    for vertices in combinations(range(n), r):
        if all((adj[i] >> j) & 1 == 0 for i, j in combinations(vertices, 2)):
            return True
    return False


def critical_count_k1_n6_r3() -> int:
    return sum(not has_independent_r(F, 6, 3) for F in systems_k1(6))


def regular_tournament_count(q: int) -> int:
    edges = list(combinations(range(q), 2))
    target = (q - 1) // 2
    total = 0
    for orientation in range(1 << len(edges)):
        outdegree = [0] * q
        for bit, (i, j) in enumerate(edges):
            if (orientation >> bit) & 1:
                outdegree[i] += 1
            else:
                outdegree[j] += 1
        if all(d == target for d in outdegree):
            total += 1
    return total


def main() -> None:
    print("Exhaustive minima for k=1")
    print("n  distinct conflict graphs  A_2  A_3  alpha_min")
    for n in range(1, 8):
        graph_count, minima = exhaustive_minima_k1(n)
        guaranteed_alpha = max(r for r, count in enumerate(minima) if count > 0)
        # Directly, the largest independent-set size guaranteed for every system is
        # ceil(n/3); report the theorem's value and verify it from zero/nonzero.
        theorem_alpha = (n + 2) // 3
        assert minima[2] == exact_pairs(n, 1) if n >= 2 else minima[1] == 1
        if n >= 3:
            assert minima[3] == exact_triples_k1(n)
        # Verify that every graph has an independent set of theorem_alpha, while
        # some graph has no larger one, using the minimum coefficients.
        if theorem_alpha <= n:
            assert minima[theorem_alpha] > 0
        if theorem_alpha + 1 <= n:
            assert minima[theorem_alpha + 1] == 0
        assert guaranteed_alpha == theorem_alpha
        print(
            f"{n:>1}  {graph_count:>24}  "
            f"{(minima[2] if n >= 2 else 0):>3}  "
            f"{(minima[3] if n >= 3 else 0):>3}  {theorem_alpha:>9}"
        )

    critical = critical_count_k1_n6_r3()
    assert critical == 40
    print(f"\nCritical systems at (k,r,n)=(1,3,6): {critical}")

    R3 = regular_tournament_count(3)
    R5 = regular_tournament_count(5)
    assert (R3, R5) == (2, 24)
    print(f"Labeled regular tournaments: R_3={R3}, R_5={R5}")

    count_k2_r3 = comb(10, 5) // 2 * R5**2
    assert count_k2_r3 == 72_576
    print(f"Critical systems at (k,r,n)=(2,3,10): {count_k2_r3}")
    print("\nAll checks passed.")


if __name__ == "__main__":
    main()
