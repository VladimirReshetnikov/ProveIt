"""Greedy small-boundary scan orders.

The rule is the one of fastunknot 0.1: repeatedly take the unprocessed crossing
sharing the most edges with the processed region (ties: fewest new boundary
edges, then smallest index).  Since the boundary size is the same for every
candidate, the key reduces to (shared edges, loop edges, -index), which changes
only for the neighbours of the crossing just processed.  A lazy heap therefore
gives O(n log n) per start instead of the original O(n^2) rescoring; the
resulting orders are identical (tested).  The heap formulation was proposed
independently by all nine acceleration proposals.
"""
from __future__ import annotations

from collections import defaultdict
from heapq import heapify, heappop, heappush
from typing import Callable


def validate_order(n: int, order) -> list[int]:
    order = list(order)
    if len(order) != n or any(type(i) is not int for i in order) or set(order) != set(range(n)):
        raise ValueError("a scan order must be a permutation of all crossing indices")
    return order


def _graph(pd):
    owners = defaultdict(list)
    for i, row in enumerate(pd):
        for label in row:
            owners[label].append(i)
    neighbours = [[] for _ in pd]
    for pair in owners.values():
        if len(pair) != 2:
            raise ValueError("every edge label must occur exactly twice")
        a, b = pair
        if a != b:
            neighbours[a].append(b)
            neighbours[b].append(a)
    loops = [4 - len(set(row)) for row in pd]
    return neighbours, loops


def _greedy(neighbours, loops, start: int, bound: tuple | None = None):
    """Greedy order from ``start`` and its (maximal, total) boundary profile.

    The boundary grows by 4 - 2*shared - 2*loops when a crossing is added, so the
    profile costs O(1) per step.  With ``bound`` (the best profile so far) the
    candidate is abandoned, returning None, as soon as it cannot be strictly
    smaller: both components only grow along the order.
    """
    n = len(neighbours)
    active = [True] * n
    shared = [0] * n
    # score of 0.1: (shared, -(|boundary| + 4 - 2*shared - 2*loops), -index); |boundary| is common
    heap = [(0, -2 * loops[i], i) for i in range(n)]
    heapify(heap)
    order = []
    current = start
    size = worst = total = 0
    best_worst, best_total = bound if bound is not None else (None, None)
    while len(order) < n:
        if order:
            while True:
                neg_shared, neg_loops, current = heappop(heap)
                if active[current] and -neg_shared == 2 * shared[current] + 0:
                    break
        order.append(current)
        active[current] = False
        size += 4 - 2 * shared[current] - 2 * loops[current]
        if size > worst:
            worst = size
        total += size
        if best_worst is not None and (worst > best_worst or (worst == best_worst and total >= best_total)):
            return None
        for other in neighbours[current]:
            if active[other]:
                shared[other] += 1
                heappush(heap, (-2 * shared[other], -2 * loops[other], other))
    return order, (worst, total)


def scan_order(pd, start: int | None = None) -> list[int]:
    pd = list(pd)
    if not pd:
        return []
    start = 0 if start is None else start
    if type(start) is not int or not 0 <= start < len(pd):
        raise ValueError("invalid starting crossing")
    neighbours, loops = _graph(pd)
    return _greedy(neighbours, loops, start)[0]


def order_profile(pd, order) -> tuple[int, int]:
    """(maximal boundary size, total boundary size) along an order."""
    boundary: set = set()
    worst = total = 0
    for i in order:
        for e in pd[i]:
            if e in boundary:
                boundary.remove(e)
            else:
                boundary.add(e)
        worst = max(worst, len(boundary))
        total += len(boundary)
    return worst, total


def best_scan_order(pd, tries: int | None = None, check: Callable[[], None] | None = None) -> list[int]:
    """Greedy orders from several starts; keep the smallest boundary profile."""
    pd = list(pd)
    n = len(pd)
    if n == 0:
        return []
    neighbours, loops = _graph(pd)
    starts = range(n) if tries is None or tries >= n else range(0, n, max(1, n // tries))
    best, best_profile = None, None
    for start in starts:
        if check is not None:
            check()
        found = _greedy(neighbours, loops, start, best_profile)
        if found is not None:                     # otherwise abandoned: not strictly better
            best, best_profile = found
    return best
