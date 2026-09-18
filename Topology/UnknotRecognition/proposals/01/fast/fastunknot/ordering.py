"""Deterministic greedy scan orders with incremental frontier scores.

This reproduces the original greedy rule, but a lazy heap replaces its repeated
scan of every unprocessed crossing: O(n log n) per start, rather than O(n^2).
"""
from __future__ import annotations

from collections import defaultdict
from heapq import heapify, heappop, heappush


def validate_order(n: int, order) -> list[int]:
    order = list(order)
    if (len(order) != n or any(type(i) is not int for i in order)
            or set(order) != set(range(n))):
        raise ValueError("scan order must be a permutation of all crossing indices")
    return order


def _graph(pd):
    owners = defaultdict(list)
    for i, row in enumerate(pd):
        for label in row:
            owners[label].append(i)
    neighbours = [[] for _ in pd]
    for pair in owners.values():
        if len(pair) != 2:
            raise ValueError("every edge label must occur twice")
        a, b = pair
        if a != b:
            neighbours[a].append(b)
            neighbours[b].append(a)
    loops = [4 - len(set(row)) for row in pd]
    return neighbours, loops


def _greedy(neighbours, loops, start, check):
    n = len(neighbours)
    active = [True] * n
    shared = [0] * n
    heap = [(0, -loops[i], i) for i in range(n)]
    heapify(heap)
    result = []
    current = start
    while len(result) < n:
        if check is not None and len(result) % 64 == 0:
            check()
        if result:
            while heap:
                neg_shared, _, current = heappop(heap)
                if active[current] and -neg_shared == shared[current]:
                    break
        result.append(current)
        active[current] = False
        for other in neighbours[current]:
            if active[other]:
                shared[other] += 1
                heappush(heap, (-shared[other], -loops[other], other))
    return result


def scan_order(pd, start=None, *, check=None):
    n = len(pd)
    if not n:
        return []
    start = 0 if start is None else start
    if type(start) is not int or not 0 <= start < n:
        raise ValueError("invalid starting crossing")
    neighbours, loops = _graph(pd)
    return _greedy(neighbours, loops, start, check)


def order_profile(pd, order):
    boundary = set()
    worst = total = 0
    for index in order:
        for edge in pd[index]:
            if edge in boundary:
                boundary.remove(edge)
            else:
                boundary.add(edge)
        worst = max(worst, len(boundary))
        total += len(boundary)
    return worst, total


def best_scan_order(pd, tries=None, *, check=None):
    n = len(pd)
    if not n:
        return []
    if tries is not None and (type(tries) is not int or tries <= 0):
        raise ValueError("tries must be positive")
    neighbours, loops = _graph(pd)
    # Preserve the baseline's exact start sequence and tie-breaking.
    starts = range(n) if tries is None or tries >= n else range(0, n, max(1, n // tries))
    best = None
    best_profile = None
    for start in starts:
        if check is not None:
            check()
        order = _greedy(neighbours, loops, start, check)
        profile = order_profile(pd, order)
        if best_profile is None or profile < best_profile:
            best, best_profile = order, profile
    return best
