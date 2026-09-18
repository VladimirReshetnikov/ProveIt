"""Heap-maintained versions of the upstream greedy frontier orders."""
from __future__ import annotations
from collections import defaultdict
from heapq import heappop, heappush
from typing import Callable


def validate_order(n: int, order) -> list[int]:
    order = list(order)
    if len(order) != n or any(type(i) is not int for i in order) or set(order) != set(range(n)):
        raise ValueError("scan order must be a permutation of all crossing indices")
    return order


def scan_order(pd, start: int | None = None, *, check: Callable[[], None] = lambda: None):
    n = len(pd)
    if not n:
        return []
    start = 0 if start is None else start
    if type(start) is not int or not 0 <= start < n:
        raise ValueError("invalid starting crossing")
    where = defaultdict(set)
    for i, row in enumerate(pd):
        for edge in row:
            where[edge].add(i)
    loops = [4 - len(set(row)) for row in pd]
    alive = [True] * n
    versions = [0] * n
    boundary = set()
    heap = [(0, -loops[i], i, 0) for i in range(n)]
    # Initial heap is not sorted by loops, so heapify explicitly.
    from heapq import heapify
    heapify(heap)
    result = []
    current = start
    for step in range(n):
        check()
        if step:
            while heap:
                _, _, current, version = heappop(heap)
                if alive[current] and versions[current] == version:
                    break
        result.append(current)
        alive[current] = False
        changed = set()
        for edge in pd[current]:
            boundary.symmetric_difference_update((edge,))
            changed.update(where[edge])
        for i in changed:
            if alive[i]:
                versions[i] += 1
                shared = sum(edge in boundary for edge in pd[i])
                heappush(heap, (-shared, -loops[i], i, versions[i]))
    return result


def order_profile(pd, order):
    boundary = set()
    worst = total = 0
    for i in order:
        for edge in pd[i]:
            boundary.symmetric_difference_update((edge,))
        worst = max(worst, len(boundary))
        total += len(boundary)
    return worst, total


def best_scan_order(pd, tries: int | None = None, *, check: Callable[[], None] = lambda: None):
    n = len(pd)
    if not n:
        return []
    if tries is not None and (type(tries) is not int or tries < 1):
        raise ValueError("tries must be positive")
    # Preserve the baseline's exact start set, including rounding behavior.
    starts = range(n) if tries is None or tries >= n else range(0, n, max(1, n // tries))
    best, score = None, None
    for start in starts:
        check()
        order = scan_order(pd, start, check=check)
        candidate = order_profile(pd, order)
        if score is None or candidate < score:
            best, score = order, candidate
    return best
