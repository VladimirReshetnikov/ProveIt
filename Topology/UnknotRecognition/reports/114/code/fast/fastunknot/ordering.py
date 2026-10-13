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
TYPE_CHECKING = False            # annotations only: importing typing costs 4.6 ms at start-up
if TYPE_CHECKING:
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


TIE_RULES = ("index", "oldest", "recent")


def _greedy_ties(neighbours, loops, start: int, ties: str, bound: tuple | None = None):
    """``_greedy`` with another rule for ties between crossings that share equally many edges
    with the processed region: ``oldest`` takes the one that has waited longest since it first
    touched the region, ``recent`` the one touched last.  The rules are incomparable (on 81
    diagrams each is better on about as many inputs as it is worse, work ratios 0.01 to 28),
    which is what a race of orders exploits; ``index`` is the default rule of ``_greedy``."""
    n = len(neighbours)
    active = [True] * n
    shared = [0] * n
    tie = [0] * n
    heap = [(0, -2 * loops[i], 0, i) for i in range(n)]
    heapify(heap)
    order = []
    current = start
    size = worst = total = clock = 0
    best_worst, best_total = bound if bound is not None else (None, None)
    recent = ties == "recent"
    while len(order) < n:
        if order:
            while True:
                neg_shared, neg_loops, key, current = heappop(heap)
                if active[current] and -neg_shared == 2 * shared[current] and key == tie[current]:
                    break
        order.append(current)
        active[current] = False
        clock += 1
        size += 4 - 2 * shared[current] - 2 * loops[current]
        if size > worst:
            worst = size
        total += size
        if best_worst is not None and (worst > best_worst or (worst == best_worst and total >= best_total)):
            return None
        for other in neighbours[current]:
            if active[other]:
                shared[other] += 1
                if recent:
                    tie[other] = -clock
                elif not tie[other]:
                    tie[other] = clock
                heappush(heap, (-2 * shared[other], -2 * loops[other], tie[other], other))
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


def best_scan_order(pd, tries: int | None = None, check: Callable[[], None] | None = None,
                    ties: str = "index") -> list[int]:
    """Greedy orders from several starts; keep the smallest boundary profile."""
    if ties not in TIE_RULES:
        raise ValueError(f"ties must be one of {TIE_RULES}")
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
        found = (_greedy(neighbours, loops, start, best_profile) if ties == "index"
                 else _greedy_ties(neighbours, loops, start, ties, best_profile))
        if found is not None:                     # otherwise abandoned: not strictly better
            best, best_profile = found
    return best


def repeated_stages(pd, order) -> int:
    """Number of crossings met in a picture already seen along ``order``.

    The picture of a stage is the position of the four crossing slots among the
    boundary points, up to monotone relabelling.  A transfer plan can only be
    reused across stages (``planar.Planar`` with ``shape_cache``) in a stage whose
    picture occurred before, so zero means that cache cannot help at all.
    """
    points: set = set()
    seen: set = set()
    repeats = 0
    for index in order:
        slots = pd[index]
        rank = {label: r for r, label in enumerate(sorted(points.union(slots)))}
        key = (tuple(rank[label] for label in slots), tuple(sorted(rank[label] for label in points)))
        if key in seen:
            repeats += 1
        else:
            seen.add(key)
        for label in slots:
            if label in points:
                points.remove(label)
            else:
                points.add(label)
    return repeats
