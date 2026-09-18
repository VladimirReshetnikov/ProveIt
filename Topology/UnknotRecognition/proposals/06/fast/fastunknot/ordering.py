"""Deterministic greedy scan orders, with explicit permutation validation."""
from __future__ import annotations
from collections import defaultdict
from time import monotonic
from .reference_algebra import ScanLimit

def _check_deadline(deadline):
    if deadline is not None and monotonic() >= deadline:
        raise ScanLimit("time budget exhausted during ordering")

def validate_order(n, order):
    order = list(order)
    if any(type(i) is not int for i in order) or sorted(order) != list(range(n)):
        raise ValueError("order must be a permutation of all crossing indices")
    return order

def scan_order(pd: list, start: int | None = None, *, deadline: float | None = None) -> list[int]:
    """Greedy order: prefer crossings sharing many edges with the current boundary."""
    n = len(pd)
    if n == 0:
        return []
    remaining = set(range(n))
    boundary: dict[int, int] = defaultdict(int)
    order: list[int] = []
    current = 0 if start is None else start
    while remaining:
        _check_deadline(deadline)
        if order:
            def score(i):
                shared = sum(1 for e in pd[i] if boundary.get(e))
                loops = 4 - len(set(pd[i]))
                return (shared, -(len(boundary) + 4 - 2 * shared - 2 * loops), -i)
            current = max(remaining, key=score)
        order.append(current)
        remaining.discard(current)
        for e in pd[current]:
            if boundary.get(e):
                del boundary[e]
            else:
                boundary[e] = 1
    return order


def order_profile(pd: list, order: list[int]) -> tuple[int, int]:
    """(maximal boundary size, total boundary size) along an order."""
    boundary: set = set()
    worst = total = 0
    for i in order:
        for e in pd[i]:
            boundary.symmetric_difference_update({e})
        worst = max(worst, len(boundary))
        total += len(boundary)
    return worst, total


def best_scan_order(pd: list, tries: int | None = None, *, deadline: float | None = None) -> list[int]:
    """Greedy orders from several starting crossings; keep the smallest boundary profile."""
    n = len(pd)
    if n == 0:
        return []
    if tries is not None and (type(tries) is not int or tries < 1):
        raise ValueError("tries must be positive")
    starts = range(n) if tries is None or tries >= n else range(0, n, max(1, n // tries))
    best, best_profile = None, None
    for start in starts:
        order = scan_order(pd, start, deadline=deadline)
        profile = order_profile(pd, order)
        if best_profile is None or profile < best_profile:
            best, best_profile = order, profile
    return best


