"""Visible connected sums: split only certified two-edge bonds of the projection.

This is not topological prime decomposition. A composite knot whose particular
projection hides all such cuts is simply left intact.
"""
from __future__ import annotations
from collections import Counter
from time import monotonic
from typing import Callable
from .diagram import Diagram
from .geometry import ScanLimit


def split_once(diagram: Diagram, check: Callable[[], None] = lambda: None):
    n = diagram.crossings
    if n < 2:
        return None
    walk = [dart // 4 for dart in diagram.traversal()]
    best = None
    balance = 0
    for start in range(2 * n):
        check()
        parity = [False] * n
        open_count = 0
        for length in range(1, 2 * n - 1):
            cid = walk[(start + length - 1) % (2 * n)]
            parity[cid] = not parity[cid]
            open_count += 1 if parity[cid] else -1
            if open_count == 0:
                small = min(length // 2, n - length // 2)
                if small > balance:
                    balance, best = small, (start, length)
                    if balance == n // 2:
                        break
        if balance == n // 2:
            break
    if best is None:
        return None
    start, length = best
    selected = {walk[(start + j) % (2 * n)] for j in range(length)}
    counts = Counter(e for i in selected for e in diagram.pd[i])
    cut = sorted(e for e, count in counts.items() if count == 1)
    if len(cut) != 2:
        raise ArithmeticError("closed Gauss interval is not a two-edge cut")
    edge, other = cut
    pieces = []
    for side in (True, False):
        rows = [[edge if e == other else e for e in row]
                for i, row in enumerate(diagram.pd) if (i in selected) == side]
        # Independently revalidate the capped spherical rotation system.
        pieces.append(Diagram.from_pd(rows))
    evidence = {"cut_edges": cut, "left_crossings": sorted(selected),
                "gauss_interval": [start, length], "input_crossings": n}
    return pieces[0], pieces[1], evidence


def visible_factors(diagram: Diagram, check: Callable[[], None] = lambda: None):
    pending = [diagram]
    factors, trace = [], []
    while pending:
        check()
        current = pending.pop()
        split = split_once(current, check)
        if split is None:
            factors.append(current)
        else:
            a, b, cut = split
            trace.append({**cut, "pd": current.to_json()['pd']})
            pending.extend((b, a))
    return factors, trace


def factor_rank(pd, *, max_objects, deadline, check_d_squared, pivot):
    from .scan import khovanov_rank
    def check():
        if deadline is not None and monotonic() >= deadline:
            raise ScanLimit("time budget exhausted")
    factors, trace = visible_factors(Diagram.from_pd(pd), check)
    if len(factors) == 1:
        return None
    by_degree = {0: 1}  # Reduced ranks multiply under connected sum over F2.
    memo, summaries, stats = {}, [], {}
    for diagram in factors:
        check()
        key = diagram.pd
        reused = key in memo
        if not reused:
            seconds = None if deadline is None else max(0., deadline - monotonic())
            memo[key] = khovanov_rank(diagram.pd, max_objects=max_objects, seconds=seconds,
                                      check_d_squared=check_d_squared, pivot=pivot, factor=False)
        result = memo[key]
        if any(v % 2 for v in result['by_degree'].values()):
            raise ArithmeticError("F2 splitting must hold in every homological degree")
        new = {}
        for h, v in by_degree.items():
            for j, w in result['by_degree'].items():
                new[h + j] = new.get(h + j, 0) + v * (w // 2)
        by_degree = new
        summaries.append({"pd": diagram.to_json()['pd'], "crossings": diagram.crossings,
                          "reduced_rank": result['reduced_rank'], "memoized": reused})
        if not reused:
            for key, value in result['stats'].items():
                if key.startswith('max_'):
                    stats[key] = max(stats.get(key, 0), value)
                else:
                    stats[key] = stats.get(key, 0) + value
    reduced = sum(by_degree.values())
    stats.update(factors=len(factors), distinct_factors=len(memo))
    return {"rank": 2 * reduced, "reduced_rank": reduced,
            "by_degree": {h: 2 * v for h, v in sorted(by_degree.items())},
            "stats": stats, "order": [], "factorized": True,
            "factor_results": summaries, "decomposition": trace,
            "backend": "connected-sum-product", "pivot": pivot}
