"""Visible connected-sum factorization, with replayable two-edge-cut evidence.

This detects cuts in the supplied projection; it is NOT a topological prime
factorization oracle. Absence of a cut says nothing about knot primality.
"""
from __future__ import annotations
from time import monotonic
from .diagram import Diagram
from .scan import ScanLimit, khovanov_rank


def _check(deadline):
    if deadline is not None and monotonic() >= deadline:
        raise ScanLimit("time budget exhausted during connected-sum factorization")


def _close(diagram: Diagram, vertices: set[int], e: int, f: int) -> Diagram:
    return Diagram.from_pd([[e if x == f else x for x in row]
                            for i, row in enumerate(diagram.pd) if i in vertices])


def find_cut(diagram: Diagram, *, deadline: float | None = None):
    """Find a proper closed interval of the cyclic Gauss word, in O(n^2) time.

    Both visits to every crossing in the interval lie there, so the projection
    subgraph has exactly the two boundary edges. In a spherical diagram this
    gives a connected-sum circle. Closing both sides retains all crossings.
    """
    n = diagram.crossings
    if n < 2:
        return None
    walk = diagram.traversal()
    size = len(walk)
    for start in range(size):
        _check(deadline)
        active, vertices = set(), set()
        for length in range(1, size):
            if length % 128 == 0:
                _check(deadline)
            dart = walk[(start + length - 1) % size]
            v = dart // 4
            vertices.add(v)
            active.symmetric_difference_update({v})
            if not active:
                incoming = walk[start]
                outgoing = walk[(start + length) % size]
                e = diagram.pd[incoming // 4][incoming % 4]
                f = diagram.pd[outgoing // 4][outgoing % 4]
                if e == f or not 0 < len(vertices) < n:
                    raise ArithmeticError("invalid proper Gauss interval")
                left = _close(diagram, vertices, e, f)
                right = _close(diagram, set(range(n)) - vertices, e, f)
                return left, right, {"cut_edges": [e, f],
                                     "left_crossings": sorted(vertices)}
    return None


def decompose(diagram: Diagram, *, deadline: float | None = None):
    """Return (leaves, cut_records); leaf entries are (node_id, Diagram).

    An explicit stack avoids Python recursion limits. The worst-case bound of
    this deliberately simple implementation is O(n^3), before bit costs.
    """
    pending, leaves, cuts, next_id = [(0, diagram)], [], [], 1
    while pending:
        _check(deadline)
        node, current = pending.pop()
        split = find_cut(current, deadline=deadline)
        if split is None:
            leaves.append((node, current))
            continue
        left, right, evidence = split
        li, ri = next_id, next_id + 1
        next_id += 2
        cuts.append({"node": node, "children": [li, ri], **evidence})
        pending.extend(((ri, right), (li, left)))
    return leaves, cuts


def replay_decomposition(diagram: Diagram, cuts: list[dict]) -> dict[int, Diagram]:
    """Validate actual two-edge bonds and reconstruct all leaf diagrams."""
    nodes = {0: diagram}
    allocated = {0}
    for cut in cuts:
        current = nodes.pop(cut['node'])
        e, f = cut['cut_edges']
        chosen = set(cut['left_crossings'])
        if len(chosen) != len(cut['left_crossings']) or not chosen < set(range(current.crossings)):
            raise ValueError("not a proper crossing subset")
        if not chosen or e == f:
            raise ValueError("empty cut or repeated edge")
        endpoints = {}
        for i, row in enumerate(current.pd):
            for label in row:
                endpoints.setdefault(label, []).append(i)
        crossing_edges = {label for label, (u, v) in endpoints.items()
                          if (u in chosen) != (v in chosen)}
        if crossing_edges != {e, f}:
            raise ValueError("not the claimed two-edge cut")
        li, ri = cut['children']
        if type(li) is not int or type(ri) is not int or li == ri or li in allocated or ri in allocated:
            raise ValueError("duplicate or invalid node id")
        allocated.update((li, ri))
        nodes[li] = _close(current, chosen, e, f)
        nodes[ri] = _close(current, set(range(current.crossings)) - chosen, e, f)
    return nodes


def factorized_khovanov_rank(diagram: Diagram, *, max_objects=None, seconds=None,
                             check_d_squared=False, pivot_strategy="fill") -> dict:
    """Total ranks and raw homological degrees, using reduced connected-sum tensor products.

    Unlike a scanner that materializes the final homology generators, this can
    return enormous ranks as binary integers. Repeated identical PD leaves are
    evaluated once. Only the supplied projection's visible factors are used.
    """
    from math import isfinite
    if seconds is not None and (not isfinite(seconds) or seconds < 0):
        raise ValueError("seconds must be finite and nonnegative")
    deadline = None if seconds is None else monotonic() + seconds
    leaves, cuts = decompose(diagram, deadline=deadline)
    total = {0: 1}
    factors, memo = [], {}
    for node, leaf in leaves:
        _check(deadline)
        if leaf.pd not in memo:
            remaining = None if deadline is None else max(0, deadline - monotonic())
            memo[leaf.pd] = khovanov_rank(leaf.pd, max_objects=max_objects,
                seconds=remaining, check_d_squared=check_d_squared, pivot_strategy=pivot_strategy)
        answer = memo[leaf.pd]
        reduced = {}
        for h, rank in answer['by_degree'].items():
            if rank % 2:
                raise ArithmeticError("odd unreduced F2 rank in a homological degree")
            reduced[h] = rank // 2
        new = {}
        for h, count in total.items():
            for k, multiplicity in reduced.items():
                new[h + k] = new.get(h + k, 0) + count * multiplicity
        total = new
        factors.append({"node": node, "crossings": leaf.crossings,
                        "reduced_rank": answer['reduced_rank'], "stats": answer['stats']})
    return {"rank": 2 * sum(total.values()), "reduced_rank": sum(total.values()),
            "by_degree": {h: 2*v for h, v in sorted(total.items())},
            "factors": factors, "cuts": cuts, "distinct_factors_computed": len(memo)}
