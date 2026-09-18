"""Visible connected-sum decomposition through certified two-edge cuts.

This is a decomposition of the GIVEN PLANE DIAGRAM, not topological prime
recognition. A prime-looking projection may still represent a composite knot.
Each accepted cut is explicitly checked, and both closures are revalidated.
"""
from __future__ import annotations

from collections import defaultdict
from time import monotonic
from typing import Any

from .diagram import Diagram
from .scan import ScanLimit


def _edge_ends(diagram: Diagram) -> dict[int, list[int]]:
    ends: dict[int, list[int]] = defaultdict(list)
    for v, row in enumerate(diagram.pd):
        for edge in row:
            ends[edge].append(v)
    return ends


def _face_pairs(diagram: Diagram) -> dict[int, tuple[int, int]]:
    face_of = {}
    for i, face in enumerate(diagram.faces()):
        for dart in face:
            face_of[dart] = i
    alpha = diagram.alpha()
    pairs = {}
    for v, row in enumerate(diagram.pd):
        for j, edge in enumerate(row):
            dart = 4 * v + j
            pairs[edge] = tuple(sorted((face_of[dart], face_of[alpha[dart]])))
    return pairs


def close_cut(diagram: Diagram, left: set[int], cut: tuple[int, int]
              ) -> tuple[Diagram, Diagram]:
    """Verify a planar two-edge bond and close the two one-strand tangles.

    Common dual endpoints supply the two face arcs making a separating
    Jordan curve. Connectivity of both sides prevents an arbitrary partition
    or an unnoticed additional component from being accepted.
    """
    n = diagram.crossings
    if (not left or len(left) == n or any(type(v) is not int or v < 0 or v >= n for v in left)
            or len(cut) != 2 or cut[0] == cut[1]):
        raise ValueError("invalid nontrivial two-edge partition")
    ends = _edge_ends(diagram)
    boundary = {edge for edge, (u, v) in ends.items() if (u in left) != (v in left)}
    if boundary != set(cut):
        raise ValueError("partition boundary is not exactly the proposed cut")
    dual = _face_pairs(diagram)
    if dual[cut[0]] != dual[cut[1]] or dual[cut[0]][0] == dual[cut[0]][1]:
        raise ValueError("cut has no two-face Jordan-curve witness")
    right = set(range(n)) - left
    adjacency: list[list[int]] = [[] for _ in range(n)]
    for edge, (u, v) in ends.items():
        if edge not in boundary:
            adjacency[u].append(v)
            adjacency[v].append(u)
    for side in (left, right):
        seen = {min(side)}
        stack = list(seen)
        while stack:
            for v in adjacency[stack.pop()]:
                if v not in seen:
                    seen.add(v)
                    stack.append(v)
        if seen != side:
            raise ValueError("cut side is not connected")
    e, f = cut
    children = []
    for side in (left, right):
        rows = [[e if label == f else label for label in diagram.pd[v]] for v in sorted(side)]
        children.append(Diagram.from_pd(rows))
    return children[0], children[1]


def split_once(diagram: Diagram, *, deadline: float | None = None
               ) -> tuple[Diagram, Diagram, dict] | None:
    if diagram.crossings < 2:
        return None
    ends = _edge_ends(diagram)
    dual = _face_pairs(diagram)
    classes: dict[tuple[int, int], list[int]] = defaultdict(list)
    for edge, pair in dual.items():
        if pair[0] != pair[1]:
            classes[pair].append(edge)
    adjacency: list[list[tuple[int, int]]] = [[] for _ in diagram.pd]
    for edge, (u, v) in ends.items():
        adjacency[u].append((edge, v))
        adjacency[v].append((edge, u))
    for labels in classes.values():
        # Consecutive parallel dual edges suffice to find a dual 2-cycle.
        for e, f in zip(labels, labels[1:]):
            if deadline is not None and monotonic() >= deadline:
                raise ScanLimit("connected-sum decomposition time budget exhausted")
            cut = (e, f)
            seen = {ends[e][0]}
            stack = list(seen)
            while stack:
                for edge, v in adjacency[stack.pop()]:
                    if edge not in cut and v not in seen:
                        seen.add(v)
                        stack.append(v)
            if len(seen) == diagram.crossings:
                continue
            first, second = close_cut(diagram, seen, cut)
            return first, second, {"cut_edges": list(cut), "left_crossings": sorted(seen)}
    return None


def decompose(diagram: Diagram, *, deadline: float | None = None
              ) -> tuple[list[Diagram], dict]:
    """Iterative decomposition; no Python recursion-depth dependence."""
    pending = [(0, diagram)]
    next_id = 1
    records, leaves, factors = [], [], []
    while pending:
        if deadline is not None and monotonic() >= deadline:
            raise ScanLimit("connected-sum decomposition time budget exhausted")
        node, current = pending.pop()
        split = split_once(current, deadline=deadline)
        if split is None:
            leaves.append(node)
            factors.append(current)
        else:
            first, second, witness = split
            children = [next_id, next_id + 1]
            next_id += 2
            records.append({"parent": node, "children": children, **witness})
            pending.extend(((children[1], second), (children[0], first)))
    return factors, {"cuts": records, "leaf_ids": leaves,
                     "factor_crossings": [d.crossings for d in factors]}


def verify_decomposition(diagram: Diagram, evidence: dict) -> list[Diagram]:
    """Replay all cuts, returning factors or raising ValueError on bad evidence."""
    nodes = {0: diagram}
    used = {0}
    try:
        for item in evidence['cuts']:
            parent = item['parent']
            children = item['children']
            if (parent not in nodes or len(children) != 2 or children[0] == children[1]
                    or any(type(i) is not int or i < 0 or i in used for i in children)):
                raise ValueError("invalid decomposition tree")
            original_left = item['left_crossings']
            left = set(original_left)
            if len(left) != len(original_left):
                raise ValueError("duplicate crossing in cut witness")
            first, second = close_cut(nodes.pop(parent), left, tuple(item['cut_edges']))
            nodes[children[0]], nodes[children[1]] = first, second
            used.update(children)
        leaf_ids = evidence['leaf_ids']
        if len(leaf_ids) != len(nodes) or set(leaf_ids) != set(nodes):
            raise ValueError("incorrect leaf list")
        factors = [nodes[i] for i in leaf_ids]
        if [d.crossings for d in factors] != evidence['factor_crossings']:
            raise ValueError("incorrect factor crossing counts")
        return factors
    except (KeyError, TypeError, IndexError) as exc:
        raise ValueError("malformed decomposition evidence") from exc


def connected_sum(first: Diagram, second: Diagram) -> Diagram:
    """Construct a plane connected sum (test/benchmark helper)."""
    if not first.pd:
        return second
    if not second.pd:
        return first
    offset = 2 * first.crossings
    rows = [list(row) for row in first.pd]
    rows.extend([[edge + offset for edge in row] for row in second.pd])
    position = {}
    for i, row in enumerate(rows):
        for j, edge in enumerate(row):
            if edge in (0, offset):
                position.setdefault(edge, (i, j))
    i, j = position[0]
    k, ell = position[offset]
    rows[i][j], rows[k][ell] = offset, 0
    return Diagram.from_pd(rows)


def factored_khovanov_rank(diagram: Diagram, *, max_objects: int | None = None,
                           seconds: float | None = None, check_d_squared: bool = False,
                           memoize: bool = True) -> dict[str, Any]:
    """Return ranks without materializing the tensor product of sum factors.

    For knots over F2, the reduced Poincare polynomials multiply under #;
    unreduced homological ranks are twice the reduced ranks. Quantum gradings
    are not computed. Cube homological degree is additive because no crossings
    are changed by the cut. Identical normalized PD factors reuse a computation.
    """
    from .scan import khovanov_rank
    from math import isfinite
    if seconds is not None and (not isfinite(seconds) or seconds < 0):
        raise ValueError("seconds must be finite and nonnegative")
    if max_objects is not None and (type(max_objects) is not int or max_objects < 1):
        raise ValueError("max_objects must be a positive integer")
    deadline = None if seconds is None else monotonic() + seconds
    factors, decomposition = decompose(diagram, deadline=deadline)
    polynomial: dict[int, int] = {0: 1}
    cache: dict[tuple, dict] = {}
    results = []
    for factor in factors:
        if deadline is not None and monotonic() >= deadline:
            raise ScanLimit("factored Khovanov time budget exhausted")
        result = cache.get(factor.pd) if memoize else None
        reused = result is not None
        if result is None:
            remaining = None if deadline is None else max(0.0, deadline - monotonic())
            result = khovanov_rank(factor.pd, max_objects=max_objects,
                                   seconds=remaining, check_d_squared=check_d_squared)
            if memoize:
                cache[factor.pd] = result
        if any(v % 2 for v in result['by_degree'].values()):
            raise ArithmeticError("unreduced knot homological rank is not even")
        reduced = {h: v // 2 for h, v in result['by_degree'].items()}
        new: dict[int, int] = defaultdict(int)
        for h, u in polynomial.items():
            for j, v in reduced.items():
                new[h + j] += u * v
        polynomial = dict(new)
        results.append({"crossings": factor.crossings, "reused": reused,
                        "rank": result['rank'], "reduced_rank": result['reduced_rank'],
                        "by_degree": result['by_degree'], "stats": result['stats']})
    if deadline is not None and monotonic() >= deadline:
        raise ScanLimit("factored Khovanov time budget exhausted")
    reduced_rank = sum(polynomial.values())
    return {"rank": 2 * reduced_rank, "reduced_rank": reduced_rank,
            "by_degree": {h: 2 * v for h, v in sorted(polynomial.items())},
            "decomposition": decomposition, "factors": results,
            "quasipolynomial_guarantee": False}
