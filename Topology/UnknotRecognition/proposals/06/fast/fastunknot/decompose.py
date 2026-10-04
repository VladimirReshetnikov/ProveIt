"""Certified visible connected-sum decomposition of spherical PD diagrams.

Two parallel edges of the embedded dual give a Jordan curve meeting the knot
projection twice. Closing the two sides gives a connected-sum factorization.
This does not claim to find hidden/prime decompositions after isotopy.
"""
from __future__ import annotations
from collections import defaultdict
from time import monotonic
from .diagram import Diagram
from .reference_algebra import ScanLimit


def _check(deadline):
    if deadline is not None and monotonic() >= deadline:
        raise ScanLimit("time budget exhausted during connected-sum decomposition")


def split_on_edges(diagram: Diagram, edges: tuple[int, int]) -> tuple[Diagram, Diagram] | None:
    """Verify a nontrivial two-edge cut and return the two closed diagrams.

    A valid bond in a spherical embedded graph has a simple dual cycle, so
    this graph-theoretic check is also a topological splitting certificate.
    """
    if len(edges) != 2 or any(type(e) is not int for e in edges):
        return None
    e, f = edges
    if e == f or min(e, f) < 0 or max(e, f) >= 2 * diagram.crossings:
        return None
    incidences = defaultdict(list)
    for i, row in enumerate(diagram.pd):
        for label in row:
            incidences[label].append(i)
    adjacent = [[] for _ in diagram.pd]
    for label, (a, b) in incidences.items():
        if label not in edges:
            adjacent[a].append(b)
            adjacent[b].append(a)
    seen = {0}
    stack = [0]
    while stack:
        a = stack.pop()
        for b in adjacent[a]:
            if b not in seen:
                seen.add(b)
                stack.append(b)
    if len(seen) == diagram.crossings:
        return None
    # Both removed edges must cross the cut. In an even-degree connected
    # graph no single edge is a bridge; hence a disconnecting pair is a bond.
    if any(sum(i in seen for i in incidences[label]) != 1 for label in edges):
        return None
    fresh = 2 * diagram.crossings
    sides = []
    for want_seen in (True, False):
        rows = [tuple(fresh if label in edges else label for label in row)
                for i, row in enumerate(diagram.pd) if (i in seen) == want_seen]
        sides.append(Diagram.from_pd(rows))
    return tuple(sides)


def split_once(diagram: Diagram, *, deadline: float | None = None):
    """Find a visible connected-sum cut in linear expected dictionary work."""
    _check(deadline)
    if diagram.crossings < 2:
        return None
    face_of = {}
    for face, darts in enumerate(diagram.faces()):
        for dart in darts:
            face_of[dart] = face
    sides = defaultdict(list)
    for i, row in enumerate(diagram.pd):
        for j, edge in enumerate(row):
            sides[edge].append(face_of[4 * i + j])
    dual_edges = defaultdict(list)
    for edge, pair in sides.items():
        if pair[0] != pair[1]:
            dual_edges[tuple(sorted(pair))].append(edge)
    for pair in dual_edges.values():
        _check(deadline)
        if len(pair) >= 2:
            cut = (pair[0], pair[1])
            children = split_on_edges(diagram, cut)
            if children is None:
                raise ArithmeticError("parallel dual edges failed the two-edge-cut check")
            return cut, children
    return None


def connected_sum_factors(diagram: Diagram, *, deadline: float | None = None):
    """Return leaves and a replayable flat certificate (no recursion limit).

    Each node includes its normalized PD. Internal nodes list the two removed
    edges and two child indices. Leaves list their factor index. Total encoded
    size and naive recursive decomposition work are O(n^2 log n) bits.
    """
    nodes = [{"pd": diagram.to_json()["pd"]}]
    pending = [(0, diagram)]
    factors = []
    while pending:
        node, current = pending.pop()
        split = split_once(current, deadline=deadline)
        if split is None:
            nodes[node]["factor"] = len(factors)
            factors.append(current)
            continue
        cut, children = split
        ids = [len(nodes), len(nodes) + 1]
        nodes[node].update({"cut_edges": list(cut), "children": ids})
        for child in children:
            nodes.append({"pd": child.to_json()["pd"]})
        pending.extend(reversed(list(zip(ids, children))))
    return factors, {"root": 0, "nodes": nodes}


def verify_decomposition(diagram: Diagram, certificate: dict) -> list[Diagram]:
    """Replay every cut, rejecting a malformed or disconnected certificate."""
    nodes = certificate["nodes"]
    if certificate.get("root") != 0 or not nodes:
        raise ValueError("invalid decomposition root")
    expected = {0: diagram}
    leaves = {}
    seen = set()
    for index in range(len(nodes)):
        if index not in expected or index in seen:
            raise ValueError("unreachable or repeated decomposition node")
        seen.add(index)
        node = nodes[index]
        current = Diagram.from_pd(node["pd"])
        if current != expected[index]:
            raise ValueError("decomposition PD mismatch")
        if "factor" in node:
            if (type(node["factor"]) is not int or "children" in node
                    or "cut_edges" in node or node["factor"] in leaves):
                raise ValueError("invalid decomposition leaf")
            leaves[node["factor"]] = current
        else:
            children = split_on_edges(current, tuple(node["cut_edges"]))
            ids = node["children"]
            if children is None or len(ids) != 2 or ids[0] == ids[1]:
                raise ValueError("invalid decomposition cut")
            for child_id, child in zip(ids, children):
                if type(child_id) is not int or not index < child_id < len(nodes) or child_id in expected:
                    raise ValueError("invalid decomposition tree")
                expected[child_id] = child
    if sorted(leaves) != list(range(len(leaves))):
        raise ValueError("invalid factor numbering")
    return [leaves[i] for i in range(len(leaves))]


def connected_sum(left: Diagram, right: Diagram) -> Diagram:
    """Join edge 0 of two diagrams; useful for benchmarks and regression tests."""
    if not left.pd:
        return right
    if not right.pd:
        return left
    shift = 2 * left.crossings
    rows_l = [list(row) for row in left.pd]
    rows_r = [[label + shift for label in row] for row in right.pd]
    l = [(i, j) for i, row in enumerate(rows_l) for j, x in enumerate(row) if x == 0]
    r = [(i, j) for i, row in enumerate(rows_r) for j, x in enumerate(row) if x == shift]
    # Try the two orientations of the joining band, accepting only a spherical
    # rotation system. One of them realizes the standard connected sum.
    from .diagram import DiagramError
    for reverse in (False, True):
        right_rows = [row[:] for row in rows_r]
        ends = r[::-1] if reverse else r
        for (i, j), label in zip(ends, (0, shift)):
            right_rows[i][j] = label
        left_rows = [row[:] for row in rows_l]
        left_rows[l[1][0]][l[1][1]] = shift
        try:
            return Diagram.from_pd(left_rows + right_rows)
        except DiagramError:
            pass
    raise ArithmeticError("failed to construct a spherical connected sum")
