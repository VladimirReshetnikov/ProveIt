"""Diagrammatic connected-sum factorization, not a prime-knot decomposition.

Two parallel edges in the planar dual give a Jordan curve crossing two diagram
edges.  Closing its two sides produces connected-sum factors.  We certify every
split combinatorially, and do not assert that remaining factors are prime knots.
"""
from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from time import monotonic
from .diagram import Diagram
from .scan import ScanLimit


@dataclass(frozen=True)
class Split:
    edges: tuple[int, int]
    first: tuple[int, ...]
    second: tuple[int, ...]

    def to_json(self) -> dict:
        return {'edges': list(self.edges), 'first': list(self.first),
                'second': list(self.second)}


def close_part(diagram: Diagram, indices: tuple[int, ...],
               edges: tuple[int, int]) -> Diagram:
    """Join the two cut endpoints on one side; normalize and validate the result."""
    a, b = edges
    return Diagram.from_pd([[a if e == b else e for e in diagram.pd[i]] for i in indices])


def find_split(diagram: Diagram, deadline: float | None = None) -> Split | None:
    n = diagram.crossings
    if n < 2:
        return None
    if deadline is not None and monotonic() > deadline:
        raise ScanLimit('time budget exhausted during decomposition')
    face_of = {}
    for k, face in enumerate(diagram.faces()):
        for dart in face:
            face_of[dart] = k
    occurrences = defaultdict(list)
    for i, row in enumerate(diagram.pd):
        for j, e in enumerate(row):
            occurrences[e].append(4 * i + j)
    parallel = defaultdict(list)
    adjacency = [[] for _ in range(n)]
    for e, (a, b) in occurrences.items():
        u, v = a // 4, b // 4
        adjacency[u].append((v, e))
        adjacency[v].append((u, e))
        faces = tuple(sorted((face_of[a], face_of[b])))
        if faces[0] != faces[1]:
            parallel[faces].append(e)
    for labels in parallel.values():
        if len(labels) < 2:
            continue
        cut = tuple(sorted(labels[:2]))
        seen = {0}
        stack = [0]
        while stack:
            u = stack.pop()
            for v, e in adjacency[u]:
                if e not in cut and v not in seen:
                    seen.add(v)
                    stack.append(v)
        if len(seen) == n:
            # Conservative guard: never infer a split from dual data alone.
            continue
        other = set(range(n)) - seen
        # Exactly one endpoint of each cut edge must belong to each side.
        if any(sum(d // 4 in seen for d in occurrences[e]) != 1 for e in cut):
            continue
        split = Split(cut, tuple(sorted(seen)), tuple(sorted(other)))
        close_part(diagram, split.first, cut)
        close_part(diagram, split.second, cut)
        return split
    return None


def factor_diagram(diagram: Diagram, deadline: float | None = None) -> tuple[list[Diagram], list[dict]]:
    """Return diagram factors and a replayable trace referring to local PD codes."""
    todo = [diagram]
    factors = []
    trace = []
    while todo:
        current = todo.pop()
        split = find_split(current, deadline)
        if split is None:
            factors.append(current)
        else:
            first = close_part(current, split.first, split.edges)
            second = close_part(current, split.second, split.edges)
            trace.append({'pd': [list(c) for c in current.pd], **split.to_json()})
            todo.append(second)
            todo.append(first)
    return factors, trace


def connected_sum(first: Diagram, second: Diagram) -> Diagram:
    """Utility for tests/benchmarks: splice edge zero in two disjoint diagrams."""
    if not first.pd:
        return second
    if not second.pd:
        return first
    offset = 2 * first.crossings
    a = [list(row) for row in first.pd]
    b = [[e + offset for e in row] for row in second.pd]
    # Splice one occurrence from each edge.  This cross-connects the components.
    for rows, old, new in ((a, 0, offset), (b, offset, 0)):
        changed = False
        for row in rows:
            for j, e in enumerate(row):
                if e == old:
                    row[j] = new
                    changed = True
                    break
            if changed:
                break
    return Diagram.from_pd(a + b)
