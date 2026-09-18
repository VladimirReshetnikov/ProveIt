"""Certified diagrammatic connected sums, not a topological prime decomposition.

A closed proper interval of the double-occurrence traversal word meets the rest
of the projection in exactly two edges. We additionally check that these edges
have the same two incident faces. Their dual edges form a separating 2-cycle
on the sphere. Capping the two sides gives connected-sum factors.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

from .diagram import Diagram


@dataclass(frozen=True)
class Factor:
    diagram: Diagram
    indices: tuple[int, ...]  # original crossing indices, in local crossing order


def _split(diagram: Diagram, check=None):
    n = diagram.crossings
    if n < 2:
        return None
    walk = diagram.traversal()
    word = [d // 4 for d in walk]
    face_of = {}
    for i, face in enumerate(diagram.faces()):
        for dart in face:
            face_of[dart] = i
    alpha = diagram.alpha()
    dual = {}
    for dart in range(4 * n):
        edge = diagram.pd[dart // 4][dart % 4]
        dual[edge] = tuple(sorted((face_of[dart], face_of[alpha[dart]])))
    best = None
    best_balance = 0
    length = 2 * n
    for start in range(length):
        if check is not None:
            check()
        opened = set()
        present = set()
        for count in range(1, length):
            crossing = word[(start + count - 1) % length]
            present.add(crossing)
            if crossing in opened:
                opened.remove(crossing)
            else:
                opened.add(crossing)
            if opened:
                continue
            size = len(present)
            balance = min(size, n - size)
            if balance <= best_balance:
                continue
            d0, d1 = walk[start], walk[(start + count) % length]
            e0 = diagram.pd[d0 // 4][d0 % 4]
            e1 = diagram.pd[d1 // 4][d1 % 4]
            if e0 == e1 or dual[e0] != dual[e1] or dual[e0][0] == dual[e0][1]:
                continue
            best = (frozenset(present), e0, e1)
            best_balance = balance
            if balance == n // 2:
                break
        if best_balance == n // 2:
            break
    if best is None:
        return None
    left, e0, e1 = best
    parts = []
    for choose_left in (True, False):
        indices = tuple(i for i in range(n) if (i in left) == choose_left)
        rows = [[e0 if x == e1 else x for x in diagram.pd[i]] for i in indices]
        parts.append(Factor(Diagram.from_pd(rows), indices))
    return parts, (e0, e1)


def decompose(diagram: Diagram, *, check: Callable[[], None] | None = None):
    """Return leaf factors and an explicit tree of checked dual two-edge cuts.

    The search costs O(m^2) at a node with m crossings. The conservative bound
    for all nodes is O(n^3); balanced connected-sum chains are cheaper.
    An explicit stack avoids Python's recursion limit on long chains.
    """
    leaves = []
    cuts = []
    pending = [(diagram, tuple(range(diagram.crossings)))]
    while pending:
        current, indices = pending.pop()
        if check is not None:
            check()
        split = _split(current, check)
        if split is None:
            leaves.append(Factor(current, indices))
            continue
        children, edges = split
        cuts.append({"crossing_indices": list(indices), "cut_edges": list(edges),
                     "local_pd": current.to_json()["pd"],
                     "left_indices": list(children[0].indices),
                     "right_indices": list(children[1].indices)})
        for child in reversed(children):
            pending.append((child.diagram, tuple(indices[i] for i in child.indices)))
    return leaves, cuts
