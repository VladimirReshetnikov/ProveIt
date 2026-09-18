"""Polynomial-time preprocessing: crossing-decreasing Reidemeister I/II moves
and the descending-diagram test.

Both only ever *help*: a diagram that survives them unchanged is passed on
unchanged, and neither produces a knottedness verdict.
"""
from __future__ import annotations

from dataclasses import dataclass

from .diagram import Diagram, DisjointSet


@dataclass(frozen=True)
class Move:
    kind: str
    crossings: tuple[int, ...]

    def to_json(self) -> dict:
        return {"kind": self.kind, "crossings": list(self.crossings)}


def legal_moves(diagram: Diagram) -> list[Move]:
    """Empty monogons (R1) and empty bigons with one strand over both times (R2)."""
    alpha = diagram.alpha()
    moves = []
    for face in diagram.faces():
        if len(face) == 1:
            moves.append(Move("R1", (face[0] // 4,)))
        elif len(face) == 2 and face[0] // 4 != face[1] // 4:
            # dart parity: odd slots are over-ports.  Each side of the bigon
            # must have the same over/under status at both of its crossings.
            if all(d % 2 == alpha[d] % 2 for d in face):
                moves.append(Move("R2", tuple(sorted(d // 4 for d in face))))
    return sorted(moves, key=lambda m: (m.kind, m.crossings))


def apply_move(diagram: Diagram, move: Move) -> Diagram:
    if move not in legal_moves(diagram):
        raise ValueError("illegal move")
    removed = set(move.crossings)
    edges = DisjointSet(2 * diagram.crossings)
    for i in removed:
        a, b, c, d = diagram.pd[i]
        edges.union(a, c)
        edges.union(b, d)
    remaining = [[edges.find(x) for x in row]
                 for i, row in enumerate(diagram.pd) if i not in removed]
    return Diagram.from_pd(remaining)


def simplify(diagram: Diagram, *, deadline: float | None = None) -> tuple[Diagram, list[Move]]:
    """Crossing-decreasing R1/R2 moves in O(n log n) word operations.

    Maintain the dart involution locally instead of rebuilding the entire PD
    after each move. A Fenwick tree translates permanent crossing ids into
    current indices for the original replayable Move format. Heap priorities
    implement the same R1-before-R2, lexicographic policy as legal_moves().
    """
    from heapq import heappop, heappush
    from time import monotonic
    from .scan import ScanLimit

    n = diagram.crossings
    if n == 0:
        return diagram, []
    alpha = diagram.alpha()
    alive = [True] * n
    tree = [0] + [i & -i for i in range(1, n + 1)]

    def rank(crossing):
        total = 0
        i = crossing
        while i:
            total += tree[i]
            i -= i & -i
        return total

    def remove(crossing):
        alive[crossing] = False
        i = crossing + 1
        while i <= n:
            tree[i] -= 1
            i += i & -i

    def opposite(dart):
        return 4 * (dart // 4) + (dart + 2) % 4

    def face_next(dart):
        other = alpha[dart]
        return 4 * (other // 4) + (other + 1) % 4

    def candidate(dart):
        if not alive[dart // 4]:
            return None
        other = face_next(dart)
        if other == dart:
            return "R1", (dart // 4,)
        if (other // 4 != dart // 4 and face_next(other) == dart
                and dart % 2 == alpha[dart] % 2
                and other % 2 == alpha[other] % 2):
            return "R2", tuple(sorted((dart // 4, other // 4)))
        return None

    queue = []

    def enqueue(dart):
        move = candidate(dart)
        if move is not None:
            heappush(queue, (move[0], move[1], dart))

    for dart in range(4 * n):
        enqueue(dart)
    trace = []
    while queue:
        if deadline is not None and monotonic() >= deadline:
            raise ScanLimit("time budget exhausted")
        kind, crossings, dart = heappop(queue)
        if candidate(dart) != (kind, crossings):
            continue
        trace.append(Move(kind, tuple(rank(c) for c in crossings)))
        deleted = set(crossings)
        reconnect = {}
        for c in crossings:
            for d in range(4 * c, 4 * c + 4):
                external = alpha[d]
                if external // 4 in deleted:
                    continue
                current = alpha[opposite(d)]
                # At most eight deleted darts; strands are joined straight
                # through the removed crossings, preserving the knot.
                traversed = 0
                while current // 4 in deleted:
                    current = alpha[opposite(current)]
                    traversed += 1
                    if traversed > 8:
                        raise ArithmeticError("invalid local reconnection")
                reconnect[external] = current
        for external, other in reconnect.items():
            alpha[external] = other
        for c in crossings:
            remove(c)
        affected = {d // 4 for d in reconnect}
        for c in affected:
            for d in range(4 * c, 4 * c + 4):
                enqueue(d)
    if not trace:
        return diagram, []
    pd = [[min(d, alpha[d]) for d in range(4 * c, 4 * c + 4)]
          for c in range(n) if alive[c]]
    return Diagram.from_pd(pd), trace


def descending_start(diagram: Diagram) -> int | None:
    """Find a descending basepoint in O(n) time by circular interval coverage.

    A crossing is first encountered underneath precisely for basepoints in the
    cyclic interval (over_visit, under_visit]. Test both traversal orientations.
    """
    if not diagram.pd:
        return 0
    walk = diagram.traversal()
    reverse = [4 * (d // 4) + (d + 2) % 4 for d in reversed(walk)]
    for traversal in (walk, reverse):
        size = len(traversal)
        visits = [[0, 0] for _ in diagram.pd]
        for i, dart in enumerate(traversal):
            visits[dart // 4][dart % 2] = i  # under=0, over=1
        delta = [0] * (size + 1)
        for under, over in visits:
            if over < under:
                delta[over + 1] += 1
                delta[under + 1] -= 1
            else:
                delta[over + 1] += 1
                delta[size] -= 1
                delta[0] += 1
                delta[under + 1] -= 1
        bad = 0
        for i, dart in enumerate(traversal):
            bad += delta[i]
            if bad == 0:
                return dart
    return None
