"""Polynomial-time preprocessing: crossing-decreasing Reidemeister I/II moves
and the descending-diagram test.

Both only ever *help*: a diagram that survives them unchanged is passed on
unchanged, and neither produces a knottedness verdict.
"""
from __future__ import annotations

from dataclasses import dataclass
from time import monotonic
from .reference_algebra import ScanLimit

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
    trace: list[Move] = []
    while diagram.crossings:
        if deadline is not None and monotonic() >= deadline:
            raise ScanLimit("time budget exhausted during Reidemeister reduction")
        moves = legal_moves(diagram)
        if not moves:
            break
        diagram = apply_move(diagram, moves[0])
        trace.append(moves[0])
    return diagram, trace


def descending_start(diagram: Diagram, *, deadline: float | None = None) -> int | None:
    """A start dart from which every crossing is first met on its over-strand.

    Such a diagram is descending, hence an unknot.  Failure proves nothing.
    """
    if not diagram.pd:
        return 0
    alpha = diagram.alpha()
    n = diagram.crossings
    for start in range(4 * n):
        if deadline is not None and monotonic() >= deadline:
            raise ScanLimit("time budget exhausted during descending test")
        seen: set[int] = set()
        current = start
        ok = True
        for _ in range(2 * n):
            crossing = current // 4
            if crossing not in seen:
                if current % 2 == 0:  # first visit on an under-port
                    ok = False
                    break
                seen.add(crossing)
            opposite = 4 * crossing + (current + 2) % 4
            current = alpha[opposite]
        if ok:
            return start
    return None
