"""Deterministic, crossing-decreasing Reidemeister I and II moves only."""
from __future__ import annotations

from dataclasses import dataclass

from .algebra import DisjointSet
from .diagram import PlanarDiagram


@dataclass(frozen=True)
class Reduction:
    kind: str
    vertices: tuple[int, ...]
    face_darts: tuple[int, ...]

    def to_json(self) -> dict:
        return {"kind": self.kind, "vertices": list(self.vertices),
                "face_darts": list(self.face_darts)}


def legal_reductions(diagram: PlanarDiagram) -> tuple[Reduction, ...]:
    alpha = diagram.edge_involution()
    moves = []
    for face in diagram.face_darts():
        if len(face) == 1:
            moves.append(Reduction("R1", (face[0] // 4,), face))
        elif len(face) == 2 and face[0] // 4 != face[1] // 4:
            # One side of the empty bigon must be OVER at both crossings,
            # and the other side UNDER at both. Opposite parity would be
            # a clasp, not a removable Reidemeister-II pair.
            if all(d % 2 == alpha[d] % 2 for d in face):
                moves.append(Reduction("R2", tuple(sorted(d // 4 for d in face)), face))
    return tuple(sorted(moves, key=lambda move: (move.kind, move.vertices, move.face_darts)))


def apply_reduction(diagram: PlanarDiagram, move: Reduction) -> PlanarDiagram:
    if move not in legal_reductions(diagram):
        raise ValueError("This is not a legal empty-monogon/bigon reduction.")
    removed = set(move.vertices)
    edges = DisjointSet(2 * diagram.n)
    for vertex in removed:
        a, b, c, d = diagram.crossings[vertex]
        edges.union(a, c)
        edges.union(b, d)
    remaining = tuple(tuple(edges.find(x) for x in row)
                      for vertex, row in enumerate(diagram.crossings) if vertex not in removed)
    return PlanarDiagram(remaining)


def simplify(diagram: PlanarDiagram) -> tuple[PlanarDiagram, tuple[Reduction, ...]]:
    trace = []
    while diagram.n:
        moves = legal_reductions(diagram)
        if not moves:
            break
        move = moves[0]
        diagram = apply_reduction(diagram, move)
        trace.append(move)
    return diagram, tuple(trace)


def verify_reduction_trace(diagram: PlanarDiagram, trace: list[dict]) -> PlanarDiagram:
    if not isinstance(trace, list):
        raise ValueError("A reduction trace must be a list.")
    for item in trace:
        if not isinstance(item, dict):
            raise ValueError("Invalid reduction step.")
        try:
            move = Reduction(item["kind"], tuple(item["vertices"]), tuple(item["face_darts"]))
        except (KeyError, TypeError) as exc:
            raise ValueError("Invalid reduction step.") from exc
        if any(type(x) is not int for x in move.vertices + move.face_darts):
            raise ValueError("Reduction indices must be integers.")
        diagram = apply_reduction(diagram, move)
    return diagram
