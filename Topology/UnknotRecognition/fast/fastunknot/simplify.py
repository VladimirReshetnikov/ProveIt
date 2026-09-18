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


def simplify_reference(diagram: Diagram) -> tuple[Diagram, list[Move]]:
    """The 0.1 simplifier: rebuild and revalidate the diagram after every move (quadratic)."""
    trace: list[Move] = []
    while diagram.crossings:
        moves = legal_moves(diagram)
        if not moves:
            break
        diagram = apply_move(diagram, moves[0])
        trace.append(moves[0])
    return diagram, trace


class _Darts:
    """Mutable dart structure for incremental Reidemeister I/II reduction.

    Dart 4i+j is slot j of crossing i; ``alpha`` pairs the two darts of an edge.
    The face walk is d -> rot(alpha[d]) with rot(4i+j) = 4i+(j+1)%4.  Removing a
    crossing splices the edges that passed through it, so only the faces next to
    the spliced edges need to be looked at again: O(1) work per move plus the
    final rebuild, instead of one full revalidation per move.
    """

    def __init__(self, diagram: Diagram):
        self.alpha = diagram.alpha()
        self.alive = [True] * diagram.crossings
        self.remaining = diagram.crossings

    def nxt(self, d: int) -> int:
        a = self.alpha[d]
        return a - a % 4 + (a + 1) % 4

    def move_at(self, d: int):
        """A legal move whose face contains dart d, or None."""
        if not self.alive[d // 4]:
            return None
        e = self.nxt(d)
        if e == d:
            return ("R1", (d // 4,), (d,))
        if e // 4 != d // 4 and self.nxt(e) == d:
            if d % 2 == self.alpha[d] % 2 and e % 2 == self.alpha[e] % 2:
                return ("R2", tuple(sorted((d // 4, e // 4))), (d, e))
        return None

    def _splice(self, through: dict) -> list[int]:
        """Remove the crossings owning the darts in ``through`` (a fixed-point-free
        involution: the strand entering the removed region at x leaves it at through[x])."""
        alpha = self.alpha
        touched = []
        done = set()
        for x in through:
            outer = alpha[x]
            if outer in through or outer in done:
                continue
            y = alpha[through[x]]
            while y in through:                     # the strand re-enters the removed region
                y = alpha[through[y]]
            alpha[outer], alpha[y] = y, outer
            done.update((outer, y))
            touched.extend((outer, y))
        return touched

    def apply(self, move) -> list[int]:
        kind, crossings, darts = move
        if kind == "R1":
            d = darts[0]
            base, j = d - d % 4, d % 4
            k, l = base + (j + 1) % 4, base + (j + 2) % 4
            through = {k: l, l: k}
        else:
            d, e = darts
            a, j = d - d % 4, d % 4
            b, k = e - e % 4, e % 4
            x0, x1 = a + (j + 2) % 4, b + (k + 1) % 4   # strand through a.j -- b.(k-1)
            y0, y1 = a + (j + 1) % 4, b + (k + 2) % 4   # strand through a.(j-1) -- b.k
            through = {x0: x1, x1: x0, y0: y1, y1: y0}
        for c in crossings:
            self.alive[c] = False
        self.remaining -= len(crossings)
        if self.remaining == 0:
            return []
        return self._splice(through)

    def rebuild(self) -> Diagram:
        rows, label = [], {}
        for i, alive in enumerate(self.alive):
            if not alive:
                continue
            row = []
            for j in range(4):
                d = 4 * i + j
                key = min(d, self.alpha[d])
                row.append(label.setdefault(key, len(label)))
            rows.append(row)
        return Diagram.from_pd(rows)


def simplify(diagram: Diagram) -> tuple[Diagram, list[Move]]:
    """Crossing-decreasing Reidemeister I/II moves until none applies.

    Incremental version (idea from acceleration proposal 02).  Moves in the
    trace name crossings by their index in the *input* diagram; ``replay``
    checks a trace.  The result is revalidated once at the end.
    """
    if not diagram.crossings:
        return diagram, []
    state = _Darts(diagram)
    trace: list[Move] = []
    stack = list(range(4 * diagram.crossings - 1, -1, -1))
    while stack and state.remaining:
        move = state.move_at(stack.pop())
        if move is None:
            continue
        trace.append(Move(move[0], move[1]))
        for d in state.apply(move):
            stack.append(d)
    return state.rebuild(), trace


def replay(diagram: Diagram, trace) -> Diagram:
    """Re-apply a trace produced by ``simplify``, checking that every move is legal."""
    state = _Darts(diagram)
    for item in trace:
        kind, crossings = (item.kind, tuple(item.crossings)) if isinstance(item, Move) else             (item["kind"], tuple(item["crossings"]))
        found = None
        for c in crossings:
            if not 0 <= c < len(state.alive) or not state.alive[c]:
                raise ValueError("the trace removes a crossing that is not present")
            for j in range(4):
                move = state.move_at(4 * c + j)
                if move is not None and move[0] == kind and move[1] == tuple(sorted(crossings)):
                    found = move
        if found is None:
            raise ValueError("the trace contains an illegal move")
        state.apply(found)
    return state.rebuild()


def descending_start_quadratic(diagram: Diagram) -> int | None:
    """The 0.1 test: try every start dart separately (kept as a test oracle)."""
    if not diagram.pd:
        return 0
    alpha = diagram.alpha()
    n = diagram.crossings
    for start in range(4 * n):
        seen: set[int] = set()
        current = start
        ok = True
        for _ in range(2 * n):
            crossing = current // 4
            if crossing not in seen:
                if current % 2 == 0:
                    ok = False
                    break
                seen.add(crossing)
            current = alpha[4 * crossing + (current + 2) % 4]
        if ok:
            return start
    return None


def descending_start(diagram: Diagram) -> int | None:
    """A start dart from which every crossing is first met on its over-strand, in O(n).

    Such a diagram is descending, hence an unknot.  Failure proves nothing.
    Reading the traversal cyclically from position s, crossing c is met first
    on its under-strand exactly when s lies in the cyclic interval
    (over position, under position].  Mark these bad intervals with a difference
    array and sweep; do the same for the reversed traversal.  (Linear-time
    formulation from the acceleration proposals; 0.1 tried each start in turn.)
    """
    if not diagram.pd:
        return 0
    forward = diagram.traversal()
    length = len(forward)
    backward = [dart ^ 2 for dart in reversed(forward)]
    for walk in (forward, backward):
        where = {}
        for k, dart in enumerate(walk):
            where[dart // 4, dart % 2] = k
        diff = [0] * (length + 1)
        for c in range(diagram.crossings):
            left, right = (where[c, 1] + 1) % length, where[c, 0]
            if left <= right:
                diff[left] += 1
                diff[right + 1] -= 1
            else:
                diff[left] += 1
                diff[length] -= 1
                diff[0] += 1
                diff[right + 1] -= 1
        bad = 0
        for k, dart in enumerate(walk):
            bad += diff[k]
            if bad == 0:
                return dart
    return None
