"""Visible connected sums: split a diagram along two-edge cuts of its projection.

Two edges that border the same pair of faces are crossed by a simple closed
curve meeting the diagram in exactly those two points, so the diagram is a
connected sum of the two sides.  This is *diagrammatic* factorization (proposed
by eight of the nine acceleration proposals), not prime decomposition: a
composite knot drawn without such a curve is left intact.

Why it matters: reduced Khovanov homology over a field is multiplicative under
connected sum, so ranks multiply and degree counts convolve, while a minimal
complex of the whole diagram needs as many objects as the rank.  The rank of k
summed copies of the Conway knot is 33^k, which no explicit complex can hold,
but each factor needs at most a few hundred objects.  For recognition, a
connected sum is trivial exactly when every summand is.
"""
from __future__ import annotations

from collections import defaultdict
from typing import Callable

from .diagram import Diagram, DiagramError


def split_once(diagram: Diagram):
    """(left, right, evidence) for one two-edge cut, or None."""
    n = diagram.crossings
    if n < 2:
        return None
    alpha = diagram.alpha()
    face_of = {}
    for index, face in enumerate(diagram.faces()):
        for dart in face:
            face_of[dart] = index
    by_faces: dict = defaultdict(list)
    for i, row in enumerate(diagram.pd):
        for j, edge in enumerate(row):
            dart = 4 * i + j
            if dart < alpha[dart]:
                a, b = face_of[dart], face_of[alpha[dart]]
                if a != b:
                    by_faces[(a, b) if a < b else (b, a)].append(edge)
    groups = [g for g in by_faces.values() if len(g) >= 2]
    if not groups:
        return None
    walk = diagram.traversal()                      # incoming darts, in order along the knot
    position = {diagram.pd[d // 4][d % 4]: k for k, d in enumerate(walk)}
    best = None
    for group in groups:
        stops = sorted(position[e] for e in group)
        for x, y in zip(stops, stops[1:] + [stops[0] + 2 * n]):
            length = y - x                          # crossing visits strictly between the two cuts
            balance = min(length, 2 * n - length)
            if best is None or balance > best[0]:
                best = (balance, x, y % (2 * n))
    _, x, y = best
    visits = []
    k = x
    while k != y:
        visits.append(walk[k] // 4)
        k = (k + 1) % (2 * n)
    inside = set(visits)
    edge_x = diagram.pd[walk[x] // 4][walk[x] % 4]
    edge_y = diagram.pd[walk[y] // 4][walk[y] % 4]
    pieces = []
    for side in (True, False):
        rows = [[edge_x if e == edge_y else e for e in row]
                for i, row in enumerate(diagram.pd) if (i in inside) == side]
        if not rows:
            return None
        try:
            pieces.append(Diagram.from_pd(rows))    # revalidates: one component, spherical
        except DiagramError:
            return None
    if pieces[0].crossings + pieces[1].crossings != n:
        raise ArithmeticError("a two-edge cut did not partition the crossings")
    return pieces[0], pieces[1], {"cut_edges": [edge_x, edge_y], "crossings": [pieces[0].crossings,
                                                                                pieces[1].crossings]}


def visible_factors(diagram: Diagram, check: Callable[[], None] = lambda: None):
    """All factors obtained by repeatedly splitting, and the list of cuts."""
    pending, factors, cuts = [diagram], [], []
    while pending:
        check()
        current = pending.pop()
        split = split_once(current)
        if split is None:
            factors.append(current)
        else:
            left, right, evidence = split
            cuts.append(evidence)
            pending.extend((right, left))
    return factors, cuts


def convolve(a: dict, b: dict) -> dict:
    out: dict = defaultdict(int)
    for h, v in a.items():
        for k, w in b.items():
            out[h + k] += v * w
    return dict(sorted(out.items()))
