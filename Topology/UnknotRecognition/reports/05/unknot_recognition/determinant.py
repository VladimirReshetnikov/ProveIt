"""The Fox-colouring determinant: a one-sided nontriviality test."""
from __future__ import annotations

from .algebra import DisjointSet, bareiss_determinant
from .diagram import PlanarDiagram


def fox_matrix(diagram: PlanarDiagram) -> tuple[tuple[int, ...], ...]:
    n = diagram.n
    if not n:
        return ()
    arcs = DisjointSet(2 * n)
    for a, b, c, d in diagram.crossings:
        arcs.union(b, d)  # join the two halves of the over-arc
    roots = sorted({arcs.find(x) for x in range(2 * n)})
    if len(roots) != n:
        raise ArithmeticError("Unexpected number of Wirtinger arcs for a knot.")
    index = {root: i for i, root in enumerate(roots)}
    rows = []
    for a, b, c, d in diagram.crossings:
        row = [0] * n
        row[index[arcs.find(b)]] += 2
        row[index[arcs.find(a)]] -= 1
        row[index[arcs.find(c)]] -= 1
        rows.append(tuple(row))
    return tuple(rows)


def knot_determinant(diagram: PlanarDiagram) -> int:
    matrix = fox_matrix(diagram)
    if not matrix:
        return 1
    minor = [row[:-1] for row in matrix[:-1]]
    result = abs(bareiss_determinant(minor))
    if result == 0 or result % 2 == 0:
        raise ArithmeticError("A knot determinant must be a positive odd integer.")
    return result
