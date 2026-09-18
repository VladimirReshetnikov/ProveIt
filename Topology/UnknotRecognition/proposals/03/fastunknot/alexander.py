"""Exact Alexander polynomial from the Wirtinger presentation (Fox calculus).

Polynomials in ``t`` are lists of integer coefficients, lowest degree first.
The Alexander matrix has a row for every crossing: with over-arc ``o``,
incoming under-arc ``u`` and outgoing under-arc ``v`` the row is
``(1 - t) x_o + t x_u - x_v`` at a positive crossing and
``(1 - t) x_o - x_u + t x_v`` at a negative crossing.  Deleting one row and one
column and taking a fraction-free determinant over Z[t] gives the Alexander
polynomial up to a unit, which is normalized to have positive constant term.
A polynomial different from 1 certifies that the knot is nontrivial; the
polynomial 1 proves nothing.  Running time is polynomial in the crossing number.
"""
from __future__ import annotations

from .diagram import Diagram, DisjointSet

Poly = list  # coefficients, lowest degree first


def trim(p: Poly) -> Poly:
    while p and p[-1] == 0:
        p.pop()
    return p


def add(p: Poly, q: Poly) -> Poly:
    n = max(len(p), len(q))
    return trim([(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)])


def sub(p: Poly, q: Poly) -> Poly:
    n = max(len(p), len(q))
    return trim([(p[i] if i < len(p) else 0) - (q[i] if i < len(q) else 0) for i in range(n)])


def mul(p: Poly, q: Poly) -> Poly:
    if not p or not q:
        return []
    out = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                out[i + j] += a * b
    return trim(out)


def exact_div(p: Poly, q: Poly) -> Poly:
    """Exact division in Z[t]; raises if the division is not exact."""
    p, q = trim(list(p)), trim(list(q))
    if not q:
        raise ZeroDivisionError("division by the zero polynomial")
    if not p:
        return []
    result = [0] * (len(p) - len(q) + 1)
    remainder = p[:]
    for k in range(len(result) - 1, -1, -1):
        coefficient, rest = divmod(remainder[k + len(q) - 1], q[-1])
        if rest:
            raise ArithmeticError("non-exact polynomial division")
        result[k] = coefficient
        for j, b in enumerate(q):
            remainder[k + j] -= coefficient * b
    if any(remainder):
        raise ArithmeticError("non-exact polynomial division")
    return trim(result)


def determinant(matrix: list[list[Poly]], *, check=lambda: None) -> Poly:
    """Fraction-free Bareiss elimination over Z[t]."""
    n = len(matrix)
    if n == 0:
        return [1]
    a = [[trim(list(x)) for x in row] for row in matrix]
    sign, previous = 1, [1]
    for k in range(n - 1):
        check()
        pivot_row = next((i for i in range(k, n) if a[i][k]), None)
        if pivot_row is None:
            return []
        if pivot_row != k:
            a[k], a[pivot_row] = a[pivot_row], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k + 1, n):
            check()
            for j in range(k + 1, n):
                a[i][j] = exact_div(sub(mul(pivot, a[i][j]), mul(a[i][k], a[k][j])), previous)
            a[i][k] = []
        previous = pivot
    result = a[-1][-1]
    return [-c for c in result] if sign < 0 else result


def normalize(p: Poly) -> Poly:
    """Divide by the largest power of t and make the constant term positive."""
    p = trim(list(p))
    if not p:
        return []
    while p and p[0] == 0:
        p.pop(0)
    if p[0] < 0:
        p = [-c for c in p]
    return p


def alexander_matrix(diagram: Diagram) -> list[list[Poly]]:
    n = diagram.crossings
    arcs = DisjointSet(2 * n)
    for _, b, _, d in diagram.pd:
        arcs.union(b, d)
    roots = sorted({arcs.find(e) for e in range(2 * n)})
    if len(roots) != n:
        raise ArithmeticError("unexpected number of Wirtinger arcs")
    column = {root: i for i, root in enumerate(roots)}
    signs = diagram.signs()
    incoming_under = {d // 4: d % 4 for d in diagram.traversal() if d % 2 == 0}
    one_minus_t, t, minus_one = [1, -1], [0, 1], [-1]
    matrix = [[[] for _ in range(n)] for _ in range(n)]
    for i, (a, b, c, _) in enumerate(diagram.pd):
        under_in, under_out = (a, c) if incoming_under[i] == 0 else (c, a)
        o, u, v = (column[arcs.find(b)], column[arcs.find(under_in)],
                   column[arcs.find(under_out)])
        entries = ((o, one_minus_t), (u, t), (v, minus_one)) if signs[i] > 0 else \
                  ((o, one_minus_t), (u, minus_one), (v, t))
        for col, value in entries:
            matrix[i][col] = add(matrix[i][col], value)
    return matrix


def alexander_polynomial(diagram: Diagram, *, check=lambda: None) -> Poly:
    if diagram.crossings == 0:
        return [1]
    matrix = alexander_matrix(diagram)
    minor = [row[:-1] for row in matrix[:-1]]
    return normalize(determinant(minor, check=check))


def evaluate(p: Poly, value: int) -> int:
    result = 0
    for c in reversed(p):
        result = result * value + c
    return result


def format_polynomial(p: Poly) -> str:
    if not p:
        return "0"
    terms = []
    for k, c in enumerate(p):
        if not c:
            continue
        if k == 0:
            terms.append(str(c))
        else:
            power = "t" if k == 1 else f"t^{k}"
            terms.append(f"{c}*{power}" if c not in (1, -1) else (power if c == 1 else f"-{power}"))
    return " + ".join(terms).replace("+ -", "- ")
