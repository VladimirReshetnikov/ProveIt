"""Polynomial-time one-sided Alexander tests without Z[t] arithmetic."""
from __future__ import annotations
from typing import Callable
from .diagram import Diagram, DisjointSet

PRIME = 2147483647


def numeric_minor(diagram: Diagram, t: int, prime: int = PRIME):
    n = diagram.crossings
    if not n:
        return []
    arcs = DisjointSet(2 * n)
    for _, b, _, d in diagram.pd:
        arcs.union(b, d)
    roots = sorted({arcs.find(e) for e in range(2 * n)})
    if len(roots) != n:
        raise ArithmeticError("unexpected number of Wirtinger arcs")
    col = {root: i for i, root in enumerate(roots)}
    signs = diagram.signs()
    incoming = {d // 4: d % 4 for d in diagram.traversal() if not d % 2}
    matrix = [[0] * (n - 1) for _ in range(n - 1)]
    for i, (a, b, c, _) in enumerate(diagram.pd[:-1]):
        u, v = (a, c) if incoming[i] == 0 else (c, a)
        entries = ((b, 1 - t), (u, t), (v, -1)) if signs[i] > 0 else \
                  ((b, 1 - t), (u, -1), (v, t))
        for edge, coefficient in entries:
            j = col[arcs.find(edge)]
            if j < n - 1:
                matrix[i][j] = (matrix[i][j] + coefficient) % prime
    return matrix


def determinant_mod(matrix, prime=PRIME, check: Callable[[], None] = lambda: None):
    a = [row[:] for row in matrix]
    n, result = len(a), 1
    for k in range(n):
        check()
        pivot = next((i for i in range(k, n) if a[i][k] % prime), None)
        if pivot is None:
            return 0
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            result = -result
        value = a[k][k] % prime
        result = result * value % prime
        inv = pow(value, -1, prime)
        row = a[k]
        # Sparse tails avoid touching zero entries of this pivot row.
        tail = [(j, row[j]) for j in range(k + 1, n) if row[j]]
        for i in range(k + 1, n):
            if a[i][k]:
                coefficient = a[i][k] * inv % prime
                for j, v in tail:
                    a[i][j] = (a[i][j] - coefficient * v) % prime
                a[i][k] = 0
    return result % prime


def alexander_obstruction(diagram: Diagram, check: Callable[[], None] = lambda: None):
    """For an unknot this minor is +-t^k, 0 <= k <= n-1. A mismatch is decisive."""
    attempts = []
    for value in (-1, 2):
        check()
        det = determinant_mod(numeric_minor(diagram, value), check=check)
        possible, power = set(), 1
        for _ in range(max(1, diagram.crossings)):
            possible.update((power, (-power) % PRIME))
            power = power * value % PRIME
        obstruction = det not in possible
        attempts.append({"t": value, "determinant_mod_p": det,
                         "max_unit_exponent": max(0, diagram.crossings - 1)})
        if obstruction:
            return {"obstruction": True, "prime": PRIME, "attempts": attempts}
    return {"obstruction": False, "prime": PRIME, "attempts": attempts}
