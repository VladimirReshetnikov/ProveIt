"""One-sided exact Alexander tests over a fixed prime field.

If the deleted Alexander minor belongs to Z[t]^* after inverting t, it is
+/- t^k with 0 <= k <= n-1. A field evaluation outside this finite set proves
knottedness. A matching evaluation proves nothing and triggers the next stage.
"""
from __future__ import annotations

from .diagram import Diagram, DisjointSet

PRIME = 1_000_000_007


def evaluated_minor(diagram: Diagram, value: int, modulus: int = PRIME):
    n = diagram.crossings
    if n == 0:
        return []
    arcs = DisjointSet(2 * n)
    for _, b, _, d in diagram.pd:
        arcs.union(b, d)
    roots = sorted({arcs.find(e) for e in range(2 * n)})
    if len(roots) != n:
        raise ArithmeticError("unexpected number of Wirtinger arcs")
    col = {root: i for i, root in enumerate(roots)}
    signs = diagram.signs()  # Fox local signs, relative to under-port a -> c
    matrix = [[0] * (n - 1) for _ in range(n - 1)]
    value %= modulus
    for i, (a, b, c, _) in enumerate(diagram.pd[:-1]):
        o, u, v = col[arcs.find(b)], col[arcs.find(a)], col[arcs.find(c)]
        entries = ((o, 1 - value), (u, value), (v, -1)) if signs[i] > 0 else \
                  ((o, 1 - value), (u, -1), (v, value))
        for j, coefficient in entries:
            if j < n - 1:
                matrix[i][j] = (matrix[i][j] + coefficient) % modulus
    return matrix


def determinant_mod(matrix, modulus=PRIME, *, check=None):
    """O(n^3) field operations; row swaps are tracked, no integer rounding."""
    if modulus != PRIME:
        raise ValueError(f"this implementation uses the fixed prime {PRIME}")
    n = len(matrix)
    if any(len(row) != n for row in matrix):
        raise ValueError("matrix must be square")
    a = [[x % modulus for x in row] for row in matrix]
    determinant = 1
    for k in range(n):
        if check is not None:
            check()
        row = next((i for i in range(k, n) if a[i][k]), None)
        if row is None:
            return 0
        if row != k:
            a[k], a[row] = a[row], a[k]
            determinant = -determinant
        pivot = a[k][k]
        determinant = determinant * pivot % modulus
        inv = pow(pivot, -1, modulus)
        pivot_row = a[k]
        nonzero = [(j, pivot_row[j]) for j in range(k + 1, n) if pivot_row[j]]
        for i in range(k + 1, n):
            if not a[i][k]:
                continue
            factor = a[i][k] * inv % modulus
            target = a[i]
            for j, coefficient in nonzero:
                target[j] = (target[j] - factor * coefficient) % modulus
            target[k] = 0
    return determinant


def alexander_witness(diagram: Diagram, *, check=None):
    """Return a reproducible nonunit witness, or None (inconclusive)."""
    if diagram.crossings == 0:
        return None
    p = PRIME
    degree_bound = diagram.crossings - 1
    for value in (-1, 2):
        determinant = determinant_mod(evaluated_minor(diagram, value), check=check)
        powers = set()
        term = 1
        for _ in range(degree_bound + 1):
            powers.add(term)
            powers.add(-term % p)
            term = term * value % p
        if determinant not in powers:
            return {"kind": "alexander-nonunit-evaluation", "prime": p, "t": value,
                    "minor_determinant": determinant, "degree_bound": degree_bound,
                    "removed_row": degree_bound, "removed_column": degree_bound}
    return None


def verify_alexander_witness(diagram: Diagram, witness: dict) -> bool:
    """Recompute the minor and check the unit exclusion, not just its hash."""
    try:
        p = witness["prime"]
        value = witness["t"]
        n = diagram.crossings
        if (witness.get("kind") != "alexander-nonunit-evaluation" or p != PRIME
                or value not in (-1, 2) or n == 0 or witness["degree_bound"] != n - 1
                or witness["removed_row"] != n - 1 or witness["removed_column"] != n - 1):
            return False
        determinant = determinant_mod(evaluated_minor(diagram, value))
        if determinant != witness["minor_determinant"]:
            return False
        powers = {pow(value, k, p) for k in range(n)}
        powers |= {(-x) % p for x in powers}
        return determinant not in powers
    except (KeyError, TypeError, ValueError, ArithmeticError, AttributeError, IndexError):
        return False
