"""Exact integral and binary linear algebra. All arithmetic is deterministic."""
from __future__ import annotations
from fractions import Fraction
from math import gcd, lcm
from .diagram import DSU, Diagram


def determinant_bareiss(matrix: list[list[int]]) -> int:
    """Fraction-free elimination with row pivoting; det(empty)=1."""
    n = len(matrix)
    if any(len(r) != n for r in matrix):
        raise ValueError("A square matrix is required")
    if any(type(x) is not int for row in matrix for x in row):
        raise ValueError("Matrix entries must be integers, not booleans")
    if not n:
        return 1
    a, denominator, sign = [list(row) for row in matrix], 1, 1
    for k in range(n - 1):
        pivot_row = next((i for i in range(k, n) if a[i][k]), None)
        if pivot_row is None:
            return 0
        if pivot_row != k:
            a[k], a[pivot_row] = a[pivot_row], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                numerator = pivot * a[i][j] - a[i][k] * a[k][j]
                q, rem = divmod(numerator, denominator)
                if rem:
                    raise ArithmeticError("Non-exact Bareiss division")
                a[i][j] = q
            a[i][k] = 0
        denominator = pivot
    return sign * a[-1][-1]


def fox_determinant(diagram: Diagram) -> int:
    """Compute |Delta_K(-1)|. A value different from 1 certifies knottedness.

    A value of 1 NEVER certifies unknotness (e.g. T(3,5)).
    """
    n = diagram.crossings
    if n == 0:
        return 1
    dsu = DSU(2 * n)
    for _, b, _, d in diagram.pd:
        dsu.union(b - 1, d - 1)
    roots = sorted({dsu.find(i) for i in range(2 * n)})
    if len(roots) != n:
        raise AssertionError("Unexpected number of Wirtinger arcs")
    root_index = {r: i for i, r in enumerate(roots)}
    matrix = [[0] * n for _ in range(n)]
    for i, (a, b, c, _) in enumerate(diagram.pd):
        for edge, coefficient in ((b, 2), (a, -1), (c, -1)):
            matrix[i][root_index[dsu.find(edge - 1)]] += coefficient
    return abs(determinant_bareiss([r[:-1] for r in matrix[:-1]]))


def gf2_rank(columns: list[int]) -> int:
    """Binary column echelon form, packed into Python integers."""
    pivots: dict[int, int] = {}
    for v in columns:
        if type(v) is not int or v < 0:
            raise ValueError("Columns must be nonnegative integer bitvectors")
        while v:
            p = v.bit_length() - 1
            if p not in pivots:
                pivots[p] = v
                break
            v ^= pivots[p]
    return len(pivots)


def integer_nullspace(matrix: list[list[int]], ncols: int) -> list[list[int]]:
    """A primitive integral vector for each rational kernel basis direction.

    This is a basis over Q after scalar extension, NOT a saturated Z-basis.
    Fraction numerators and denominators are arbitrary precision.
    """
    if type(ncols) is not int or ncols < 0 or any(len(r) != ncols for r in matrix):
        raise ValueError("Invalid matrix dimensions")
    if any(type(x) is not int for row in matrix for x in row):
        raise ValueError("Matrix entries must be integers, not booleans")
    a = [[Fraction(x) for x in row] for row in matrix]
    row, pivots = 0, []
    for col in range(ncols):
        p = next((i for i in range(row, len(a)) if a[i][col]), None)
        if p is None:
            continue
        a[row], a[p] = a[p], a[row]
        pivot = a[row][col]
        a[row] = [x / pivot for x in a[row]]
        for i in range(len(a)):
            if i != row and a[i][col]:
                factor = a[i][col]
                a[i] = [x - factor * y for x, y in zip(a[i], a[row])]
        pivots.append(col)
        row += 1
        if row == len(a):
            break
    answer = []
    for free in sorted(set(range(ncols)) - set(pivots)):
        x = [Fraction(0)] * ncols
        x[free] = Fraction(1)
        for r, p in enumerate(pivots):
            x[p] = -a[r][free]
        denominator = lcm(*(c.denominator for c in x))
        vector = [int(c * denominator) for c in x]
        divisor = gcd(*vector)
        vector = [c // divisor for c in vector]
        first = next(c for c in vector if c)
        if first < 0:
            vector = [-c for c in vector]
        answer.append(vector)
    return answer
