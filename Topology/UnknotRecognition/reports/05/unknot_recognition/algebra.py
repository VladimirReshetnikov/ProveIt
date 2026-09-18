"""Exact, dependency-free algebra. No floating-point decisions."""
from __future__ import annotations

from fractions import Fraction
from math import gcd, lcm
from typing import Iterable, Sequence


class DisjointSet:
    def __init__(self, size: int):
        self.parent = list(range(size))
        self.rank = [0] * size

    def find(self, item: int) -> int:
        root = item
        while self.parent[root] != root:
            root = self.parent[root]
        while item != root:
            item, self.parent[item] = self.parent[item], root
        return root

    def union(self, first: int, second: int) -> None:
        first, second = self.find(first), self.find(second)
        if first == second:
            return
        if self.rank[first] < self.rank[second]:
            first, second = second, first
        self.parent[second] = first
        if self.rank[first] == self.rank[second]:
            self.rank[first] += 1


def bareiss_determinant(matrix: Sequence[Sequence[int]]) -> int:
    """Fraction-free determinant, including singular matrices and row swaps."""
    n = len(matrix)
    if any(len(row) != n for row in matrix):
        raise ValueError("The matrix must be square.")
    if any(type(x) is not int for row in matrix for x in row):
        raise ValueError("The matrix must contain integers, not floats or booleans.")
    if n == 0:
        return 1
    a = [list(row) for row in matrix]
    sign, previous = 1, 1
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
                quotient, remainder = divmod(numerator, previous)
                if remainder:
                    raise ArithmeticError("Non-exact division in Bareiss elimination.")
                a[i][j] = quotient
            a[i][k] = 0
        previous = pivot
    return sign * a[-1][-1]


def rank_f2(columns: Iterable[int]) -> int:
    """Column rank over F_2. Bit i is the coefficient in row i."""
    pivots: dict[int, int] = {}
    for column in columns:
        if type(column) is not int or column < 0:
            raise ValueError("Binary columns must be non-negative integers.")
        while column:
            pivot = column.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = column
                break
            column ^= pivots[pivot]
    return len(pivots)


def rational_nullspace(matrix: Sequence[Sequence[int]], width: int) -> tuple[tuple[int, ...], ...]:
    """A rational basis, scaled to primitive integer vectors; not a Z-basis claim."""
    if width < 0 or any(len(row) != width for row in matrix):
        raise ValueError("Inconsistent matrix dimensions.")
    a = [[Fraction(x) for x in row] for row in matrix]
    row = 0
    pivots: list[int] = []
    for col in range(width):
        found = next((i for i in range(row, len(a)) if a[i][col]), None)
        if found is None:
            continue
        a[row], a[found] = a[found], a[row]
        scale = a[row][col]
        a[row] = [x / scale for x in a[row]]
        for i in range(len(a)):
            if i != row and a[i][col]:
                scale = a[i][col]
                a[i] = [x - scale * y for x, y in zip(a[i], a[row])]
        pivots.append(col)
        row += 1
        if row == len(a):
            break
    free = [col for col in range(width) if col not in pivots]
    result = []
    for col in free:
        vector = [Fraction(0)] * width
        vector[col] = Fraction(1)
        for i, pivot in enumerate(pivots):
            vector[pivot] = -a[i][col]
        denominator = lcm(*(x.denominator for x in vector)) if vector else 1
        integers = [int(x * denominator) for x in vector]
        common = gcd(*integers) if integers else 1
        integers = [x // common for x in integers]
        first = next((x for x in integers if x), 1)
        if first < 0:
            integers = [-x for x in integers]
        result.append(tuple(integers))
    return tuple(result)
