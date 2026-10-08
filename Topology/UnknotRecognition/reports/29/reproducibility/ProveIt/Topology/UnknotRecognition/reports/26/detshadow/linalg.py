"""Exact determinants and singular-safe terminal compression; stdlib only."""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from typing import Sequence


def bareiss(matrix: Sequence[Sequence[int]]) -> int:
    a = [list(row) for row in matrix]
    n = len(a)
    if any(len(row) != n for row in a):
        raise ValueError("matrix must be square")
    if any(type(x) is not int for row in a for x in row):
        raise TypeError("Bareiss requires integer entries")
    if n == 0:
        return 1
    old, sign = 1, 1
    for k in range(n - 1):
        pivot = next((i for i in range(k, n) if a[i][k]), None)
        if pivot is None:
            return 0
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            sign = -sign
        value = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                quotient, rem = divmod(value * a[i][j] - a[i][k] * a[k][j], old)
                if rem:
                    raise ArithmeticError("non-exact Bareiss division")
                a[i][j] = quotient
            a[i][k] = 0
        old = value
    return sign * a[-1][-1]


def rational_det(matrix: Sequence[Sequence[F]]) -> F:
    a = [[F(x) for x in row] for row in matrix]
    n = len(a)
    if any(len(row) != n for row in a):
        raise ValueError("matrix must be square")
    result = F(1)
    for k in range(n):
        pivot = next((i for i in range(k, n) if a[i][k]), None)
        if pivot is None:
            return F(0)
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            result = -result
        p = a[k][k]
        result *= p
        for i in range(k + 1, n):
            if a[i][k]:
                f = a[i][k] / p
                for j in range(k + 1, n):
                    a[i][j] -= f * a[k][j]
                a[i][k] = F(0)
    return result


def signed_laplacian(n: int, edges: Sequence[tuple[int, int, int]]) -> list[list[int]]:
    if type(n) is not int or n < 1:
        raise ValueError("a graph must have at least one vertex")
    a = [[0] * n for _ in range(n)]
    for u, v, weight in edges:
        if not (0 <= u < n and 0 <= v < n) or type(weight) is not int:
            raise ValueError("invalid weighted edge")
        if u == v:
            continue
        a[u][u] += weight
        a[v][v] += weight
        a[u][v] -= weight
        a[v][u] -= weight
    return a


def normalize_partition(labels: Sequence[int], size: int) -> tuple[int, ...]:
    if len(labels) != size or any(type(x) is not int for x in labels):
        raise ValueError("partition needs one integer label per terminal")
    names: dict[int, int] = {}
    return tuple(names.setdefault(x, len(names)) for x in labels)


def quotient_cofactor(lap: Sequence[Sequence[int]], terminals: Sequence[int],
                       partition: Sequence[int]) -> list[list[int]]:
    """Independent full-size construction; ground first terminal's block."""
    n = len(lap)
    b = list(terminals)
    if not b or len(set(b)) != len(b) or any(x < 0 or x >= n for x in b):
        raise ValueError("invalid terminals")
    labels = normalize_partition(partition, len(b))
    interior = [x for x in range(n) if x not in set(b)]
    ids = {x: j for j, x in enumerate(interior)}
    for x, g in zip(b, labels):
        ids[x] = -1 if g == 0 else len(interior) + g - 1
    d = len(interior) + max(labels)
    result = [[0] * d for _ in range(d)]
    for i in range(n):
        if ids[i] < 0:
            continue
        for j in range(n):
            if ids[j] >= 0:
                result[ids[i]][ids[j]] += lap[i][j]
    return result


@dataclass(frozen=True)
class TerminalKernel:
    """Signed response matrix with its nullspace border retained.

    Algebraic queries allow all partitions, with no planarity assumption.
    Application to tangles separately requires correct quotient geometry.
    """
    terminals: tuple[int, ...]
    interior: tuple[int, ...]
    selected: tuple[int, ...]
    null_vertices: tuple[int, ...]
    factor: F
    coupling: tuple[tuple[F, ...], ...]
    response: tuple[tuple[F, ...], ...]

    @property
    def nullity(self) -> int:
        return len(self.null_vertices)

    @classmethod
    def build(cls, lap: Sequence[Sequence[int]], terminals: Sequence[int]) -> 'TerminalKernel':
        n = len(lap)
        if any(len(row) != n for row in lap):
            raise ValueError("matrix must be square")
        if any(lap[i][j] != lap[j][i] for i in range(n) for j in range(n)):
            raise ValueError("matrix must be symmetric")
        b = tuple(terminals)
        if not b or len(set(b)) != len(b) or any(type(x) is not int or x < 0 or x >= n for x in b):
            raise ValueError("invalid terminals")
        interior = tuple(i for i in range(n) if i not in set(b))
        active = list(interior) + list(b)
        r = len(interior)
        m = [[F(lap[i][j]) for j in active] for i in active]
        selected: list[int] = []
        factor = F(1)
        while r:
            diagonal = next((i for i in range(r) if m[i][i]), None)
            if diagonal is not None:
                pivot = [diagonal]
            else:
                pair = next(((i, j) for i in range(r) for j in range(i + 1, r) if m[i][j]), None)
                if pair is None:
                    break
                pivot = list(pair)
            keep = [i for i in range(len(active)) if i not in pivot]
            if len(pivot) == 1:
                p = pivot[0]
                det = m[p][p]
                nxt = [[m[i][j] - m[i][p] * m[p][j] / det for j in keep] for i in keep]
            else:
                p, q = pivot
                a, c, d = m[p][p], m[p][q], m[q][q]
                det = a * d - c * c
                if not det:
                    raise ArithmeticError("singular two-by-two pivot")
                nxt = []
                for i in keep:
                    row = []
                    for j in keep:
                        correction = (m[i][p] * (d * m[p][j] - c * m[q][j])
                                      + m[i][q] * (-c * m[p][j] + a * m[q][j])) / det
                        row.append(m[i][j] - correction)
                    nxt.append(row)
            factor *= det
            selected.extend(active[i] for i in pivot)
            active = [active[i] for i in keep]
            r -= len(pivot)
            m = nxt
        if any(m[i][j] for i in range(r) for j in range(r)):
            raise ArithmeticError("interior residue is not zero")
        return cls(b, interior, tuple(selected), tuple(active[:r]), factor,
                   tuple(tuple(row[r:]) for row in m[:r]),
                   tuple(tuple(row[r:]) for row in m[r:]))

    def reduced_matrix(self, partition: Sequence[int]) -> list[list[F]] | None:
        labels = normalize_partition(partition, len(self.terminals))
        q, r = max(labels), self.nullity
        if r > q:
            return None
        a = [[F(0)] * (r + q) for _ in range(r + q)]
        for x, g in enumerate(labels):
            if g == 0:
                continue
            col = r + g - 1
            for i in range(r):
                a[i][col] += self.coupling[i][x]
                a[col][i] += self.coupling[i][x]
            for y, h in enumerate(labels):
                if h:
                    a[col][r + h - 1] += self.response[x][y]
        return a

    def query(self, partition: Sequence[int]) -> int:
        small = self.reduced_matrix(partition)
        if small is None:
            return 0
        r = self.nullity
        # Critical partitions have q=r. Their determinant is independent of
        # the response block and equals (-1)^r det(RQ)^2.
        if r and len(small) == 2 * r:
            coupling_det = rational_det([row[r:] for row in small[:r]])
            answer = self.factor * (-1 if r % 2 else 1) * coupling_det**2
        else:
            answer = self.factor * rational_det(small)
        if answer.denominator != 1:
            raise ArithmeticError("quotient cofactor is not integral")
        return answer.numerator

    def to_json(self) -> dict:
        def enc(x):
            return [x.numerator, x.denominator]
        return dict(terminals=list(self.terminals), interior=list(self.interior),
                    selected=list(self.selected), null_vertices=list(self.null_vertices),
                    factor=enc(self.factor), coupling=[[enc(x) for x in row] for row in self.coupling],
                    response=[[enc(x) for x in row] for row in self.response])


def verify_kernel(lap, kernel: TerminalKernel) -> bool:
    """Independent block-identity verification, not a replay of the builder.

    This verifies linear algebra only. It says nothing about whether an input
    graph was correctly extracted from a tangle.
    """
    n = len(lap)
    p, z, b = list(kernel.selected), list(kernel.null_vertices), list(kernel.terminals)
    if sorted(p + z + b) != list(range(n)) or sorted(p + z) != sorted(kernel.interior):
        return False
    rest = z + b
    a = [[F(lap[i][j]) for j in p] + [F(lap[i][j]) for j in rest] for i in p]
    r = len(p)
    determinant = F(1)
    for k in range(r):
        pivot = next((i for i in range(k, r) if a[i][k]), None)
        if pivot is None:
            return False
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            determinant = -determinant
        factor = a[k][k]
        determinant *= factor
        a[k] = [x / factor for x in a[k]]
        for i in range(r):
            if i != k:
                factor = a[i][k]
                a[i] = [x - factor*y for x,y in zip(a[i], a[k])]
    if determinant != kernel.factor:
        return False
    schur = [[F(lap[i][j]) - sum(F(lap[i][p[k]]) * a[k][r+t] for k in range(r))
              for t,j in enumerate(rest)] for i in rest]
    s = len(z)
    return (not any(schur[i][j] for i in range(s) for j in range(s))
            and tuple(tuple(row[s:]) for row in schur[:s]) == kernel.coupling
            and tuple(tuple(row[s:]) for row in schur[s:]) == kernel.response)
