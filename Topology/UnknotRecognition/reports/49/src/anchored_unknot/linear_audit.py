"""Independent exact rational-rank and integer-minor audit; no group verdicts."""
from __future__ import annotations
from fractions import Fraction
from functools import reduce
from math import gcd
from .grammar import Source


def rational_rank(rows: list[list[int]]) -> int:
    if not rows:
        return 0
    a = [[Fraction(x) for x in row] for row in rows]
    rank = 0
    for col in range(len(a[0])):
        pivot = next((i for i in range(rank, len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        x = a[rank][col]
        a[rank] = [v / x for v in a[rank]]
        for i in range(rank + 1, len(a)):
            x = a[i][col]
            if x:
                a[i] = [v - x * w for v, w in zip(a[i], a[rank])]
        rank += 1
        if rank == len(a):
            break
    return rank


def determinant(matrix: list[list[int]]) -> int:
    """Fraction-free Bareiss determinant with row pivoting."""
    n = len(matrix)
    if not n:
        return 1
    a = [row[:] for row in matrix]
    if any(len(row) != n for row in a):
        raise ValueError("square matrix required")
    last, sign = 1, 1
    for k in range(n - 1):
        pivot = next((i for i in range(k, n) if a[i][k]), None)
        if pivot is None:
            return 0
        if pivot != k:
            a[pivot], a[k] = a[k], a[pivot]
            sign = -sign
        p = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                num = a[i][j] * p - a[i][k] * a[k][j]
                if num % last:
                    raise ArithmeticError("nonexact Bareiss division")
                a[i][j] = num // last
            a[i][k] = 0
        last = p
    return sign * a[-1][-1]


def audit_state(source: Source, images: dict[int, tuple[int, int]], slots: set[int],
                with_cofactors: bool = True) -> dict:
    gs = source.generators
    a = source.exponent_matrix()
    rows = [a[j] for j in sorted(slots)]
    live = sorted({t for t, k in images.values()})
    if set(images) != set(gs) or any(k == 0 for _, k in images.values()):
        raise AssertionError("not a nonzero monomial map")
    if rational_rank(rows) != len(gs) - len(live) or len(rows) != len(gs) - len(live):
        raise AssertionError("selected source rows are not independent")
    l0 = source.max_length
    blocks = []
    for target in live:
        columns = [i for i, g in enumerate(gs) if images[g][0] == target]
        vector = [images[gs[i]][1] for i in columns]
        if reduce(gcd, (abs(x) for x in vector), 0) != 1:
            raise AssertionError("column is not primitive")
        if any(sum(row[i] * images[gs[i]][1] for i in columns) for row in rows):
            raise AssertionError("selected source matrix does not annihilate column")
        t = len(columns)
        squared_bound = 1 if t == 1 else (t - 1) ** (t - 1) * l0 ** (2 * (t - 1))
        if any(x * x > squared_bound for x in vector):
            raise AssertionError("Hadamard bound violated")
        report = {'size': t, 'max_exponent_bits': max(abs(x).bit_length() for x in vector)}
        if with_cofactors:
            basis = []
            for row in rows:
                restricted = [row[i] for i in columns]
                if rational_rank(basis + [restricted]) > len(basis):
                    basis.append(restricted)
                if len(basis) == t - 1:
                    break
            if len(basis) != t - 1:
                raise AssertionError("block does not have one-dimensional kernel")
            cof = [(-1) ** j * determinant([row[:j] + row[j + 1:] for row in basis]) for j in range(t)]
            divisor = reduce(gcd, (abs(x) for x in cof), 0)
            primitive = [x // divisor for x in cof]
            if primitive != vector and [-x for x in primitive] != vector:
                raise AssertionError("primitive cofactor vector mismatch")
            report['cofactor_gcd_bits'] = divisor.bit_length()
        blocks.append(report)
    return {'selected_rows': len(rows), 'live_rank': len(live), 'blocks': blocks}
