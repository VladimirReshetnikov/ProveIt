#!/usr/bin/env python3
"""Exact finite certificates for strict Wick valuation balancing.

Only rational matrices and lexicographically ordered rational valuation vectors
are implemented. This is a finite certificate solver, NOT a general Hahn-series
CAS. Fourier--Motzkin elimination may take exponential space and time.

Python 3.10+, standard library only. See verify.py for independent finite tests.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
from math import gcd, lcm
from typing import Iterable, Sequence

Value = tuple[F, ...]


def value(xs: Iterable[int | F]) -> Value:
    out = tuple(map(F, xs))
    if not out:
        raise ValueError("A valuation vector must have positive rank.")
    return out


def add(x: Value, y: Value) -> Value:
    if len(x) != len(y):
        raise ValueError("Valuation ranks differ.")
    return tuple(a + b for a, b in zip(x, y))


def scale(a: int | F, x: Value) -> Value:
    return tuple(F(a) * b for b in x)


def linear(a: Sequence[int | F], x: Sequence[Value], rank: int) -> Value:
    if len(a) != len(x):
        raise ValueError("Linear combination dimensions differ.")
    out = (F(0),) * rank
    for ai, xi in zip(a, x):
        out = add(out, scale(ai, xi))
    return out


@dataclass(frozen=True)
class _Row:
    a: tuple[F, ...]
    b: Value
    origin: tuple[F, ...]

    def times(self, c: F) -> _Row:
        if c <= 0:
            raise ValueError("Only positive row rescalings preserve strictness.")
        return _Row(tuple(c * x for x in self.a), scale(c, self.b),
                    tuple(c * x for x in self.origin))


@dataclass(frozen=True)
class Certificate:
    """Exactly one of balance and obstruction is non-None."""
    balance: tuple[Value, ...] | None
    obstruction: tuple[int, ...] | None
    generated_rows: int


def strict_alternative(matrix: Sequence[Sequence[int | F]],
                       constants: Sequence[Value], *,
                       dimension: int | None = None,
                       rank: int | None = None,
                       max_rows: int = 200_000) -> Certificate:
    """Solve M p + b > 0 over Q^rank with its lexicographic order.

    Return p, or a primitive nonnegative integer vector q with q^T M=0
    and q.b <= 0. Raise RuntimeError on the explicit resource guard.
    A returned certificate is always independently rechecked.
    """
    mat = tuple(tuple(map(F, row)) for row in matrix)
    n = len(mat)
    d = len(mat[0]) if n else (0 if dimension is None else dimension)
    r = len(constants[0]) if constants else (1 if rank is None else rank)
    if d < 0 or r < 1 or len(constants) != n:
        raise ValueError("Invalid dimensions.")
    if any(len(row) != d for row in mat):
        raise ValueError("Ragged matrix.")
    b = tuple(value(x) for x in constants)
    if any(len(x) != r for x in b):
        raise ValueError("Valuation ranks differ.")
    zero = (F(0),) * r
    unit = (F(1),) + (F(0),) * (r - 1)
    rows = [_Row(row, bi, tuple(F(i == j) for j in range(n)))
            for i, (row, bi) in enumerate(zip(mat, b))]
    generated = n

    def eliminate(rs: list[_Row], variables: int):
        nonlocal generated
        active = []
        for row in rs:
            if not any(row.a):
                if row.b <= zero:
                    return None, row.origin
            else:
                active.append(row)
        if variables == 0:
            return (), None
        if not active:
            return (zero,) * variables, None
        pos, neg, flat = [], [], []
        for row in active:
            last = row.a[-1]
            if last > 0:
                pos.append(row.times(1 / last))
            elif last < 0:
                neg.append(row.times(-1 / last))
            else:
                flat.append(_Row(row.a[:-1], row.b, row.origin))
        if generated + len(pos) * len(neg) > max_rows:
            raise RuntimeError("Fourier--Motzkin row budget exceeded.")
        derived = flat[:]
        for lo in pos:
            for hi in neg:
                derived.append(_Row(tuple(x + y for x, y in
                                          zip(lo.a[:-1], hi.a[:-1])),
                                    add(lo.b, hi.b),
                                    tuple(x + y for x, y in
                                          zip(lo.origin, hi.origin))))
                generated += 1
        partial, obstruction = eliminate(derived, variables - 1)
        if obstruction is not None:
            return None, obstruction
        assert partial is not None
        lower = [scale(-1, add(row.b, linear(row.a[:-1], partial, r)))
                 for row in pos]
        upper = [add(row.b, linear(row.a[:-1], partial, r)) for row in neg]
        if lower and upper:
            left, right = max(lower), min(upper)
            assert left < right
            last = scale(F(1, 2), add(left, right))
        elif lower:
            last = add(max(lower), unit)
        elif upper:
            last = add(min(upper), scale(-1, unit))
        else:
            last = zero
        return partial + (last,), None

    p, q = eliminate(rows, d)
    if q is None:
        assert p is not None
        assert all(add(bi, linear(row, p, r)) > zero
                   for row, bi in zip(mat, b))
        return Certificate(p, None, generated)
    denominator = lcm(*(x.denominator for x in q))
    integers = tuple(int(denominator * x) for x in q)
    divisor = gcd(*integers)
    integers = tuple(x // divisor for x in integers)
    assert any(integers) and all(x >= 0 for x in integers)
    assert all(sum(integers[i] * mat[i][j] for i in range(n)) == 0
               for j in range(d))
    assert linear(integers, b, r) <= zero
    return Certificate(None, integers, generated)


def wick_certificate(alphas: Sequence[Sequence[int]],
                     edges: Sequence[tuple[int, int]],
                     coupling_values: Sequence[Value],
                     covariance_values: Sequence[Value], *,
                     max_rows: int = 200_000) -> Certificate:
    """Certify lambda_a + alpha_a.p > 0, c_ij - p_i - p_j > 0.

    Edge indices are zero-based, unique, and i <= j. All listed covariance
    entries and couplings are assumed nonzero; omitted entries are zero.
    An obstruction has coordinates (vertex multiplicities, edge counts).
    """
    if not alphas:
        raise ValueError("Supply at least one interaction monomial.")
    d = len(alphas[0])
    if d == 0 or any(len(a) != d or any(not isinstance(x, int) or x < 0
                                      for x in a) or sum(a) < 1 for a in alphas):
        raise ValueError("Interactions must have nonnegative integer degrees.")
    if len(set(edges)) != len(edges) or any(not 0 <= i <= j < d for i, j in edges):
        raise ValueError("Invalid or repeated covariance edge.")
    if len(coupling_values) != len(alphas) or len(covariance_values) != len(edges):
        raise ValueError("Value counts do not match incidence data.")
    matrix = [tuple(a) for a in alphas]
    for i, j in edges:
        row = [0] * d
        row[i] -= 1
        row[j] -= 1
        matrix.append(tuple(row))
    return strict_alternative(matrix, tuple(coupling_values) + tuple(covariance_values),
                              max_rows=max_rows)


def serializable(cert: Certificate) -> dict:
    return {"balance": None if cert.balance is None else
            [[str(x) for x in v] for v in cert.balance],
            "obstruction": cert.obstruction,
            "generated_rows": cert.generated_rows}


if __name__ == "__main__":
    import json
    sample = wick_certificate([(4, 0), (0, 4)], [(0, 0), (0, 1), (1, 1)],
                              [value([-1]), value([-1])],
                              [value([2]), value([0]), value([2])])
    print(json.dumps(serializable(sample), indent=2))
