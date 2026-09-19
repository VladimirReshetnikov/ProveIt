#!/usr/bin/env python3
"""Exact diagonal Hardinian-array counts and proved asymptotic constants.

The main counter uses only Python's standard library.  See article.tex for
proofs of all identities.  No floating-point arithmetic is used for counts.

Usage:
    python code/hardinian.py 40 --max-r 7
    python code/hardinian.py 12 --max-r 11 --method generic
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction
from itertools import combinations
from math import comb, factorial
from typing import Sequence

Matrix = list[list[int]]


def _nonnegative_int(value: int, name: str) -> None:
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        raise ValueError(f"{name} must be a nonnegative integer")


def skew_pascal(size: int) -> Matrix:
    """A = B J B^T, with B the size x size lower Pascal matrix.

    A[0,j] = 2**j - 1; A[i,i] = 0; A[i,j] = -A[j,i];
    A[i,j] = A[i-1,j] + A[i,j-1] for 0 < i < j.
    This construction takes O(size**2) integer additions.
    """
    _nonnegative_int(size, "size")
    a = [[0] * size for _ in range(size)]
    if size:
        for j in range(1, size):
            a[0][j] = (1 << j) - 1
            a[j][0] = -a[0][j]
        for i in range(1, size):
            for j in range(i + 1, size):
                a[i][j] = a[i - 1][j] + a[i][j - 1]
                a[j][i] = -a[i][j]
    return a


def matvec(a: Matrix, v: Sequence[int]) -> list[int]:
    return [sum(x * y for x, y in zip(row, v)) for row in a]


def matmul(a: Matrix, b: Matrix) -> Matrix:
    if not a:
        return []
    bt = list(zip(*b))
    return [[sum(x * y for x, y in zip(row, col)) for col in bt] for row in a]


def _skew_square(a: Matrix) -> Matrix:
    n = len(a)
    q = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i, n):
            q[i][j] = q[j][i] = -sum(x * y for x, y in zip(a[i], a[j]))
    return q


def _trace_cube_symmetric(q: Matrix) -> int:
    """tr(Q^3), without constructing Q^2."""
    n = len(q)
    total = sum(q[i][i] ** 3 for i in range(n))
    for i in range(n):
        for j in range(i + 1, n):
            total += 3 * (q[i][i] + q[j][j]) * q[i][j] ** 2
            ij = q[i][j]
            total += 6 * ij * sum(q[j][k] * q[i][k] for k in range(j + 1, n))
    return total


def counts(n: int, max_r: int = 7, *, method: str = "auto") -> list[int]:
    """Return [H_0(n,n),...,H_max_r(n,n)].  n must be positive.

    'auto' uses skew traces through r=7 and otherwise a generic Newton
    algorithm. 'generic' independently extracts det(I+t(A+vv^T)).
    Counts with r >= n are zero.  Integer divisions are checked.
    """
    _nonnegative_int(n, "n")
    _nonnegative_int(max_r, "max_r")
    if n == 0:
        raise ValueError("n must be positive")
    if method not in ("auto", "generic"):
        raise ValueError("method must be 'auto' or 'generic'")
    limit = min(max_r, n - 1)
    a = skew_pascal(n - 1)
    v = [1 << j for j in range(n - 1)]
    if method == "generic" or limit > 7:
        c = [[a[i][j] + v[i] * v[j] for j in range(n - 1)]
             for i in range(n - 1)]
        powers = c
        traces = [0]
        coefficients = [1]
        for k in range(1, limit + 1):
            traces.append(sum(powers[i][i] for i in range(n - 1)))
            numer = sum((-1) ** (j - 1) * traces[j] * coefficients[k - j]
                        for j in range(1, k + 1))
            value, rem = divmod(numer, k)
            if rem:
                raise ArithmeticError("nonintegral Newton coefficient")
            coefficients.append(value)
            if k < limit:
                powers = matmul(powers, c)
        return coefficients + [0] * (max_r - limit)

    # tr(A^(2j)), needed for det(I+tA).
    traces_even = [0]
    if limit >= 2:
        traces_even.append(-sum(x * x for row in a for x in row))
    if limit >= 4:
        q = _skew_square(a)
        traces_even.append(sum(x * x for row in q for x in row))
    if limit >= 6:
        traces_even.append(_trace_cube_symmetric(q))
    e = [1]
    for m in range(1, limit // 2 + 1):
        numer = -sum(traces_even[j] * e[m - j] for j in range(1, m + 1))
        value, rem = divmod(numer, 2 * m)
        if rem:
            raise ArithmeticError("nonintegral skew Newton coefficient")
        e.append(value)

    # v^T A^(2j) v = (-1)^j ||A^j v||^2.
    b = []
    w = v
    for j in range((limit + 1) // 2):
        b.append((-1) ** j * sum(x * x for x in w))
        if j + 1 < (limit + 1) // 2:
            w = matvec(a, w)
    result = []
    for r in range(limit + 1):
        if r % 2 == 0:
            result.append(e[r // 2])
        else:
            m = r // 2
            result.append(sum(e[m - j] * b[j] for j in range(m + 1)))
    if any(x < 0 for x in result):
        raise ArithmeticError("negative counting coefficient")
    return result + [0] * (max_r - limit)


def rational_constant(r: int) -> Fraction:
    """Q_r = C_r * pi**floor(r/2), returned exactly."""
    _nonnegative_int(r, "r")
    q = [Fraction(1), Fraction(1, 12)]
    for k in range(r - 1):
        factor = Fraction(2) ** (2 * k - 2) * factorial(k) ** 2 / 3 ** (4 * k + 4)
        q.append(q[k] * factor)
    return q[r]


def bareiss(a: Sequence[Sequence[int]]) -> int:
    """Exact determinant with pivoting; det of the empty matrix is 1."""
    n = len(a)
    if any(len(row) != n for row in a):
        raise ValueError("matrix must be square")
    if not n:
        return 1
    b = [list(row) for row in a]
    old = 1
    sign = 1
    for k in range(n - 1):
        if b[k][k] == 0:
            pivot_row = next((i for i in range(k + 1, n) if b[i][k]), None)
            if pivot_row is None:
                return 0
            b[k], b[pivot_row] = b[pivot_row], b[k]
            sign = -sign
        pivot = b[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                numer = pivot * b[i][j] - b[i][k] * b[k][j]
                b[i][j], rem = divmod(numer, old)
                if rem:
                    raise ArithmeticError("nonintegral Bareiss update")
            b[i][k] = 0
        old = pivot
    return sign * b[-1][-1]


def pfaffian(a: Sequence[Sequence[int]]) -> int:
    """Small exact recursive Pfaffian, for independent checks only."""
    n = len(a)
    if n % 2 or any(len(row) != n for row in a):
        raise ValueError("Pfaffian requires even square size")
    if not n:
        return 1
    total = 0
    for j in range(1, n):
        inds = [i for i in range(1, n) if i != j]
        minor = [[a[k][l] for l in inds] for k in inds]
        total += (-1) ** (j + 1) * a[0][j] * pfaffian(minor)
    return total


def direct_minor_count(n: int, r: int) -> int:
    """Original complementary-minor formula; exponential reference method."""
    if not (0 <= r < n):
        return 0
    N = n - 1
    inds = list(combinations(range(N), N - r))
    return sum(bareiss([[comb(i + j, i) for j in cols] for i in rows])
               for rows in inds for cols in inds)


def square_minor_count(n: int, r: int) -> int:
    """Positive sum-of-squares formula; exponential reference method."""
    if not (0 <= r < n):
        return 0
    inds = list(combinations(range(n - 1), r))
    return sum(sum(bareiss([[comb(i, j) if j <= i else 0 for j in cols]
                           for i in rows]) for cols in inds) ** 2 for rows in inds)


def array_count(n: int, r: int) -> int:
    """Independent row dynamic program applying the array definition directly.

    Intended for small n.  No determinant identity enters this method.
    """
    if not (0 <= r < n):
        return 0
    bottom = n - 1 - r
    states: dict[tuple[int, ...], int] = {(): 1}
    for i in range(n):
        new: dict[tuple[int, ...], int] = {}
        for prev, multiplicity in states.items():
            def extend(row: list[int]) -> None:
                j = len(row)
                if j == n:
                    key = tuple(row)
                    new[key] = new.get(key, 0) + multiplicity
                    return
                lo = max(0, max(i, j) - r)
                hi = min(max(i, j), bottom)
                neighbors = ([] if not row else [row[-1]])
                if i:
                    neighbors.append(prev[j])
                    if j:
                        neighbors.append(prev[j - 1])
                if neighbors:
                    lo = max(lo, max(neighbors))
                    hi = min(hi, min(x + 1 for x in neighbors))
                if i == j == 0:
                    lo = hi = 0
                if i == j == n - 1:
                    lo = max(lo, bottom)
                    hi = min(hi, bottom)
                for value in range(lo, hi + 1):
                    row.append(value)
                    extend(row)
                    row.pop()
            extend([])
        states = new
    return sum(states.values())


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int)
    parser.add_argument("--max-r", type=int, default=7)
    parser.add_argument("--method", choices=("auto", "generic"), default="auto")
    args = parser.parse_args()
    try:
        h = counts(args.n, args.max_r, method=args.method)
    except (ValueError, ArithmeticError) as exc:
        parser.error(str(exc))
    print(json.dumps({"n": args.n, "counts": [str(x) for x in h],
                      "constants": [{"r": r,
                                     "rational_prefactor": str(rational_constant(r)),
                                     "pi_exponent": -(r // 2)}
                                    for r in range(args.max_r + 1)]}, indent=2))


if __name__ == "__main__":
    main()
