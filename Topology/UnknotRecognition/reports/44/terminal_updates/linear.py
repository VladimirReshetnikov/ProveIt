"""Deterministic finite-field rank normal forms, including singular updates.

Maintains left * A * right = diag(I_rank, 0) and
scale * det(left) * det(right) = 1. A rank-one update takes O(d^2)
field operations. The low-level object is mutable; use clone() for transactions.
"""
from __future__ import annotations
from dataclasses import dataclass
from math import isqrt
from time import monotonic
from typing import Sequence

Matrix = list[list[int]]

class BudgetExceeded(RuntimeError):
    """An exact computation was interrupted; this is not a mathematical verdict."""

@dataclass
class Budget:
    units_left: int | None = None
    deadline: float | None = None
    units_used: int = 0

    def tick(self, units: int = 1) -> None:
        if units < 0:
            raise ValueError('negative work charge')
        self.units_used += units
        if self.units_left is not None:
            self.units_left -= units
            if self.units_left < 0:
                raise BudgetExceeded('work allowance exhausted')
        if self.deadline is not None and monotonic() >= self.deadline:
            raise BudgetExceeded('deadline reached')


def tick(budget: Budget | None, units: int = 1) -> None:
    if budget is not None:
        budget.tick(units)


def is_prime(p: int) -> bool:
    """Exact trial division; intended for the small primes used in this package."""
    if type(p) is not int or p < 2:
        return False
    if p % 2 == 0:
        return p == 2
    return all(p % d for d in range(3, isqrt(p)+1, 2))


def eye(n: int) -> Matrix:
    return [[int(i == j) for j in range(n)] for i in range(n)]


def transpose(a: Matrix) -> Matrix:
    return [list(col) for col in zip(*a)] if a else []


def square(a: Sequence[Sequence[int]], p: int) -> Matrix:
    n = len(a)
    if any(len(row) != n for row in a):
        raise ValueError('a square matrix is required')
    if any(type(x) is not int for row in a for x in row):
        raise ValueError('matrix entries must be integers')
    return [[x % p for x in row] for row in a]


def matmul(a: Matrix, b: Matrix, p: int) -> Matrix:
    if not a:
        return []
    if not b:
        if len(a[0]):
            raise ValueError('matrix dimensions disagree')
        return [[] for _ in a]
    if len(a[0]) != len(b):
        raise ValueError('matrix dimensions disagree')
    bt = transpose(b)
    return [[sum(x*y for x, y in zip(row, col)) % p for col in bt] for row in a]


def det_mod(a: Sequence[Sequence[int]], p: int) -> int:
    """Independent static row elimination; does not use DynamicRank."""
    m = square(a, p)
    n, ans = len(m), 1
    for k in range(n):
        pos = next((i for i in range(k, n) if m[i][k]), None)
        if pos is None:
            return 0
        if pos != k:
            m[k], m[pos] = m[pos], m[k]
            ans = -ans
        pivot = m[k][k]
        ans = ans * pivot % p
        inv = pow(pivot, -1, p)
        for i in range(k+1, n):
            c = m[i][k] * inv % p
            if c:
                for j in range(k+1, n):
                    m[i][j] = (m[i][j] - c*m[k][j]) % p
            m[i][k] = 0
    return ans % p


def bareiss(a: Sequence[Sequence[int]]) -> int:
    """Exact integer determinant with checked fraction-free divisions."""
    n = len(a)
    if any(len(row) != n for row in a):
        raise ValueError('a square matrix is required')
    if any(type(x) is not int for row in a for x in row):
        raise ValueError('integer entries required')
    if not n:
        return 1
    m = [list(row) for row in a]
    prev, sign = 1, 1
    for k in range(n-1):
        pos = next((i for i in range(k, n) if m[i][k]), None)
        if pos is None:
            return 0
        if pos != k:
            m[k], m[pos] = m[pos], m[k]
            sign = -sign
        pivot = m[k][k]
        for i in range(k+1, n):
            for j in range(k+1, n):
                numerator = pivot*m[i][j] - m[i][k]*m[k][j]
                value, rem = divmod(numerator, prev)
                if rem:
                    raise ArithmeticError('nonexact Bareiss division')
                m[i][j] = value
            m[i][k] = 0
        prev = pivot
    return sign*m[-1][-1]


class DynamicRank:
    def __init__(self, a: Sequence[Sequence[int]], p: int,
                 budget: Budget | None = None, *, _prime_checked: bool = False):
        if not _prime_checked and not is_prime(p):
            raise ValueError('the modulus must be prime')
        m = square(a, p)
        self.p, self.n = p, len(m)
        self.left, self.right = eye(self.n), eye(self.n)
        self.rank, self.scale = 0, 1
        self.cases = {'tail_left': 0, 'tail_right': 0, 'regular': 0,
                      'rank_drop': 0, 'zero': 0}
        n = self.n
        for k in range(n):
            tick(budget, max(1, (n-k)**2))
            pivot_pos = next(((i, j) for i in range(k, n)
                              for j in range(k, n) if m[i][j]), None)
            if pivot_pos is None:
                break
            i, j = pivot_pos
            if i != k:
                m[k], m[i] = m[i], m[k]
                self._swap_rows(k, i)
            if j != k:
                for row in m:
                    row[k], row[j] = row[j], row[k]
                self._swap_cols(k, j)
            inv = pow(m[k][k], -1, p)
            m[k] = [x*inv % p for x in m[k]]
            self._scale_row(k, inv, budget)
            for i in range(k+1, n):
                c = m[i][k]
                if c:
                    m[i] = [(x-c*y) % p for x, y in zip(m[i], m[k])]
                    self._row_add(i, k, -c, budget)
            # The pivot column is now e_k. Clear the rest of row k by columns.
            for j in range(k+1, n):
                c = m[k][j]
                if c:
                    for i in range(n):
                        m[i][j] = (m[i][j]-c*m[i][k]) % p
                    self._col_add(j, k, -c, budget)
            self.rank += 1

    def clone(self, budget: Budget | None = None) -> 'DynamicRank':
        tick(budget, 2*self.n*self.n+1)
        other = object.__new__(DynamicRank)
        other.p, other.n = self.p, self.n
        other.left = [row[:] for row in self.left]
        other.right = [row[:] for row in self.right]
        other.rank, other.scale = self.rank, self.scale
        other.cases = self.cases.copy()
        return other

    @property
    def determinant(self) -> int:
        return self.scale if self.rank == self.n else 0

    def _swap_rows(self, a: int, b: int) -> None:
        if a != b:
            self.left[a], self.left[b] = self.left[b], self.left[a]
            self.scale = -self.scale % self.p

    def _swap_cols(self, a: int, b: int) -> None:
        if a != b:
            for row in self.right:
                row[a], row[b] = row[b], row[a]
            self.scale = -self.scale % self.p

    def _scale_row(self, i: int, c: int, budget: Budget | None) -> None:
        tick(budget, self.n+1)
        p = self.p
        c %= p
        if not c:
            raise ArithmeticError('zero row scaling is forbidden')
        self.left[i] = [c*x % p for x in self.left[i]]
        self.scale = self.scale * pow(c, -1, p) % p

    def _scale_col(self, j: int, c: int, budget: Budget | None) -> None:
        tick(budget, self.n+1)
        p = self.p
        c %= p
        if not c:
            raise ArithmeticError('zero column scaling is forbidden')
        for row in self.right:
            row[j] = row[j]*c % p
        self.scale = self.scale * pow(c, -1, p) % p

    def _row_add(self, dst: int, src: int, c: int, budget: Budget | None) -> None:
        tick(budget, self.n)
        p = self.p
        self.left[dst] = [(x+c*y) % p for x, y in zip(self.left[dst], self.left[src])]

    def _col_add(self, dst: int, src: int, c: int, budget: Budget | None) -> None:
        tick(budget, self.n)
        p = self.p
        for row in self.right:
            row[dst] = (row[dst]+c*row[src]) % p

    def update(self, u: Sequence[int], v: Sequence[int],
               budget: Budget | None = None) -> str:
        """Replace A by A+u*v^T. For atomic publication, update a clone."""
        n, p, r = self.n, self.p, self.rank
        if len(u) != n or len(v) != n:
            raise ValueError('update vector dimensions disagree')
        if any(type(z) is not int for z in (*u, *v)):
            raise ValueError('update vectors must be integral')
        tick(budget, 1)
        x, y = [], []
        for row in self.left:
            tick(budget, n)
            x.append(sum(a*b for a, b in zip(row, u)) % p)
        for j in range(n):
            tick(budget, n)
            y.append(sum(v[i]*self.right[i][j] for i in range(n)) % p)
        if not any(x) or not any(y):
            self.cases['zero'] += 1
            return 'zero'
        if any(x[r:]):
            self._tail_update(x, y, budget)
            case = 'tail_left'
        elif any(y[r:]):
            # Transpose the whole invariant; a column-side tail is now a row tail.
            self.left, self.right = transpose(self.right), transpose(self.left)
            self._tail_update(y, x, budget)
            self.left, self.right = transpose(self.right), transpose(self.left)
            case = 'tail_right'
        else:
            alpha = (1+sum(x[i]*y[i] for i in range(r))) % p
            if alpha:
                inv = pow(alpha, -1, p)
                h = []
                for j in range(n):
                    tick(budget, r)
                    h.append(sum(y[i]*self.left[i][j] for i in range(r)) % p)
                for i in range(r):
                    if x[i]:
                        c = x[i]*inv % p
                        tick(budget, n)
                        self.left[i] = [(a-c*b) % p for a, b in zip(self.left[i], h)]
                self.scale = self.scale*alpha % p
                case = 'regular'
            else:
                self._drop_update(x, y, budget)
                case = 'rank_drop'
        self.cases[case] += 1
        tick(budget, 1)
        return case

    def _tail_update(self, x: list[int], y: list[int], budget: Budget | None) -> None:
        n, r, p = self.n, self.rank, self.p
        k = next(i for i in range(r, n) if x[i])
        self._swap_rows(r, k)
        x[r], x[k] = x[k], x[r]
        self._scale_row(r, pow(x[r], -1, p), budget)
        x[r] = 1
        # The original row r in J is zero: these operations preserve J.
        for i in range(n):
            if i != r and x[i]:
                self._row_add(i, r, -x[i], budget)
        # The update is now e_r*y. Remove its active columns.
        for i in range(r):
            if y[i]:
                self._row_add(r, i, -y[i], budget)
        k = next((i for i in range(r, n) if y[i]), None)
        if k is None:
            return
        self._swap_cols(r, k)
        y[r], y[k] = y[k], y[r]
        c = y[r]
        inv = pow(c, -1, p)
        self._scale_row(r, inv, budget)
        for j in range(r+1, n):
            if y[j]:
                self._col_add(j, r, -y[j]*inv, budget)
        self.rank += 1

    def _drop_update(self, x: list[int], y: list[int], budget: Budget | None) -> None:
        r, p, n = self.rank, self.p, self.n
        t = r-1
        k = next(i for i in range(r) if x[i])
        # Active conjugation S*J*S^{-1}=J, taking x to e_t.
        self._swap_rows(t, k)
        self._swap_cols(t, k)
        x[t], x[k] = x[k], x[t]
        y[t], y[k] = y[k], y[t]
        c = x[t]
        self._scale_row(t, pow(c, -1, p), budget)
        self._scale_col(t, c, budget)
        y[t] = y[t]*c % p
        for i in range(t):
            if x[i]:
                self._row_add(i, t, -x[i], budget)
                self._col_add(t, i, x[i], budget)
                y[t] = (y[t]+x[i]*y[i]) % p
        if y[t] != (-1 % p):
            raise ArithmeticError('rank-drop normalization identity failed')
        for i in range(t):
            if y[i]:
                self._row_add(t, i, -y[i], budget)
        self.rank -= 1

    def certificate(self) -> dict:
        return dict(p=self.p, rank=self.rank, scale=self.scale,
                    left=[row[:] for row in self.left],
                    right=[row[:] for row in self.right])


def verify_normal_form(a: Matrix, certificate: dict) -> bool:
    """Deterministic cubic verifier, independent of the updating algorithm."""
    try:
        p = certificate['p']
        if not is_prime(p):
            return False
        m = square(a, p)
        n = len(m)
        l, rr = square(certificate['left'], p), square(certificate['right'], p)
        rank, scale = certificate['rank'], certificate['scale']
        if len(l) != n or len(rr) != n or type(rank) is not int or not 0 <= rank <= n:
            return False
        if type(scale) is not int:
            return False
        if scale*det_mod(l, p)*det_mod(rr, p) % p != 1:
            return False
        target = [[int(i == j and i < rank) for j in range(n)] for i in range(n)]
        return matmul(matmul(l, m, p), rr, p) == target
    except (ValueError, TypeError, KeyError, ArithmeticError, IndexError):
        return False
