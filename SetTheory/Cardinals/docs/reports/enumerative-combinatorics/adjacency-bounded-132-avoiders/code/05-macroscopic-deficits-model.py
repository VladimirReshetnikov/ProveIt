"""Exact Catalan and endpoint-state counts for adjacency-bounded 132-avoiders.

The endpoint recurrence is the Mayama--Akita recurrence, rederived in the
article's Appendix A. All counting arithmetic uses Python integers. These
routines support finite checks; they do not verify the asymptotic proofs.
"""
from __future__ import annotations

from functools import lru_cache
from math import comb

Permutation = tuple[int, ...]


def catalans(max_n: int) -> list[int]:
    """Return the Catalan numbers C_0,...,C_max_n."""
    if max_n < 0:
        raise ValueError("max_n must be nonnegative")
    return [comb(2 * n, n) // (n + 1) for n in range(max_n + 1)]


class Counter:
    """Count avoiders of size N with adjacent differences at most m.

    T(n,u,v) counts the same class with first deficiency at most u and
    last deficiency at most v. Only states with 1 <= n <= N are used.
    The memoized T callable is instance-local, so different bounds cannot
    accidentally share cached states.
    """

    def __init__(self, N: int, m: int) -> None:
        if N < 1 or m < 0:
            raise ValueError("N must be positive and m nonnegative")
        self.N, self.m = N, m
        self.C = catalans(N)
        self.H: list[list[int]] = [[1]]
        for n in range(1, N + 1):
            row: list[int] = []
            total = 0
            for j in range(n):
                first = n - j
                # Exact first-entry count (article, equation (2.5)).
                total += (j + 1) * comb(n + first - 2, n - 1) // n
                row.append(total)
            if total != self.C[n]:
                raise ArithmeticError("first-entry counts do not sum to C_n")
            self.H.append(row)
        self.T = lru_cache(maxsize=None)(self._T)

    def h(self, n: int, u: int) -> int:
        """Count unrestricted n-avoiders with first deficiency <= u."""
        if u < 0:
            return 0
        if n == 0:
            return 1
        return self.H[n][min(u, n - 1)]

    def unrestricted(self, n: int, u: int, v: int) -> int:
        """Both endpoint thresholds, without an adjacency restriction.

        Called only with n >= 1 and nonnegative thresholds. Separate the
        case of final maximum from the other possible final values.
        """
        if n == 1:
            return 1
        return self.h(n - 1, u - 1) + sum(
            self.C[n - q - 1] * self.h(q, u)
            for q in range(1, min(v, n - 1) + 1)
        )

    def _T(self, n: int, u: int, v: int) -> int:
        if min(u, v) < 0:
            return 0
        if n == 1:
            return 1
        u, v = min(u, n - 1), min(v, n - 1)
        if n <= self.m + 1:
            return self.unrestricted(n, u, v)

        # Maximum at the end.
        total = self.T(n - 1, u - 1, self.m - 1)
        # Maximum at position k, followed by a nonempty right block.
        for k in range(1, min(self.m, n - 1) + 1):
            coefficient = 1 if k == 1 else self.h(k - 1, u - 1)
            if coefficient and v >= k:
                right_size = n - k
                total += coefficient * self.T(
                    right_size,
                    min(self.m - k, right_size - 1),
                    min(v - k, right_size - 1),
                )
        return total

    def count(self) -> int:
        """Return a_N^(m), with no endpoint restriction."""
        return self.T(self.N, self.N - 1, self.N - 1)


@lru_cache(maxsize=None)
def av(n: int) -> tuple[Permutation, ...]:
    """Exhaustively generate Av_n(132); use only for small n."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    if n == 0:
        return ((),)
    return tuple(
        tuple(x + b for x in left) + (n,) + right
        for b in range(n)
        for left in av(n - b - 1)
        for right in av(b)
    )


def mx(permutation: Permutation) -> int:
    """Largest adjacent absolute difference; zero for size <= 1."""
    return max(
        (abs(a - b) for a, b in zip(permutation, permutation[1:])), default=0
    )
