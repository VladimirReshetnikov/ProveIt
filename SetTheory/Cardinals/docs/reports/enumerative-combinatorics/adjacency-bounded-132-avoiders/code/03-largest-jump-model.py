"""Exact computations for the largest-jump boundary law.

All probability coefficients use fractions.Fraction. No numerical output is
used as a substitute for the proofs in article.tex.
"""
from __future__ import annotations
from fractions import Fraction as F
from functools import lru_cache
from math import comb
from typing import TypeAlias

Series: TypeAlias = list[F]
Permutation: TypeAlias = tuple[int, ...]


def catalan(n: int) -> int:
    if n < 0:
        return 0
    return comb(2*n, n)//(n+1)


def mul(a: Series, b: Series, n: int) -> Series:
    return [sum((a[j]*b[k-j] for j in range(k+1)), F(0))
            for k in range(n+1)]


def inverse(a: Series, n: int) -> Series:
    if not a[0]:
        raise ValueError("A power-series inverse needs a nonzero constant.")
    b = [1/a[0]] + [F(0)]*n
    for k in range(1, n+1):
        b[k] = -sum((a[j]*b[k-j] for j in range(1, k+1)), F(0))/a[0]
    return b


def sqrt_one(a: Series, n: int) -> Series:
    if a[0] != 1:
        raise ValueError("sqrt_one requires constant coefficient 1.")
    b = [F(1)] + [F(0)]*n
    for k in range(1, n+1):
        b[k] = (a[k]-sum((b[j]*b[k-j] for j in range(1, k)), F(0)))/2
    return b


def probability_series(n: int) -> tuple[Series, Series, Series]:
    """Return coefficients of G (law), A (clipping correction), and K."""
    if n < 1:
        raise ValueError("n must be positive")
    q = [F(0)]+[F(catalan(k-1), 4**k) for k in range(1, n+1)]
    one_minus_q = [-v for v in q]
    one_minus_q[0] += 1
    r = sqrt_one(one_minus_q, n)
    one_minus_r = [-v for v in r]
    one_minus_r[0] += 1
    den = [-4*v for v in q]
    den[0] += 3
    invden = inverse(den, n)
    a = [v/2 for v in mul(mul(q, one_minus_r, n), invden, n)]
    kseries = [q[k]+a[k]-(a[k-1] if k else 0) for k in range(n+1)]
    h = mul(q, invden, n)
    inv_one_minus_q = inverse(one_minus_q, n)
    j = [v/4 for v in mul(kseries,
                         mul(inv_one_minus_q, inv_one_minus_q, n), n)]
    return [h[k]+j[k] for k in range(n+1)], a, kseries


def first_count(n: int, first: int) -> int:
    """Number of 132-avoiders of length n with given first value."""
    if not 1 <= first <= n:
        return 0
    return (n-first+1)*comb(n+first-2, n-1)//n


def independent_clipping(n: int) -> Series:
    """A coefficients from endpoint tails, not the closed form for A.

    P(z)=z/(1+2 sqrt(1-z)) enumerates first values at Catalan
    Boltzmann parameter 1/4. Only its coefficients and finite endpoint
    counts enter this separate calculation.
    """
    sqrt = [F(1)]
    for k in range(1, n+1):
        sqrt.append(sqrt[-1]*F(2*k-3, 2*k))
    p = [F(0)]*(n+1)
    for k in range(1, n+1):
        p[k] = (4*p[k-1]+2*sqrt[k-1]-(1 if k == 1 else 0))/3
    a = [F(0)]*(n+1)
    for k in range(1, n+1):
        for f in range(1, k):
            tail = p[f]-sum((F(first_count(t, f), 4**t)
                            for t in range(f, k)), F(0))
            a[k] += tail*sum((F(catalan(b), 16*4**b)
                             for b in range(k-f)), F(0))
    return a


@lru_cache(maxsize=None)
def avoiders(n: int) -> tuple[Permutation, ...]:
    """Catalan recursion at the maximum; intended only for small n."""
    if n == 0:
        return ((),)
    ans = []
    for left_size in range(n):
        right_size = n-1-left_size
        for left in avoiders(left_size):
            for right in avoiders(right_size):
                ans.append(tuple(v+right_size for v in left)+(n,)+right)
    return tuple(ans)


def avoids_132(p: Permutation) -> bool:
    """Independent direct pattern test."""
    return not any(p[i] < p[k] < p[j]
                   for i in range(len(p)) for j in range(i+1, len(p))
                   for k in range(j+1, len(p)))


def deficit(p: Permutation) -> int:
    if not p:
        raise ValueError("The empty permutation has no deficit convention here.")
    return len(p)-max((abs(a-b) for a, b in zip(p, p[1:])), default=0)


# A skeleton is (tag, finite decoration, child); the terminal has child None.
@lru_cache(maxsize=None)
def skeletons(cost: int) -> tuple[tuple, ...]:
    if cost < 2:
        return ()
    ans = [("T", tau, None) for tau in avoiders(cost-1)]
    ans.extend(("A", (), child) for child in skeletons(cost-1))
    for b in range(cost-2):
        for beta in avoiders(b):
            ans.extend(("R", beta, child)
                       for child in skeletons(cost-b-1))
    return tuple(ans)


def skeleton_value(skeleton: tuple) -> tuple[int, int | None]:
    """The limit pair (deficit, finite last value or None for infinity)."""
    tag, beta, child = skeleton
    if tag == "T":
        return beta[0], beta[-1]
    d, last = skeleton_value(child)
    if tag == "A":
        return min(d+1, last) if last is not None else d+1, None
    return d+len(beta)+1, last


def reconstruct(skeleton: tuple, hole: Permutation) -> Permutation:
    tag, beta, child = skeleton
    if tag == "T":
        b = len(beta)
        return tuple(v+b for v in hole)+(len(hole)+b+1,)+beta
    core = reconstruct(child, hole)
    if tag == "A":
        return core+(len(core)+1,)
    return tuple(v+len(core) for v in beta)+(len(core)+len(beta)+1,)+core


def skeleton_tail(h: int) -> F:
    """Exact P(T > h) for the total skeleton cost."""
    if h < 0:
        return F(1)
    return F(2*(h+1)*(2*h+1)*catalan(h), (h+2)*4**h)
