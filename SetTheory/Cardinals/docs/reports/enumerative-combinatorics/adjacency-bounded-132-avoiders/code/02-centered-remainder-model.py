"""Exact finite objects for adjacency-bounded 132-avoiders.

No floating point arithmetic is used in this module. These routines support
finite checks; the all-m theorems are proved in the accompanying article.
"""
from functools import lru_cache
from fractions import Fraction
from math import comb
from typing import Iterable

@lru_cache(None)
def catalan(n: int) -> int:
    if n < 0:
        return 0
    return comb(2*n, n)//(n+1)

@lru_cache(None)
def first_entry(k: int, j: int) -> int:
    """Number of length-k blocks ending at max with first deficiency j."""
    if k == 1:
        return int(j == 0)
    if not (1 <= j < k):
        return 0
    numerator = j * comb(2*k-j-3, k-2)
    assert numerator % (k-1) == 0
    return numerator//(k-1)

@lru_cache(None)
def cumulative(k: int, p: int) -> int:
    if p < 0:
        return 0
    if k == 1:
        return 1
    return sum(first_entry(k, j) for j in range(1, min(p, k-1)+1))

def scalar_coefficients(m: int, d: int | None = None) -> list[int]:
    if m < 1:
        raise ValueError('m must be positive')
    if d is None:
        return [0] + [catalan(k-1) for k in range(1, m+1)]
    if not 1 <= d < m:
        raise ValueError('block bound requires 1 <= d < m')
    return [0] + [cumulative(k, d) for k in range(1, m-d+1)]

def eval_poly(coeffs: Iterable[int], x: Fraction) -> Fraction:
    value = Fraction(0)
    for a in reversed(list(coeffs)):
        value = value*x+a
    return value

def isolate_root(coeffs: list[int], bits: int = 42) -> tuple[Fraction, Fraction]:
    """Outward exact interval for the positive root of P(x)=1."""
    if (bits < 1 or len(coeffs) < 2 or coeffs[0] != 0
            or not any(coeffs[1:]) or any(a < 0 for a in coeffs)):
        raise ValueError('invalid positive-polynomial isolation problem')
    lo, hi = Fraction(0), Fraction(1)
    while eval_poly(coeffs, hi) < 1:
        hi *= 2
    for _ in range(bits):
        mid = (lo+hi)/2
        if eval_poly(coeffs, mid) < 1:
            lo = mid
        else:
            hi = mid
    assert eval_poly(coeffs, lo) <= 1 <= eval_poly(coeffs, hi)
    return lo, hi

def component(m: int, kind: str):
    """Return states and edges (row, column, degree, integer multiplicity)."""
    if m < 2 or kind not in {'U', 'V'}:
        raise ValueError('use m >= 2 and kind U or V')
    if kind == 'U':
        states = [(p, -1) for p in range(m)]  # -1 denotes infinity here only
    else:
        states = [(p,q) for p in range(m) for q in range(p)]
        states += [(p,m-1) for p in range(m-1)]
    index = {state: i for i, state in enumerate(states)}
    edges = []
    for i, (p,q) in enumerate(states):
        for k in range(1, m+1):
            target = (m-k, -1 if kind == 'U' else q-k)
            a = cumulative(k,p)
            if a and target in index:
                edges.append((i,index[target],k,a))
        if kind == 'V' and p >= 1:
            edges.append((i,index[(p-1,m-1)],1,1))
    return states, edges

@lru_cache(None)
def avoiders(n: int) -> tuple[tuple[int, ...], ...]:
    if n == 0:
        return ((),)
    out = []
    for ell in range(n):
        r = n-1-ell
        for left in avoiders(ell):
            for right in avoiders(r):
                out.append(tuple(a+r for a in left)+(n,)+right)
    return tuple(out)

def avoids_132(p: tuple[int, ...]) -> bool:
    return all(not(p[i] < p[k] < p[j])
               for i in range(len(p)) for j in range(i+1,len(p))
               for k in range(j+1,len(p)))
