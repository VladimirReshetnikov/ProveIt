#!/usr/bin/env python3
"""Independent exact enumeration and midpoint identities for four-direction arrays."""
from __future__ import annotations
from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
from math import comb, factorial, prod


def successors(state: tuple[int,...], n: int):
    for i,x in enumerate(state):
        if x==n:continue
        # Equal adjacent counts are permitted only at 0 and n.
        if i and not (state[i-1]>=x+2 or (x==n-1 and state[i-1]==n)):
            continue
        nxt=list(state);nxt[i]+=1
        yield tuple(nxt)


def count(m: int, n: int) -> int:
    if m<1 or n<0:raise ValueError('m >= 1 and n >= 0 required')
    current={(0,)*m:1}
    for _ in range(m*n):
        nxt=defaultdict(int)
        for state,c in current.items():
            for s in successors(state,n):nxt[s]+=c
        current=nxt
    return current[(n,)*m]


def all_prefixes(m: int,n: int) -> dict[tuple[int,...],int]:
    current={(0,)*m:1}; result=dict(current)
    for _ in range(m*n):
        nxt=defaultdict(int)
        for state,c in current.items():
            for s in successors(state,n):nxt[s]+=c
        result.update(nxt);current=nxt
    return result


def shifted_hook(parts: tuple[int,...]) -> int:
    parts=tuple(x for x in parts if x)
    if any(parts[i]<=parts[i+1] for i in range(len(parts)-1)):
        raise ValueError('positive parts must be strictly decreasing')
    value=F(factorial(sum(parts)),prod(factorial(x) for x in parts))
    for i,x in enumerate(parts):
        for y in parts[i+1:]:value*=F(x-y,x+y)
    assert value.denominator==1
    return value.numerator


def interior_probability(m: int,n: int) -> F:
    """The exact lower bound I_m(n), without the multinomial factor M_m(n)."""
    total=F(0)
    for increasing in combinations(range(1,n),m):
        value=F(prod(comb(n,x) for x in increasing),2**(m*n))
        for i,x in enumerate(increasing):
            for y in increasing[i+1:]:
                value*=F((x-y)**2,(x+y)*(2*n-x-y))
        total+=value
    return total


def unrestricted_word_count(m: int,n: int) -> int:
    return factorial(m*n)//factorial(n)**m


def brute_poset(m: int,n: int) -> int:
    """Bitmask linear-extension count, independent of the row-count DP."""
    N=m*n
    if N>22:raise ValueError('brute_poset is limited to 22 cells')
    pred=[0]*N
    for i in range(m):
        for j in range(n):
            a=i*n+j
            if j:pred[a] |= 1<<(a-1)
            if i:
                pred[a] |= 1<<((i-1)*n+j)
                if j+1<n:pred[a] |= 1<<((i-1)*n+j+1)
    @lru_cache(None)
    def solve(mask: int) -> int:
        if mask==(1<<N)-1:return 1
        return sum(solve(mask|(1<<a)) for a in range(N)
                   if not ((mask>>a)&1) and not (pred[a]&~mask))
    return solve(0)
