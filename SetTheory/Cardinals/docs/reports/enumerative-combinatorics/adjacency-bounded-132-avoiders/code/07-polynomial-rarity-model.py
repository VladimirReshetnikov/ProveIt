"""Exact counts for adjacency-bounded 132-avoiding permutations.

The endpoint DP is an independently packaged adaptation of the Mayama--Akita
recurrence and ProveIt's 05-macroscopic-deficits-model.py (blob f0248e0d61...).
All counting operations use integers. These tests are not asymptotic proofs.
"""
from __future__ import annotations
from functools import lru_cache
from math import comb
from typing import Iterator


def catalans(n: int) -> list[int]:
    if n < 0:
        raise ValueError("n must be nonnegative")
    return [comb(2*k, k)//(k+1) for k in range(n+1)]


@lru_cache(None)
def avoiders(n: int) -> tuple[tuple[int, ...], ...]:
    if n < 0:
        raise ValueError("n must be nonnegative")
    if n == 0:
        return ((),)
    return tuple(tuple(x+r for x in left)+(n,)+right
                 for r in range(n)
                 for left in avoiders(n-r-1)
                 for right in avoiders(r))


def avoids132(p: tuple[int, ...]) -> bool:
    return not any(p[i] < p[k] < p[j]
                   for i in range(len(p))
                   for j in range(i+1, len(p))
                   for k in range(j+1, len(p)))


def max_jump(p: tuple[int, ...]) -> int:
    return max((abs(x-y) for x,y in zip(p,p[1:])), default=0)


class EndpointCounter:
    """Count size N avoiders with jump bound m, using exact endpoint states."""
    def __init__(self, N: int, m: int) -> None:
        if N < 1 or m < 0:
            raise ValueError("N must be positive and m nonnegative")
        self.N, self.m = N, m
        self.C = catalans(N)
        self.H = [[1]]
        for n in range(1, N+1):
            row, total = [], 0
            for d in range(n):
                total += (d+1)*comb(2*n-d-2,n-1)//n
                row.append(total)
            assert total == self.C[n]
            self.H.append(row)
        self.unrestricted = lru_cache(None)(self._unrestricted)
        self.T = lru_cache(None)(self._T)

    def h(self, n: int, u: int) -> int:
        if u < 0:
            return 0
        if n == 0:
            return 1
        return self.H[n][min(u,n-1)]

    def _unrestricted(self, n: int, u: int, v: int) -> int:
        if n == 1:
            return 1
        return self.h(n-1,u-1)+sum(
            self.C[n-j-1]*self.h(j,u)
            for j in range(1,min(v,n-1)+1))

    def _T(self, n: int, u: int, v: int) -> int:
        if min(u,v) < 0:
            return 0
        if n == 1:
            return 1
        u,v = min(u,n-1),min(v,n-1)
        if n <= self.m+1:
            return self.unrestricted(n,u,v)
        total = self.T(n-1,u-1,self.m-1)
        for k in range(1,min(self.m,n-1)+1):
            a = 1 if k == 1 else self.h(k-1,u-1)
            if a and v >= k:
                r = n-k
                total += a*self.T(r,min(self.m-k,r-1),min(v-k,r-1))
        return total

    def count(self) -> int:
        return self.T(self.N,self.N-1,self.N-1)


def envelopes(nmax: int, m: int) -> tuple[list[int], list[int]]:
    """Return lower L_m and upper B_m coefficient sequences through nmax."""
    if nmax < 0 or m < 2:
        raise ValueError("nmax >= 0 and m >= 2 required")
    C = catalans(nmax)
    lo,hi = [0]*(nmax+1),[0]*(nmax+1)
    lo[0]=hi[0]=1
    if nmax:
        hi[1]=1
    for n in range(1,nmax+1):
        lo[n]=lo[n-1]+sum(C[k-2]*lo[n-k]
                         for k in range(2,min(m-1,n)+1))
        if n>=2:
            hi[n]=hi[n-1]+sum(C[k-1]*hi[n-k]
                              for k in range(1,min(m,n-1)+1))
    return lo,hi


def skew(a: tuple[int,...], b: tuple[int,...]) -> tuple[int,...]:
    return tuple(x+len(b) for x in a)+b


@lru_cache(None)
def blocks(k: int) -> tuple[tuple[int,...],...]:
    if k == 1:
        return ((1,),)
    if k < 1:
        raise ValueError("block size must be positive")
    return tuple((k-1,)+p+(k,) for p in avoiders(k-2))


def lower_objects(n: int, m: int) -> Iterator[tuple[int,...]]:
    if n == 0:
        yield ()
    for k in range(1,min(m-1,n)+1):
        for b in blocks(k):
            for tail in lower_objects(n-k,m):
                yield skew(b,tail)


def proxy(n: int, m: int, q: int) -> float:
    """The theorem's order scale, not a probability approximation."""
    if n<1 or q<2:
        raise ValueError("n>=1 and q>=2 required")
    delta=max(q*m-n,0)
    return n**(-q/2)+n**(-3*(q-1)/2)*delta**(q-1)
