"""Exact shifted-rectangle enumerators. Python 3.10+, standard library only."""
from __future__ import annotations
from functools import lru_cache
from itertools import combinations, permutations
from math import factorial, prod
from fractions import Fraction
from collections import Counter


def legal(x: tuple[int, ...], n: int) -> bool:
    return all(0 <= a <= n for a in x) and all(
        a > b or a == b in (0, n) for a, b in zip(x, x[1:]))


def count(m: int, n: int, rare: bool = False) -> int:
    """Unit-step prefix DP; rare adds the poset relation (1,n)<(m,1)."""
    if m < 1 or n < 0 or (rare and m < 2):
        raise ValueError('Require m>=1, n>=0; rare requires m>=2')
    if n == 0:
        return 0 if rare else 1
    @lru_cache(None)
    def visit(x):
        if x == (n,) * m:
            return 1
        ans = 0
        for i in range(m):
            if x[i] == n:
                continue
            if rare and i == m-1 and x[i] == 0 and x[0] < n:
                continue
            y = x[:i] + (x[i]+1,) + x[i+1:]
            if legal(y, n):
                ans += visit(y)
        return ans
    return visit((0,) * m)


def bitmask_count(m: int, n: int, rare: bool = False) -> int:
    """Independent poset-ideal enumeration, practical only for small mn."""
    N=m*n
    pre=[0]*N
    def edge(i,j,k,l):
        pre[k*n+l] |= 1 << (i*n+j)
    for i in range(m):
        for j in range(n):
            if j+1<n: edge(i,j,i,j+1)
            if i+1<m:
                edge(i,j,i+1,j)
                if j+1<n: edge(i,j+1,i+1,j)
    if rare and n: edge(0,n-1,m-1,0)
    @lru_cache(None)
    def visit(mask):
        if mask==(1<<N)-1: return 1
        return sum(visit(mask | (1<<j)) for j in range(N)
                   if not(mask>>j&1) and pre[j]&mask==pre[j])
    return visit(0)


@lru_cache(None)
def signed_perms(r: int):
    return tuple((p, (-1)**sum(p[i]>p[j] for i in range(r) for j in range(i+1,r)))
                 for p in permutations(range(r)))


@lru_cache(None)
def chamber(u: tuple[int,...], v: tuple[int,...]) -> int:
    """Reflection determinant as a signed sum of integer multinomials."""
    if len(u)!=len(v): raise ValueError('Endpoint dimensions differ')
    if not u: return 1
    if any(a>b for a,b in zip(u,v)): return 0
    L=sum(v)-sum(u)
    ans=0
    for p, sign in signed_perms(len(u)):
        ds=[v[i]-u[p[i]] for i in range(len(u))]
        if min(ds)>=0:
            ans += sign * (factorial(L)//prod(factorial(d) for d in ds))
    return ans


def chamber_dp(u: tuple[int,...], v: tuple[int,...]) -> int:
    @lru_cache(None)
    def visit(x):
        if x==v: return 1
        return sum(visit(x[:i]+(x[i]+1,)+x[i+1:]) for i in range(len(x))
                   if x[i]<v[i] and (i==0 or x[i]+1<x[i-1]))
    if any(a>b for a,b in zip(u,v)): return 0
    return visit(u)


def dyck_words(m: int):
    def go(w,b,d):
        if b==d==m:
            yield w
        if b<m: yield from go(w+'B',b+1,d)
        if d<b: yield from go(w+'D',b,d+1)
    yield from go('',0,0)


def event_counts(m: int, n: int) -> dict[str,int]:
    """Independent event-skeleton evaluation using chamber determinants."""
    if n<2: raise ValueError('Birth/death events must be distinct: n>=2')
    tuples={r: tuple(tuple(reversed(c)) for c in combinations(range(1,n),r))
            for r in range(m+1)}
    @lru_cache(None)
    def visit(b,d,u):
        if d==m: return (('',1),)
        result=Counter()
        for v in tuples[b-d]:
            weight=chamber(u,v)
            if not weight: continue
            if b<m and (not v or v[-1]>=2):
                for tail,c in visit(b+1,d,v+(1,)):
                    result['B'+tail] += weight*c
            if v and v[0]==n-1:
                for tail,c in visit(b,d+1,v[1:]):
                    result['D'+tail] += weight*c
        return tuple(sorted(result.items()))
    return dict(visit(0,0,()))


def height(w: str) -> int:
    t=h=0
    for c in w:
        t+=1 if c=='B' else -1
        h=max(h,t)
    return h


def hook(parts: tuple[int,...]) -> int:
    """Classical shifted hook product for strict positive partitions."""
    if any(x<=0 for x in parts) or any(a<=b for a,b in zip(parts,parts[1:])):
        raise ValueError('Parts must be strictly decreasing and positive')
    v=Fraction(factorial(sum(parts)),prod(factorial(x) for x in parts))
    for i in range(len(parts)):
        for j in range(i+1,len(parts)):
            v *= Fraction(parts[i]-parts[j],parts[i]+parts[j])
    assert v.denominator==1
    return v.numerator


def rare_core(m: int, n: int) -> int:
    """Exact positive-middle part of R_m, from the first-completion hook cut."""
    if m<2 or n<2: raise ValueError('Require m,n>=2')
    r=m-2
    return sum(hook((n-1,)+tuple(reversed(c))) * hook((n,)+tuple(n-x for x in c))
               for c in combinations(range(1,n-1),r))
