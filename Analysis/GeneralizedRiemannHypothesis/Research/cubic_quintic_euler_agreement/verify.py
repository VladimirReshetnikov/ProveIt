#!/usr/bin/env python3
"""Exact finite tests of the agreement theorem. Requires NumPy.
No floating point, zero lists, or unverified prime samples enter these tests.
The proof in paper.tex, not enumeration, establishes the general theorem.
"""
from itertools import product, combinations_with_replacement
from collections import Counter
import numpy as np


def vectors(p,r):
    return list(product(range(p),repeat=r))


def directions(p,r):
    return [x for x in vectors(p,r) if any(x) and next(v for v in x if v)!=0
            and next(v for v in x if v)==1]


def bound_count(p,r,k):
    s=0
    while p**(s+1)<=k: s+=1
    b=k//p**s
    if s>=r-1: return 1  # projective directions, not nonzero vectors
    return (p-b+1)*p**(r-s-2)


def exhaustive(p,r,k):
    vs=np.asarray(vectors(p,r),dtype=np.int64)
    ds=np.asarray(directions(p,r),dtype=np.int64)
    # Base k+1 encoding of projection histograms is injective.
    a=(k+1)**((vs@ds.T)%p)
    packets=np.array(list(combinations_with_replacement(range(len(vs)),k)),dtype=np.int64)
    signatures=a[packets].sum(axis=1)
    # Translate both packets so one member of the first becomes zero.
    # Every distinct ordered pair has such a translated representative.
    minimum=len(ds)+1; hist=Counter(); pairs=0
    for i in np.flatnonzero(packets[:,0]==0):
        d=np.count_nonzero(signatures!=signatures[i],axis=1)
        assert np.count_nonzero(d==0)==1  # Fourier injectivity
        h=np.bincount(d,minlength=len(ds)+1)
        pairs+=len(d)-1
        for j,n in enumerate(h[1:],1):
            if n: hist[j]+=int(n)
        minimum=min(minimum,int(d[d>0].min()))
    assert minimum==bound_count(p,r,k),(p,r,k,minimum,bound_count(p,r,k))
    print(f'exhaustive p={p} r={r} k={k}: {pairs:,} translated ordered pairs; min {minimum}/{len(ds)} projective directions; vector disagreement {(p-1)*minimum}/{p**r}; spectrum {sorted(hist)}')


def signed_diff(p,r,A,C):
    ds=directions(p,r)
    def signature(packet,v):
        return Counter(sum(a*x for a,x in zip(u,v))%p for u in packet)
    return sum(signature(A,v)!=signature(C,v) for v in ds)


def split(p,b):
    roots=[i for i in range(1,p) if pow(i,b,p)==1]
    assert len(roots)==b
    a=next(i for i in range(1,p) if i not in roots)
    def pair(t): return (t,pow(t,-1,p))
    return [pair(t) for t in roots],[pair(a*t%p) for t in roots]


def nonsplit(p,b):
    d=next(i for i in range(2,p) if pow(i,(p-1)//2,p)==p-1)
    def mul(u,v): return ((u[0]*v[0]+d*u[1]*v[1])%p,(u[0]*v[1]+u[1]*v[0])%p)
    def pw(u,n):
        a=(1,0)
        for _ in range(n): a=mul(a,u)
        return a
    unit=[(x,y) for x,y in vectors(p,2) if (x*x-d*y*y)%p==1]
    roots=[u for u in unit if pw(u,b)==(1,0)]
    assert len(roots)==b
    a=next(u for u in unit if u not in roots)
    return roots,[mul(a,u) for u in roots]


def construction(p,b):
    if b==1: return [(0,0)],[(1,0)]
    if b==p-1: return [(x,0) for x in range(1,p)],[(0,x) for x in range(1,p)]
    if (p-1)%b==0: return split(p,b)
    if (p+1)%b==0: return nonsplit(p,b)
    return None


def check_constructions():
    n=0
    for p in [3,5,7,11,13,17,19,23,29,31]:
        for b in range(1,p):
            pair=construction(p,b)
            if pair is None: continue
            A,C=pair
            assert len(A)==len(C)==b and len(set(A+C))==2*b
            d=signed_diff(p,2,A,C)
            assert d==bound_count(p,2,b),(p,b,d)
            n+=1
            if p<=7:
                for s in [1,2]:
                    # tensor with a common uniform subspace of dimension s
                    r=s+2
                    AA=[u+v for u in vectors(p,s) for v in A]
                    CC=[u+v for u in vectors(p,s) for v in C]
                    dd=signed_diff(p,r,AA,CC)
                    assert dd==bound_count(p,r,b*p**s)
                    n+=1
    print(f'{n} sharp split/nonsplit, line, and lifted constructions verified exactly.')

if __name__=='__main__':
    for p,r,ks in [(3,1,range(1,4)),(3,2,range(1,5)),(3,3,range(1,4)),(5,2,range(1,4)),(7,2,range(1,3))]:
        for k in ks: exhaustive(p,r,k)
    check_constructions()
    print('All tests passed.')
