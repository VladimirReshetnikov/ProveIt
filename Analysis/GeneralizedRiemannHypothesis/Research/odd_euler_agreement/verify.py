#!/usr/bin/env python3
"""Exact finite sanity checks for paper.tex, using only Python's standard library.

Projection histograms avoid floating-point roots of unity. Enumeration proves the
finite small-rank claims tested, but does not replace the general proof.
"""
from itertools import product, combinations, combinations_with_replacement
from collections import Counter
from fractions import Fraction
from math import comb


def points(p, r):
    return list(product(range(p), repeat=r))


def directions(p, r):
    return [v for v in points(p, r) if next((x for x in v if x), 0) == 1]


def dot(a, v, p):
    return sum(x*y for x, y in zip(a, v)) % p


def tier(p, r, k):
    d, power = 0, 1
    while power*p <= k:
        d += 1
        power *= p
    s = k//power
    if d >= r-1:
        return Fraction(p-1, p**r)
    return Fraction((p-1)*(p+1-s), p**(d+2))


def proj_hist(A, v, p):
    c = Counter(dot(a, v, p) for a in A)
    return tuple(c[i] for i in range(p))


def density(A, C, p, r):
    ds = directions(p, r)
    n = sum(proj_hist(A, v, p) != proj_hist(C, v, p) for v in ds)
    return Fraction(n*(p-1), p**r)


def exhaustive(p, r, k):
    """Use collisions on prescribed direction sets to find maximum agreement.

    A pair agrees on at least j directions iff some subset of j direction
    histograms is identical for two different packets. Check existence at the
    predicted maximum, nonexistence one above it. This covers all multisets.
    """
    V, ds = points(p,r), directions(p,r)
    dot_table = [[dot(a,v,p) for a in V] for v in ds]
    packets = list(combinations_with_replacement(range(len(V)),k))
    # Base (k+1) encoding of histograms is injective; no numerical error.
    powers = [(k+1)**i for i in range(p)]
    signatures = [tuple(sum(powers[row[i]] for i in A) for row in dot_table)
                  for A in packets]
    expected = tier(p,r,k)
    ndis = expected*p**r/(p-1)
    assert ndis.denominator == 1
    n_agree = len(ds)-int(ndis)
    # Fast path for j=0; any two packets agree on the empty subset.
    def collision(j):
        if j==0:
            return len(signatures)>=2
        if j>len(ds):
            return False
        for I in combinations(range(len(ds)), j):
            seen = set()
            for sig in signatures:
                key = tuple(sig[i] for i in I)
                if key in seen:
                    return True
                seen.add(key)
        return False
    assert collision(n_agree)
    assert not collision(n_agree+1)
    print(f'exhaustive ell={p}, r={r}, k={k}, packets={len(packets)}: min={expected}; max agreeing directions={n_agree}/{len(ds)}')
    return len(packets)


def split(p,s):
    # Multiplicative subgroup of order s.
    S = [x for x in range(1,p) if pow(x,s,p)==1]
    assert len(S)==s
    return [(x,0) for x in S], [(0,x) for x in S]


def nonsplit(p,s):
    # F_{p^2}=F_p[sqrt(D)] with D a nonsquare.
    D = next(i for i in range(1,p) if pow(i,(p-1)//2,p)==p-1)
    def mul(z,w):
        a,b=z; c,d=w
        return ((a*c+D*b*d)%p,(a*d+b*c)%p)
    def power(z,n):
        a=(1,0)
        while n:
            if n&1: a=mul(a,z)
            z=mul(z,z); n//=2
        return a
    U=[z for z in points(p,2) if (z[0]**2-D*z[1]**2)%p==1]
    S=[z for z in U if power(z,s)==(1,0)]
    assert len(U)==p+1 and len(S)==s
    c=next(z for z in U if z not in S)
    return S,[mul(c,z) for z in S]


def lift(A,C,p,d,r):
    W=points(p,d)
    return tuple(w+a+(0,)*(r-d-2) for w in W for a in A), tuple(w+c+(0,)*(r-d-2) for w in W for c in C)


def construction_checks():
    n=0
    for p in (3,5,7,11,13,17,19):
        for s in range(1,p):
            for name, fun, div in [('split',split,p-1),('nonsplit',nonsplit,p+1)]:
                if div%s: continue
                A,C=fun(p,s)
                assert len(set(A))==len(set(C))==s and not set(A)&set(C)
                assert density(A,C,p,2)==tier(p,2,s)
                n+=1
                # Lift in small rank, test padding by common factors.
                if p<=7:
                    for d,r in ((0,3),(1,3),(1,4)):
                        a,c=lift(A,C,p,d,r)
                        k=s*p**d
                        assert density(a,c,p,r)==tier(p,r,k)
                        pad=[(0,)*r]*(p**d-1)
                        assert density(list(a)+pad,list(c)+pad,p,r)==tier(p,r,k+len(pad))
                        n+=1
    for p in (3,5,7):
        for r in (1,2,3):
            A=[w+(0,) for w in points(p,r-1)]
            C=[w+(1,) for w in points(p,r-1)]
            assert density(A,C,p,r)==Fraction(p-1,p**r)
            n+=1
    print(f'constructions: {n} exact base/lift/saturated configurations verified')


def valuation_by_differences(b,p):
    """Compute pi=ζ-1 valuation exactly in Z[ζ], power basis 1,...,ζ^{p-2}.

    For a = (a_0,...,a_{p-2}), multiplication by pi sends c to
    a_0=-c_{p-2}-c_0, a_i=c_{i-1}-c_{p-2}-c_i (i>=1).
    Thus c_{p-2}=-(sum_i a_i)/p and backward division can be performed
    by integers exactly iff sum_i a_i is divisible by p.
    """
    a=[x-b[-1] for x in b[:-1]]
    assert any(a)
    t=0
    while sum(a)%p==0:
        last=-sum(a)//p
        # Check sign: sum a = -p*c_last.
        c=[-last-a[0]]
        for i in range(1,p-1):
            c.append(c[-1]-last-a[i])
        assert c[-1]==last
        assert any(c)
        a=c;t+=1
    return t


def valuation_checks():
    n=0
    for p,B in ((3,18),(5,5),(7,3)):
        for first in product(range(-B,B+1),repeat=p-1):
            b=first+(-sum(first),)
            if not any(b) or abs(b[-1])>B: continue
            m=sum(max(x,0) for x in b)
            t=valuation_by_differences(b,p)
            power=1;d=0
            while power*p<=m: power*=p;d+=1
            s=m//power
            assert 1<=t<=(p-1)*d+s, (p,b,t,d,s)
            n+=1
    print(f'valuation: {n} nonzero integer count vectors checked')


if __name__=='__main__':
    total=0
    for p,r,ks in ((3,2,range(1,6)),(5,2,range(1,6)),(3,3,range(1,4))):
        for k in ks:
            total+=exhaustive(p,r,k)
    print(f'enumeration: {total} packets across all cases')
    construction_checks()
    valuation_checks()
    print('ALL EXACT CHECKS PASSED')
