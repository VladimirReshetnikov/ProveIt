#!/usr/bin/env python3
"""Exact full-law checks by independently enumerating prescribed-Gram frames.

No enumeration of Sp is used in the formula.  The independent check enumerates
all source frames directly and counts their cross pairings with fixed targets.
Prime q and GF(4)=GF(2)[x]/(x^2+x+1) are supported.  GF(4) arithmetic is
implemented explicitly rather than substituting q=4 into a prime-field test.
"""
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import prod
import json


def mul4(x,y):
    z=0
    while y:
        if y&1:
            z ^= x
        y >>= 1
        x <<= 1
        if x&4:
            x ^= 7
    return z


def rank(A, q):
    if not A:
        return 0
    A = [list(row) for row in A]
    h, w = len(A), len(A[0])
    r = 0
    for j in range(w):
        i = next((i for i in range(r, h) if A[i][j] % q), None)
        if i is None:
            continue
        A[r], A[i] = A[i], A[r]
        inv = (next(v for v in range(1,4) if mul4(A[r][j],v)==1)
               if q==4 else pow(A[r][j] % q, -1, q))
        A[r] = ([mul4(x,inv) for x in A[r]] if q==4
                else [(x * inv) % q for x in A[r]])
        for i in range(h):
            if i != r:
                v = A[i][j] % q
                A[i] = ([x^mul4(v,y) for x,y in zip(A[i],A[r])] if q==4
                        else [(x-v*y) % q for x,y in zip(A[i], A[r])])
        r += 1
        if r == h:
            break
    return r


def gram(d, s, q):
    H = [[0]*d for _ in range(d)]
    for i in range(s):
        H[2*i][2*i+1] = 1
        H[2*i+1][2*i] = 1 if q==4 else -1 % q
    return H


def pairing(x, y, n, q):
    if q==4:
        z=0
        for i in range(n):
            z ^= mul4(x[i],y[n+i]) ^ mul4(x[n+i],y[i])
        return z
    return sum(x[i]*y[n+i] - x[n+i]*y[i] for i in range(n)) % q


def standard_frame(n, d, s, q):
    ans = []
    for i in range(s):
        ans.append(tuple(int(j == i) for j in range(2*n)))
        ans.append(tuple(int(j == n+i) for j in range(2*n)))
    for i in range(s, d-s):
        ans.append(tuple(int(j == i) for j in range(2*n)))
    return ans


@lru_cache(None)
def gaussian(q, n, k):
    if not 0 <= k <= n:
        return 0
    ans = Fraction(1)
    for j in range(k):
        ans *= Fraction(q**n-q**j, q**k-q**j)
    assert ans.denominator == 1
    return ans.numerator


@lru_cache(None)
def gl(q, k):
    return prod(q**k-q**j for j in range(k))


@lru_cache(None)
def sp(q, n):
    return q**(n*n)*prod(q**(2*j)-1 for j in range(1,n+1))


@lru_cache(None)
def embeddings(q, n, d, s):
    if not (0 <= 2*s <= d and d-s <= n):
        return 0
    ans = sp(q,n)//sp(q,n-s)
    ans *= prod(q**(2*(n-s)-i)-q**i for i in range(d-2*s))
    return ans


@lru_cache(None)
def transverse(q, r, t0, t1, ell):
    c = r-t0-t1
    return sum(gaussian(q,t0,k)*gaussian(q,t1,k)*gl(q,k)
               *gaussian(q,c,ell-k)*q**((ell-k)*(t0+t1-k))
               for k in range(max(0,ell-c), min(ell,t0,t1)+1))


def invariants(H1, H0, M, q):
    a, b = len(H1), len(H0)
    G = [H1[i]+list(M[i]) for i in range(a)]
    G += [[(M[i][j] if q==4 else -M[i][j] % q) for i in range(a)]+H0[j] for j in range(b)]
    rk = rank(G,q)
    assert rk % 2 == 0
    s = rk//2
    t1 = a-rank(H1+[[M[i][j] for i in range(a)] for j in range(b)],q)
    t0 = b-rank(H0+[list(row) for row in M],q)
    return s, a+b-rk, t0, t1


def formula_count_for_fixed_target(q,n,H1,H0,M):
    a,b = len(H1),len(H0)
    s,r,t0,t1 = invariants(H1,H0,M,q)
    s1 = rank(H1,q)//2
    den = embeddings(q,n,a,s1)
    nums = [transverse(q,r,t0,t1,ell)*embeddings(q,n,a+b-ell,s)
            for ell in range(r+1)]
    value = Fraction(sum(nums),den)
    assert value.denominator == 1
    return value.numerator, (s,r,t0,t1), nums


@lru_cache(None)
def frames(q,n,d,s):
    H = gram(d,s,q)
    vectors = list(product(range(q),repeat=2*n))
    out = []
    def extend(cols):
        j = len(cols)
        if j == d:
            out.append(tuple(cols))
            return
        for v in vectors:
            if all(pairing(u,v,n,q)==H[i][j] for i,u in enumerate(cols)):
                if rank(list(cols)+[v],q)==j+1:
                    extend(cols+[v])
    extend([])
    assert len(out)==embeddings(q,n,d,s)
    return tuple(out)


def one_case(q,n,a,s1,b,s0):
    H1,H0=gram(a,s1,q),gram(b,s0,q)
    Y=standard_frame(n,a,s1,q)
    hist=Counter()
    joint=Counter()
    for X in frames(q,n,b,s0):
        M=tuple(tuple(pairing(y,x,n,q) for x in X) for y in Y)
        hist[M]+=1
        ell=a+b-rank(list(Y)+list(X),q)
        joint[(M,ell)]+=1
    total_formula=0
    matrices=0
    joint_entries=0
    distinct_likelihoods={}
    for entries in product(range(q),repeat=a*b):
        M=tuple(tuple(entries[i*b:(i+1)*b]) for i in range(a))
        count,inv,nums=formula_count_for_fixed_target(q,n,H1,H0,M)
        assert hist[M]==count, (q,n,a,s1,b,s0,M,hist[M],count,inv)
        s,r,t0,t1=inv
        assert (count>0)==(s+max(t0,t1)<=n)
        den=embeddings(q,n,a,s1)
        for ell, num in enumerate(nums):
            assert Fraction(num,den)==joint[(M,ell)]
            joint_entries+=1
        total_formula+=count
        matrices+=1
        distinct_likelihoods[(rank(M,q),count)]=M
    expected=embeddings(q,n,b,s0)
    assert total_formula==expected
    den=Fraction(expected,q**(a*b))
    tv=sum(abs(Fraction(v,expected)-Fraction(1,q**(a*b)))
           for v in hist.values())/2
    tv+=Fraction(q**(a*b)-len(hist),2*q**(a*b))
    return {"q":q,"n":n,"a":a,"s1":s1,"b":b,"s0":s0,
            "frames_enumerated":expected,"matrices_checked":matrices,
            "intersection_cells_checked":joint_entries,"supported_matrices":len(hist),
            "total_variation":str(tv),"distinct_rank_probability_pairs":len(distinct_likelihoods),
            "status":"all exact equalities passed"}


def main():
    cases=[]
    # Every admissible form type through dimension 3 in a 4-dimensional space.
    types=[(1,0),(2,0),(2,1),(3,1)]
    for a,s1 in types:
        for b,s0 in types:
            cases.append(one_case(2,2,a,s1,b,s0))
    # Odd characteristic, independent direct frame enumeration.
    for a,s1 in types[:3]:
        for b,s0 in types[:3]:
            cases.append(one_case(3,2,a,s1,b,s0))
    # Larger ambient dimension and a case with full-dimensional source/target.
    cases.append(one_case(2,3,2,1,2,1))
    cases.append(one_case(2,2,4,2,2,1))
    # Genuine nonprime field: 2 represents x, 3 represents x+1.
    assert mul4(2,2)==3 and mul4(2,3)==1
    for a,s1 in [(1,0),(2,1)]:
        for b,s0 in [(1,0),(2,1)]:
            cases.append(one_case(4,1,a,s1,b,s0))
    cases.append(one_case(4,2,2,0,2,0))
    cases.append(one_case(4,2,2,1,2,1))
    result={"status":"PASS","method":"exact rational formula versus direct frame enumeration",
            "cases":cases,"case_count":len(cases),
            "matrices_checked":sum(x["matrices_checked"] for x in cases),
            "intersection_cells_checked":sum(x["intersection_cells_checked"] for x in cases),
            "frame_instances_enumerated":sum(x["frames_enumerated"] for x in cases)}
    print(json.dumps(result,indent=2))


if __name__=="__main__":
    main()
