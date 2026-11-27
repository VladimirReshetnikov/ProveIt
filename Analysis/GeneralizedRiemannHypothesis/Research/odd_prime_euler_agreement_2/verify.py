#!/usr/bin/env python3
"""Exact finite checks. No dependencies; not a substitute for the proof."""
from collections import Counter
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, product
from math import comb
from random import Random

def pts(p,r): return list(product(range(p),repeat=r))
def dirs(p,r): return [v for v in pts(p,r) if next((x for x in v if x),0)==1]
def dot(v,a,p): return sum(x*y for x,y in zip(v,a))%p

def projection(A,v,p):
    R=[0]*p
    for a in A: R[dot(v,a,p)]+=1
    return tuple(R)

def leading(p,k):
    d,z=0,1
    while z*p<=k: d,z=d+1,z*p
    return d,k//z

def bound(p,r,k):
    d,s=leading(p,k)
    return Fraction(p-1,p**r) if d>=r-1 else Fraction((p-1)*(p+1-s),p**(d+2))

def mul(x,y,p,n): return ((x[0]*y[0]+n*x[1]*y[1])%p,(x[0]*y[1]+x[1]*y[0])%p)
def power(x,k,p,n):
    y=(1,0)
    while k:
        if k&1: y=mul(y,x,p,n)
        x=mul(x,x,p,n); k//=2
    return y

def planar(p,s):
    if s==1: return [(0,0)],[(1,0)]
    if s==p-1: return [(a,0) for a in range(1,p)],[(0,a) for a in range(1,p)]
    if (p-1)%s==0 and s<p-1:
        B=[z for z in range(1,p) if pow(z,s,p)==1]
        b=next(z for z in range(1,p) if z not in B)
        C=[b*z%p for z in B]
        return [(z,pow(z,-1,p)) for z in B],[(z,pow(z,-1,p)) for z in C]
    if (p+1)%s==0 and s<p+1:
        n=next(z for z in range(1,p) if pow(z,(p-1)//2,p)==p-1)
        G=[(a,b) for a,b in pts(p,2) if (a*a-n*b*b)%p==1]
        B=[z for z in G if power(z,s,p,n)==(1,0)]
        b=next(z for z in G if z not in B)
        return B,[mul(b,z,p,n) for z in B]
    raise ValueError('uncovered leading digit')

def eligible(p,s): return s in (1,p-1) or ((p-1)%s==0 and s<p-1) or ((p+1)%s==0 and s<p+1)

def lift(p,r,d,s):
    A,C=planar(p,s)
    return ([a+w+(0,)*(r-d-2) for a in A for w in pts(p,d)],
            [a+w+(0,)*(r-d-2) for a in C for w in pts(p,d)])

def pi_valuation(R,p):
    # h is the coefficient vector in basis 1,zeta,...,zeta^(p-2).
    # For h=(zeta-1)q, q_last=-sum(h)/p and
    # q_i=-sum(h[:i+1])-(i+1)*q_last. Thus exact division is integral
    # iff sum(h) is divisible by p.
    h=[R[i]-R[-1] for i in range(p-1)]
    if not any(h): return None
    t=0
    while sum(h)%p==0:
        last=-sum(h)//p; running=0; q=[]
        for i,z in enumerate(h):
            running+=z; q.append(-running-(i+1)*last)
        assert q[-1]==last and any(q)
        h=q; t+=1
    return t

def test_pair(A,C,p,r):
    assert len(A)==len(C) and Counter(A)!=Counter(C)
    m=sum((Counter(A)-Counter(C)).values()); d,s=leading(p,m)
    n=0
    for v in dirs(p,r):
        R=tuple(a-c for a,c in zip(projection(A,v,p),projection(C,v,p)))
        t=pi_valuation(R,p)
        assert (t is None)==(not any(R))
        if t is not None:
            n+=1; assert 1<=t<=(p-1)*d+s,(p,r,m,R,t)
    delta=Fraction((p-1)*n,p**r)
    assert delta>=bound(p,r,m) and delta>=Fraction(p-1,p*m)
    return delta

def exhaustive_planar(p,k):
    # Every k-multiset represented once. If for any k+1 projective
    # directions two signatures coincide, the claimed lower bound fails.
    U=pts(p,2); V=dirs(p,2); n=len(U); sigs=[]
    weights=[(k+1)**i for i in range(p)]
    enc=[[weights[dot(v,a,p)] for a in U] for v in V]
    for packet in combinations_with_replacement(range(n),k):
        sigs.append(tuple(sum(row[i] for i in packet) for row in enc))
    assert len(sigs)==comb(n+k-1,k)
    checks=0
    for I in combinations(range(len(V)),k+1):
        seen=set()
        for sig in sigs:
            key=tuple(sig[i] for i in I)
            assert key not in seen,(p,k,I)
            seen.add(key)
        checks+=len(sigs)
    A,C=planar(p,k)
    assert test_pair(A,C,p,2)==bound(p,2,k)
    return len(sigs),checks

def main():
    print('Exact finite checks (not a formal proof)')
    total=0
    for p in (2,3,5):
        for k in range(1,p):
            n,t=exhaustive_planar(p,k); total+=t
            print(f'exhaustive rank=2, exponent={p}, k={k}: {n} packets; {t} signature tests; min={bound(p,2,k)}')
    print(f'Total exhaustive signature tests: {total}')
    n=0
    for p in (2,3,5,7,11,13,17,19):
        for s in range(1,p):
            if eligible(p,s):
                A,C=planar(p,s)
                assert len(set(A))==len(set(C))==s and not set(A)&set(C)
                assert test_pair(A,C,p,2)==bound(p,2,s); n+=1
    print(f'Planar sharp constructions verified: {n}')
    n=0
    for p in (2,3,5,7):
        for d in (0,1,2):
            for s in range(1,p):
                if eligible(p,s):
                    r=d+2; A,C=lift(p,r,d,s)
                    assert test_pair(A,C,p,r)==bound(p,r,len(A)); n+=1
    print(f'Sharp lifted examples verified: {n}')
    rng=Random(20261127); n=0
    for p,r in ((2,4),(3,3),(5,2),(5,3),(7,2)):
        U=pts(p,r)
        for j in range(120):
            k=rng.randint(1,min(24,len(U))); A=rng.choices(U,k=k); C=rng.choices(U,k=k)
            if Counter(A)!=Counter(C): test_pair(A,C,p,r); n+=1
    print(f'Reproducible random pairs checked: {n}')
    print('PASS: all assertions satisfied.')

if __name__=='__main__': main()
