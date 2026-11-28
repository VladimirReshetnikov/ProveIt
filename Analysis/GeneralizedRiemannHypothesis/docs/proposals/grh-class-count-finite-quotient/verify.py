#!/usr/bin/env python3
"""Exact real-integer analogue. Run: python3 verify.py."""
from fractions import Fraction as F
from itertools import product, combinations_with_replacement
from collections import defaultdict

def transpose(A):
    return tuple(zip(*A))
def mul(A, B):
    return tuple(tuple(sum(x*y for x,y in zip(a,b)) for b in zip(*B)) for a in A)
def sub(A, B):
    return tuple(tuple(x-y for x,y in zip(a,b)) for a,b in zip(A,B))
def add(A, B):
    return tuple(tuple(x+y for x,y in zip(a,b)) for a,b in zip(A,B))
def det(A):
    (a,b),(c,d)=A
    return a*d-b*c
def inverse(A):
    (a,b),(c,d)=A
    n=det(A)
    return ((F(d,n),F(-b,n)),(F(-c,n),F(a,n)))
def integral(A):
    return all(F(x).denominator == 1 for a in A for x in a)

I=((1,0),(0,1))
buckets=defaultdict(list)
for a,b,c,d in product(range(-3,4),repeat=4):
    A=((a,b),(c,d))
    if det(A):
        G=mul(transpose(A),A)
        buckets[G].append(A)
pairs=failures=indices=0
for G, As in buckets.items():
    Gi=inverse(G)
    for A,B in combinations_with_replacement(As,2):
        Ai,Bi=inverse(A),inverse(B)
        diff=sub(Ai,Bi)
        res=mul(Gi,sub(transpose(A),transpose(B)))
        assert diff==res and mul(G,Ai)==transpose(A)
        assert mul(B,Ai)==add(I,mul(B,diff))
        if integral(res):
            assert integral(mul(B,Ai))
        else:
            failures+=1
        pairs+=1
    # |Z^2/G Z^2| by flooding the generators of G^-1 Z^2/Z^2.
    def mod(v): return tuple(x%1 for x in v)
    generators=list(zip(*Gi))
    seen={(F(0),F(0))}
    todo=list(seen)
    while todo:
        v=todo.pop()
        for w in generators:
            z=mod(tuple(x+y for x,y in zip(v,w)))
            if z not in seen:
                seen.add(z)
                todo.append(z)
    assert len(seen)==abs(det(G))
    indices+=1

assert failures>0
print(f"{pairs} equal-Gram pairs ({failures} genuinely nonintegral inverse differences)")
print(f"{indices} independently enumerated scalar quotient cardinalities")
