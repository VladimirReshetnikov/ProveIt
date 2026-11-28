#!/usr/bin/env python3
"""Independent verifier: standard-library rational DVR elimination, no HNF.

Proves the finite inequalities used in N_2^o(8)=9 by exact arithmetic.
The analytic transport theorem is proved in the accompanying paper.
"""
from fractions import Fraction as F
from math import comb
from collections import Counter
import json

def val(x,p):
    x=F(x)
    if not x:return 10**9
    n,d=abs(x.numerator),x.denominator
    v=0
    while n%p==0:n//=p;v+=1
    while d%p==0:d//=p;v-=1
    return v

def mod(x,p):
    x=F(x)
    assert x.denominator%p
    return x.numerator*pow(x.denominator,-1,p)%p

def dvr_coordinates(B,p):
    """Return residues in L/pL for L=column-span_Zp(B).

    Each row/column operation is invertible over Z_(p). Selecting a
    globally least-valuation pivot ensures every elimination ratio is
    integral. We track row operations and verify all transformed columns.
    """
    t=len(B);n=len(B[0]);M=[[F(x) for x in row] for row in B]
    U=[[F(i==j) for j in range(t)] for i in range(t)]
    piv=[]
    for h in range(t):
        v,i,j=min((val(M[i][j],p),i,j) for i in range(h,t) for j in range(h,n))
        assert v<10**9
        M[h],M[i]=M[i],M[h];U[h],U[i]=U[i],U[h]
        for row in M:row[h],row[j]=row[j],row[h]
        pivot=M[h][h];piv.append(pivot)
        for i in range(h+1,t):
            f=M[i][h]/pivot
            assert val(f,p)>=0
            M[i]=[x-f*y for x,y in zip(M[i],M[h])]
            U[i]=[x-f*y for x,y in zip(U[i],U[h])]
        for j in range(h+1,n):
            f=M[h][j]/pivot
            assert val(f,p)>=0
            for i in range(t):M[i][j]-=f*M[i][h]
    assert all(M[i][j]==(piv[i] if i==j else 0) for i in range(t) for j in range(n))
    C=[[sum(U[i][h]*B[h][j] for h in range(t))/piv[i] for j in range(n)] for i in range(t)]
    assert all(val(x,p)>=0 for row in C for x in row)
    return [[mod(C[i][j],p) for i in range(t)] for j in range(n)], [val(x,p) for x in piv]

def rank_increases(columns,p):
    basis={};indices=[]
    for k,c in enumerate(columns):
        c=list(c)
        for j,b in sorted(basis.items()):
            a=c[j]
            c=[(x-a*y)%p for x,y in zip(c,b)]
        if any(c):
            j=next(j for j,x in enumerate(c) if x)
            a=pow(c[j],-1,p);basis[j]=[(a*x)%p for x in c]
            indices.append(k)
    return indices

def profiles(total,parts):
    if parts==1:
        yield (total,)
    else:
        for j in range(total+1):
            for tail in profiles(total-j,parts-1):yield (j,)+tail

def exact_open_binary(E):
    degree=max(E)
    B=[[comb(n,k)*2**k if k<=n else 0 for k in range(degree+1)] for n in E]
    columns,piv=dvr_coordinates(B,2)
    indices=rank_increases(columns,2)
    assert len(indices)==len(E)
    return indices[-1],indices,piv

def main():
    entries=[];distribution=Counter()
    for nu in profiles(8,4):
        E=sorted(a+4*j for a,m in enumerate(nu) for j in range(m))
        maximum,indices,piv=exact_open_binary(E)
        assert maximum<=9
        evens=nu[0]+nu[2]
        predicted=9 if evens%4==2 else (7 if evens%4==0 and len({x%2 for x in nu})==1 else 8)
        assert maximum==predicted
        distribution[maximum]+=1
        entries.append({'residue_multiplicities':nu,'support':E,'maximum':maximum,
                        'pivot_indices':indices,'smith_valuations':piv})
    assert len(entries)==165 and distribution=={7:23,8:100,9:42}
    result={'algorithm':'exact rational DVR elimination; Python standard library only',
            'profiles':165,'distribution':dict(sorted(distribution.items())),
            'global_maximum':9,'certificates':entries}
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
