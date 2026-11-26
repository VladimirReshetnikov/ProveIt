#!/usr/bin/env python3
"""Exact finite checks for the moment-extremum theorem. Python standard library.

The proof for all parameters is in moment_extremum.tex. This verifier:
* exhaustively checks all spanning step multisets at (m,p)=(2,5),(3,7);
* checks deterministic random examples for 2<=m<=12;
* checks extremizers at several even m and primes p == 1 mod 2m;
* independently takes cyclotomic norms of all conductor-one eigenvalues;
* checks an actual Laplacian cofactor at (m,p)=(6,13), without moment formulas.
"""
from collections import Counter
from itertools import combinations_with_replacement
from math import comb
from pathlib import Path
import json
import random


def prime(p):
    return p>=2 and all(p%d for d in range(2,int(p**0.5)+1))


def vp(n,p):
    n=abs(n)
    assert n
    v=0
    while n%p==0:
        n//=p; v+=1
    return v


def bareiss(a):
    a=[row[:] for row in a]
    n=len(a)
    if not n:return 1
    old=1; sign=1
    for k in range(n-1):
        if not a[k][k]:
            r=next((r for r in range(k+1,n) if a[r][k]),None)
            if r is None:return 0
            a[k],a[r]=a[r],a[k];sign=-sign
        pivot=a[k][k]
        pivotrow=a[k]
        for i in range(k+1,n):
            row=a[i]; aik=row[k]
            for j in range(k+1,n):
                numer=row[j]*pivot-aik*pivotrow[j]
                assert numer%old==0
                row[j]=numer//old
            row[k]=0
        old=pivot
    return sign*a[-1][-1]


def spanning(steps,p):
    x,y=steps[0]
    return any((x*b-y*a)%p for a,b in steps[1:])


def moment_form(steps,p,j):
    n=2*j
    return [sum(comb(n,t)*pow(a,n-t,p)*pow(b,t,p)
                for a,b in steps)%p for t in range(n+1)]


def data(steps,p):
    m=len(steps)
    assert p>2*m and spanning(steps,p)
    assert all(a%p or b%p for a,b in steps)
    first=next(j for j in range(1,m+1) if any(moment_form(steps,p,j)))
    counts=Counter()
    for a,b in [(1,t) for t in range(p)]+[(0,1)]:
        j=next(j for j in range(1,m+1)
               if sum(pow((a*x+b*y)%p,2*j,p) for x,y in steps)%p)
        counts[j]+=1
    A=2*sum(j*n for j,n in counts.items())
    k=m//2
    assert first<=k,(steps,p,first)
    assert A<=2*k*(p+1+2*m-2*k),(steps,p,A)
    return {'m':m,'p':p,'first_form':first,'moment_counts':dict(counts),'A':A}


def generator(p,order):
    return next(g for g in range(1,p)
                if pow(g,order,p)==1 and all(pow(g,d,p)!=1 for d in range(1,order)))


def extremizer(m,p):
    assert m%2==0 and (p-1)%(2*m)==0
    k=m//2;g=generator(p,m)
    return [(pow(g,i,p),0) for i in range(k)]+[(0,pow(g,i,p)) for i in range(k)]


def norm_eigenvalue(p,steps,a,b):
    # Work in Z[z]/(1+z+...+z^(p-1)). Multiplication-by-F matrix.
    # F=2m-sum(z^(a*x+b*y)+z^(-a*x-b*y)); exponents reduced mod p.
    coeff=[0]*p;coeff[0]=2*len(steps)
    for x,y in steps:
        e=(a*x+b*y)%p
        coeff[e]-=1;coeff[-e%p]-=1
    mat=[[0]*(p-1) for _ in range(p-1)]
    for j in range(p-1):
        col=[0]*p
        for e,c in enumerate(coeff):
            col[(e+j)%p]+=c
        last=col[-1]
        for i in range(p-1):mat[i][j]=col[i]-last
    return bareiss(mat)


def direct_tree_number(p,steps):
    # Exactly one undirected edge for every vertex and supplied step;
    # multiplicities are retained. Cofactor removes final vertex.
    n=p*p
    a=[[0]*n for _ in range(n)]
    for x in range(p):
        for y in range(p):
            u=x*p+y
            for dx,dy in steps:
                v=((x+dx)%p)*p+(y+dy)%p
                a[u][u]+=1;a[v][v]+=1
                a[u][v]-=1;a[v][u]-=1
    return bareiss([row[:-1] for row in a[:-1]])


def main():
    result={'exhaustive':[],'random':[],'extremizers':[],'cyclotomic_norms':[],'cofactor':[]}
    for m,p in [(2,5),(3,7)]:
        vectors=[(a,b) for a in range(p) for b in range(p) if a or b]
        count=0;maxA=0
        for steps in combinations_with_replacement(vectors,m):
            if not spanning(steps,p):continue
            d=data(steps,p);count+=1;maxA=max(maxA,d['A'])
        result['exhaustive'].append({'m':m,'p':p,'spanning_multisets':count,'maximum_A':maxA})
        print('exhaustive',result['exhaustive'][-1],flush=True)
    rng=random.Random(20261126)
    for m in range(2,13):
        p=next(p for p in range(2*m+1,4*m+20) if prime(p))
        count=0
        while count<200:
            steps=[(rng.randrange(p),rng.randrange(p)) for _ in range(m)]
            if not all(x or y for x,y in steps) or not spanning(steps,p):continue
            data(steps,p);count+=1
        result['random'].append({'m':m,'p':p,'samples':count})
    for m,p in [(2,5),(4,17),(4,41),(6,13),(6,37),(8,17),(8,97),(10,41),(12,73),(14,29)]:
        steps=extremizer(m,p);d=data(steps,p)
        assert d['A']==m*(p+1+m)
        assert d['first_form']==m//2
        if m>=4:assert not any(moment_form(steps,p,1))
        d['steps']=steps;result['extremizers'].append(d)
    print('extremizers',result['extremizers'],flush=True)
    for m,p in [(2,5),(4,17),(6,13),(8,17)]:
        steps=extremizer(m,p)
        vals=[vp(norm_eigenvalue(p,steps,a,b),p) for a,b in [(1,t) for t in range(p)]+[(0,1)]]
        expected=m*(p+1+m)
        assert sum(vals)==expected
        result['cyclotomic_norms'].append({'m':m,'p':p,'norm_valuations':vals,'sum':sum(vals),'tree_valuation':sum(vals)-2})
        print('norm',result['cyclotomic_norms'][-1],flush=True)
    for m,p in [(2,5),(6,13)]:
        steps=extremizer(m,p);number=direct_tree_number(p,steps)
        val=vp(number,p);assert val==m*(p+1+m)-2
        result['cofactor'].append({'m':m,'p':p,'vertices':p*p,'tree_number':str(number),'valuation':val})
        print('cofactor',{'m':m,'p':p,'valuation':val,'decimal_digits':len(str(number))},flush=True)
    out=Path(__file__).resolve().parents[1] / 'data' / 'moment_verification_results.json'
    out.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS',out,flush=True)

if __name__=='__main__':main()
