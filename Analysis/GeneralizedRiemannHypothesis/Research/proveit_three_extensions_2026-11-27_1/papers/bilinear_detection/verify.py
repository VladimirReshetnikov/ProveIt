#!/usr/bin/env python3
"""Exact checks and limiting profiles for nonzero-vector bilinear observations."""
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import comb, prod, exp, log
import json
from pathlib import Path

def qbinom(n,k,q):
    if n < 0 or k < 0 or k > n: return 0
    k=min(k,n-k)
    return prod(q**(n-i)-1 for i in range(k)) // prod(q**(k-i)-1 for i in range(k))

def rank_mod(Y,a,m,q):
    M=[list(Y[i*m:(i+1)*m]) for i in range(a)]
    r=0
    for c in range(m):
        pivot=next((i for i in range(r,a) if M[i][c]%q),None)
        if pivot is None: continue
        M[r],M[pivot]=M[pivot],M[r]
        u=pow(M[r][c],-1,q);M[r]=[(x*u)%q for x in M[r]]
        for i in range(a):
            if i != r:
                u=M[i][c];M[i]=[(x-u*y)%q for x,y in zip(M[i],M[r])]
        r+=1
        if r==a:break
    return r

def stats(Y,a,m,q):
    return (rank_mod(Y,a,m,q),sum(all(Y[i*m+j]==0 for j in range(m)) for i in range(a)),
            sum(all(Y[i*m+j]==0 for i in range(a)) for j in range(m)),Y.count(0))

@lru_cache(None)
def factorization_count(q,d,a,m,r,h,k):
    N=q**d
    ans=0
    for s in range(r,min(a,d)+1):
        subspaces=sum((-1)**j*comb(h,j)*qbinom(a-r-j,s-r,q) for j in range(h+1))
        assert subspaces>=0
        surjections=prod(N-q**i for i in range(s))
        fiber=N//q**s
        ans+=subspaces*surjections*(fiber-1)**k*fiber**(m-k)
    return ans

def enumerate_case(q,d,a,m):
    assert q in (2,3,5,7), 'Enumeration uses prime fields.'
    V=[v for v in product(range(q),repeat=d) if any(v)]
    dot=[[sum(x*y for x,y in zip(u,v))%q for v in V] for u in V]
    counts=Counter()
    for xs in product(range(len(V)),repeat=a):
        for zs in product(range(len(V)),repeat=m):
            Y=tuple(dot[i][j] for i in xs for j in zs)
            counts[Y]+=1
    N=q**d;den=(N-1)**(a+m)
    p0=Fraction(N-q,q*(N-1));p1=Fraction(N,q*(N-1))
    tv=Fraction(0);predicted_mass=0;triples=set()
    for Y in product(range(q),repeat=a*m):
        r,h,k,w=stats(Y,a,m,q);triples.add((r,h,k))
        predicted=factorization_count(q,d,a,m,r,h,k)
        assert predicted==counts.get(Y,0),(q,d,a,m,Y,predicted,counts.get(Y,0))
        assert predicted==factorization_count(q,d,m,a,r,k,h)
        predicted_mass+=predicted
        Q=p0**w*p1**(a*m-w)
        tv+=abs(Fraction(predicted,den)-Q)/2
    assert predicted_mass==den
    return dict(q=q,d=d,a=a,m=m,assignments=den,matrices=q**(a*m),statistic_triples=len(triples),
                tv_exact=str(tv),tv_decimal=float(tv),passed=True)

def g(q,c):
    return prod(1-q**(-j) for j in range(1,c+1))

def alpha(q,c):
    return prod(1-q**(-j) for j in range(c+1,max(c+101,101)))

def poisson_cdf(mu,k):
    if k<0:return 0.0
    if mu==0:return 1.0
    # scipy handles very large means without underflow.
    from scipy.stats import poisson
    return float(poisson.cdf(k,mu))

def poisson_profile(q,c,lam):
    al=alpha(q,c)
    if c==0:return max(1-al,1-exp(-lam))
    if lam<=-log(al):return 1-al
    cutoff=int((lam+log(al))/(-log(1-q**(-c))))
    return 1-al+al*poisson_cdf(lam*(q**c-1),cutoff)-poisson_cdf(lam*q**c,cutoff)

def pi(q,b,j):
    if j<max(0,-b):return 0.0
    return g(q,100)*q**(-j*(j+b))/(g(q,j)*g(q,j+b))

def rank_profile(q,c,s,limit=40):
    Q=[pi(q,s,j) for j in range(limit)]
    P=[sum(pi(q,c,k)*pi(q,s+k,j-k) for k in range(j+1)) for j in range(limit)]
    return sum(abs(x-y) for x,y in zip(P,Q))/2

def exact_column_chi2(q,N,a):
    return Fraction((N-1)**(a-2),(N-q)**a)*(Fraction((N-q+1)**a,N**(a-2))+q**a-2*N)-1

def verify_column_chi2(q,d,a):
    N=q**d;p0=Fraction(N-q,q*(N-1));p1=Fraction(N,q*(N-1))
    v=Fraction(0)
    for y in product(range(q),repeat=a):
        w=y.count(0);Q=p0**w*p1**(a-w)
        rho=Fraction(N-q**a if not any(y) else N,q**a*(N-1))
        v+=(rho-Q)**2/Q
    assert v==exact_column_chi2(q,N,a)
    return dict(q=q,d=d,a=a,chi2_exact=str(v),passed=True)

if __name__=='__main__':
    cases=[(2,1,2,2),(2,2,2,2),(2,2,3,3),(2,2,4,4),
           (2,3,2,3),(2,3,3,3),(3,2,2,2),(3,2,2,3),(3,2,3,3)]
    exact=[]
    for case in cases:
        row=enumerate_case(*case);exact.append(row);print(row,flush=True)
    chi=[verify_column_chi2(q,d,a) for q in [2,3,5] for d in range(2,5) for a in range(2,d+1)]
    profiles=[dict(q=q,c=c,lam=lam,tv=poisson_profile(q,c,lam),alpha=alpha(q,c),onset=-log(alpha(q,c)))
              for q in [2,3,5] for c in range(4) for lam in [0,.25,.5,1,2,4]]
    ranks=[dict(q=q,c=c,s=s,tv=rank_profile(q,c,s)) for q in [2,3,5] for c in range(4) for s in range(-8,13)]
    out=dict(exact_enumeration=exact,chi2_checks=chi,poisson_profiles=profiles,rank_profiles=ranks)
    Path(__file__).with_name('verification.json').write_text(json.dumps(out,indent=2))
