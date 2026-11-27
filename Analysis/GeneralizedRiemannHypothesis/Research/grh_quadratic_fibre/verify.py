#!/usr/bin/env python3
"""Exact-integer sanity checks of the finite parity lemma and prime-count profiles.
No numerical result is used in the mathematical proof. Standard library only.
"""
from math import comb, exp, log, isqrt, gcd
from fractions import Fraction
from itertools import combinations
from csv import writer
from pathlib import Path
ROOT = Path(__file__).resolve().parent

def C(n,k):
    return comb(n,k) if 0 <= k <= n else 0

def bias(m,h,t):
    return Fraction(sum((-1)**j*C(t,j)*C(m-t,h-j) for j in range(min(h,t)+1)), C(m,h))

def check_parity():
    n=0; max_scaled=0.; max_refined=0.; max_decay=0.; arg=None
    for m in range(2,81):
        for h in range(1,m//2+1):
            for t in range(m//2+1):
                f=bias(m,h,t); b=Fraction(m-2*h,m)**t; lam=h*t/m
                assert f == bias(m,t,h)
                assert bias(m,m-h,t) == (-1)**t*f
                if t==0: assert f==1
                if t==1: assert f==b
                if t>=1:
                    assert abs(f)<1
                if t<m//2:
                    r=Fraction(1)-2*Fraction(h,m)
                    if t==0: correction=0
                    else: correction=-2*Fraction(t*h,m*(m-t))*(bias(m-1,h-1,t-1)+f)
                    assert bias(m,h,t+1)==r*f+correction
                e=abs(float(f-b)); scaled=h*e
                if scaled>max_scaled: max_scaled=scaled; arg=(m,h,t)
                if lam>0:
                    max_refined=max(max_refined,scaled*exp(lam/16)/lam**2)
                    max_decay=max(max_decay,abs(float(f))*exp(lam/4))
                n+=1
    print(f'Exact parity identity checks: {n} triples (m<=80)')
    print(f'Max h*|F-b^t| = {max_scaled:.8f} at {arg}')
    print(f'Max h*|F-b^t|*exp(lambda/16)/lambda^2 = {max_refined:.8f}')
    print(f'Max |F|*exp(lambda/4) = {max_decay:.8f}')

def check_limit():
    with (ROOT/'critical_window.csv').open('w', newline='') as fp:
        w=writer(fp); w.writerow(['m','h','t','lambda','exact_bias','binomial_bias','h_times_difference','predicted_limit'])
        for h in [20,40,80,160,320,640]:
            m=h*h
            for t in [h//2,h,2*h]:
                lam=h*t/m; f=bias(m,h,t); b=Fraction(m-2*h,m)**t
                scaled=float(h*(f-b)); predicted=-2*lam**2*exp(-2*lam)
                w.writerow([m,h,t,lam,float(f),float(b),scaled,predicted])
                if h>=640: assert abs(scaled-predicted)<0.002
    print('Critical-window correction: exact rational coefficients written to critical_window.csv')

def primes(n):
    return [p for p in range(2,n+1) if all(p%d for d in range(2,isqrt(p)+1))]

def legendre(p,q):
    v=pow(p,(q-1)//2,q)
    return 1 if v==1 else -1 if v==q-1 else 0

def counts(q,S,k):
    d=[[0]*q for _ in range(k+1)]; d[0][1]=1
    for i,p in enumerate(S):
        for j in range(min(i+1,k),0,-1):
            prev=d[j-1]; dest=d[j]
            for a,c in enumerate(prev):
                if c: dest[(a*p)%q]+=c
    return d[k]

def check_primes():
    q=101; pool=[p for p in primes(251) if p!=q]
    plus=[p for p in pool if legendre(p,q)==1]; minus=[p for p in pool if legendre(p,q)==-1]
    sigma=1 if len(plus)>=len(minus) else -1
    major,minor=(plus,minus) if sigma==1 else (minus,plus)
    print(f'Prime pool: q={q}, y=251, N={len(pool)}, majority sign={sigma}, majority size={len(major)}')
    with (ROOT/'prime_counts.csv').open('w',newline='') as fp:
        w=writer(fp); w.writerow(['q','m','k','minority_t','h','lambda','sign_class_relative_to_phase','class_total','min_count','max_count','exact_profile','binomial_profile','max_abs_exact_profile_residual'])
        for t in [0,1,2,4,8,12,len(minor)]:
            S=major+minor[:t]; m=len(S)
            for k in [8,m//2,m-8]:
                h=min(k,m-k); phase=sigma**k*((-1)**t if k>m/2 else 1)
                f=bias(m,h,t); b=Fraction(m-2*h,m)**t; den=C(m,k); d=counts(q,S,k)
                assert sum(d)==den and d[0]==0
                for sign in [1,-1]:
                    vals=[d[g] for g in range(1,q) if phase*legendre(g,q)==sign]
                    assert 2*Fraction(sum(vals),den)==1+sign*f
                    exact=1+sign*f; approx=1+sign*b
                    residual=max(abs(Fraction((q-1)*v,den)-exact) for v in vals)
                    w.writerow([q,m,k,t,h,h*t/m,sign,sum(vals),min(vals),max(vals),float(exact),float(approx),float(residual)])
                    if t==0 and sign==-1: assert max(vals)==0
    print('Exact dynamic programming and sign-class aggregate checks: prime_counts.csv')

if __name__=='__main__':
    check_parity(); check_limit(); check_primes()
