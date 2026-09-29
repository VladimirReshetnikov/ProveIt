#!/usr/bin/env python3
"""Exact arithmetic checks for finite-core exponential feedback.

This checks finite coefficient identities, not the asymptotic proofs.
Only Python's standard library is required. Coefficients are stored in EGF
normalization: b[n] = n! * [q**n] U(q), even though U is an ordinary series.
"""
from __future__ import annotations
import argparse, csv, json, math, time
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def feedback_egf(nmax: int, p: int, a: int = 1, cutoff: int | None = None):
    if nmax < 1 or p < 1 or a < 1:
        raise ValueError('Require nmax,p,a >= 1.')
    fact = [math.factorial(n) for n in range(nmax + 1)]
    e = [[0] * (nmax + 1) for _ in range(nmax + 1)]
    for j in range(1, nmax + 1): e[j][0] = 1
    b = [0] * (nmax + 1)
    slopes = [a * j**p for j in range(nmax + 1)]
    for n in range(1, nmax + 1):
        b[n] = sum(fact[n] // fact[n-j] * e[j][n-j]
                   for j in range(1, min(n, cutoff or nmax) + 1))
        factors = [math.comb(n-1, k-1) * b[k] for k in range(1,n+1)]
        for j in range(1, nmax-n+1):
            e[j][n] = slopes[j] * sum(factors[k-1] * e[j][n-k]
                                      for k in range(1,n+1))
    return b, e

def inverse_egf(b: list[int]) -> list[int]:
    nmax = len(b)-1
    if b[0] != 0 or b[1] != 1: raise ValueError('Series must be tangent to identity.')
    c = [0]*(nmax+1); c[1] = 1
    bell = [[0]*(nmax+1) for _ in range(nmax+1)]
    bell[0][0] = 1; bell[1][1] = 1
    for n in range(2,nmax+1):
        for k in range(2,n+1):
            bell[n][k] = sum(math.comb(n-1,j-1)*c[j]*bell[n-j][k-1]
                             for j in range(1,n-k+2))
        c[n] = -sum(b[k]*bell[n][k] for k in range(2,n+1))
        bell[n][1] = c[n]
        assert sum(b[k]*bell[n][k] for k in range(1,n+1)) == 0
    return c

def partitions(n: int, largest: int | None = None):
    if n == 0:
        yield []
        return
    for j in range(min(n, largest or n),1-1,-1):
        for rest in partitions(n-j,j): yield [j]+rest

def partition_coefficient(n: int, p: int, a: int = 1, cutoff: int | None = None):
    ans = Fraction(0)
    for parts in partitions(n):
        if cutoff is not None and sum(j > cutoff for j in parts) != 1: continue
        counts: dict[int,int] = {}
        for j in parts: counts[j] = counts.get(j,0)+1
        denom = math.prod(math.factorial(m) for m in counts.values())
        ans += Fraction((a*sum(j**p for j in parts))**(len(parts)-1),denom)
    return ans

def one_tail_egf(nmax: int,p: int,a: int,cutoff: int):
    _, e = feedback_egf(nmax,p,a,cutoff)
    fact = [math.factorial(n) for n in range(nmax+1)]
    P=[0]*(nmax+1); T=[0]*(nmax+1); A=[0]*(nmax+1); A[0]=1
    for n in range(1,nmax+1):
        P[n]=sum(a*j**p*(fact[n]//fact[n-j])*e[j][n-j]
                 for j in range(1,min(cutoff,n)+1))
        T[n]=sum((fact[n]//fact[n-j])*e[j][n-j]
                 for j in range(cutoff+1,n+1))
        A[n]=sum(math.comb(n,k)*P[k]*A[n-k] for k in range(1,n+1))
    return [sum(math.comb(n,k)*T[k]*A[n-k] for k in range(n+1))
            for n in range(nmax+1)]

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--order',type=int,default=300)
    args=ap.parse_args(); start=time.perf_counter()
    data=ROOT/'data'; data.mkdir(exist_ok=True)
    checks=[]
    for p in (2,3):
        b,_=feedback_egf(args.order,p)
        c=inverse_egf(b)
        for n in range(1,min(18,args.order)+1):
            assert Fraction(b[n],math.factorial(n)) == partition_coefficient(n,p)
            checks.append({'p':p,'n':n,'identity':'positive Lagrange formula','passed':True})
        with (data/f'exact_p{p}.csv').open('w',newline='') as f:
            w=csv.writer(f);w.writerow(['n','n_factorial_times_u_n','n_factorial_times_v_n'])
            for n in range(1,args.order+1): w.writerow([n,b[n],c[n]])
        for M in (1,2,3):
            N=min(16,args.order); one=one_tail_egf(N,p,1,M)
            for n in range(1,N+1):
                assert Fraction(one[n],math.factorial(n))==partition_coefficient(n,p,cutoff=M)
                checks.append({'p':p,'M':M,'n':n,'identity':'one-tail marking identity','passed':True})
        print(f'p={p}: exact coefficients and inverse through n={args.order}; checks passed',flush=True)
    report={'order':args.order,'exact_partition_and_marking_checks':len(checks),
            'inverse_composition_checks':2*(args.order-1),'all_passed':True,
            'runtime_seconds':round(time.perf_counter()-start,3),'checks':checks,
            'scope':'Finite exact algebra only. No numerical experiment certifies an asymptotic theorem.'}
    (data/'exact_verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='checks'},indent=2))

if __name__=='__main__': main()
