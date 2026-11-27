#!/usr/bin/env python3
"""Direct finite prime-power tests of the constant-free binomial filter.

Requires Python 3 and numpy. The computed values are numerical illustrations,
not certificates of GRH or central nonvanishing. All prime powers are included.
"""
import argparse
import csv
import math
from pathlib import Path
import numpy as np


def prime_powers(nmax):
    isprime = np.ones(nmax + 1, dtype=bool)
    isprime[:2] = False
    for p in range(2, math.isqrt(nmax) + 1):
        if isprime[p]:
            isprime[p*p::p] = False
    p = np.flatnonzero(isprime)
    parts = [p]
    logs = [np.log(p.astype(np.longdouble))]
    for k in range(2, nmax.bit_length()):
        # Integer multiplication is safe because the base is <= sqrt(nmax)
        # and the last intermediate power is bounded by nmax*sqrt(nmax).
        bases = p[p <= math.isqrt(nmax)]
        powers = bases.copy()
        for _ in range(1,k):
            valid = powers <= nmax // bases
            powers = powers[valid] * bases[valid]
            bases = bases[valid]
            if not len(bases):
                break
        if not len(bases):
            break
        parts.append(powers)
        logs.append(np.log(bases.astype(np.longdouble)))
    ns, ws = np.concatenate(parts), np.concatenate(logs)
    order = np.argsort(ns)
    return ns[order], ws[order]


def phi(q):
    return sum(math.gcd(a,q)==1 for a in range(1,q+1))


def build_s(q, ns, ws):
    mask = (ns-1) % q == 0
    n = ns[mask]
    a = ws[mask] * phi(q)
    A = np.concatenate((np.zeros(1,dtype=np.longdouble), np.cumsum(a,dtype=np.longdouble)))
    B = np.concatenate((np.zeros(1,dtype=np.longdouble), np.cumsum(a/n,dtype=np.longdouble)))
    def S(x):
        k = np.searchsorted(n,x,side='right')
        return B[k] - A[k]/x
    return S


def D(S,t):
    t = np.longdouble(t)
    x = np.exp(t)
    y = np.exp(t+1)
    return np.sqrt(y)/np.expm1(np.longdouble(0.5)) * (1+S(x)-S(y))


def filtered(S,t,m):
    w = [np.longdouble(math.comb(m,j))/2**m for j in range(m+1)]
    r2 = np.sqrt(np.longdouble(2))
    return sum(w[j]*w[k]*D(S,t+j+k*r2) for j in range(m+1) for k in range(m+1))


def naive_s(q,x):
    # Independent tiny reference implementation, by trial division.
    total = 0.0
    for n in range(2,int(x)+1):
        if (n-1)%q:
            continue
        p = next((d for d in range(2,math.isqrt(n)+1) if n%d==0),n)
        m=n
        while m%p==0:
            m//=p
        if m==1:
            total += phi(q)*math.log(p)*(1/n-1/x)
    return total


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--max-m',type=int,default=4)
    p.add_argument('--x',type=int,nargs='+',default=[30,100,300])
    p.add_argument('--q',type=int,nargs='+',default=[1,3,5,8])
    p.add_argument('--out',type=Path,default=Path(__file__).with_name('experiment.csv'))
    args=p.parse_args()
    assert args.max_m>=0 and min(args.x)>=1 and min(args.q)>=1
    nmax=math.ceil(max(args.x)*math.exp(1+args.max_m*(1+math.sqrt(2))))+4
    if nmax>50_000_000:
        raise SystemExit('Experiment exceeds 50 million cutoff; reduce x or max-m.')
    ns,ws=prime_powers(nmax)
    print(f'Enumerated {len(ns)} prime powers through {nmax:,}.')
    rows=[]
    for q in args.q:
        S=build_s(q,ns,ws)
        for x in (19,41.25,100.5):
            if x<=nmax:
                assert abs(float(S(x))-naive_s(q,x))<1e-11
        for x in args.x:
            t=np.log(np.longdouble(x))
            for m in range(args.max_m+1):
                y=filtered(S,t,m)
                rows.append((q,x,m,f'{float(y):.12g}',f'{float(y/4):.12g}'))
    with args.out.open('w',newline='') as f:
        wr=csv.writer(f);wr.writerow(['q','x','m','B_m_D_q','B_m_D_q_over_4']);wr.writerows(rows)
    print(f'Wrote {len(rows)} rows; direct trial-division cross-checks passed.')
    for q in args.q:
        print('q=',q,'x=',max(args.x),'values:',[r[3] for r in rows if r[0]==q and r[1]==max(args.x)])

if __name__=='__main__':
    main()
