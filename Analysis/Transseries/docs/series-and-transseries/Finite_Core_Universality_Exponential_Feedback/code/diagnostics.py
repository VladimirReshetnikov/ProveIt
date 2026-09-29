#!/usr/bin/env python3
"""Floating-point diagnostics; not interval certificates.

Compute log coefficients by a positive recurrence and evaluate the bare
and finite-core saddle formulae. Exact checks live in verify_exact.py.
"""
from __future__ import annotations
import argparse, csv, json, math, time
from pathlib import Path
import numpy as np
from scipy.special import logsumexp
from scipy.optimize import root, brentq
ROOT=Path(__file__).resolve().parents[1]

def log_coefficients(nmax: int,p: float,a: float=1.0,cutoff: int | None=None):
    E=np.full((nmax+1,nmax+1),-np.inf,dtype=float)
    E[1:,0]=0.0
    lu=np.full(nmax+1,-np.inf)
    loglam=np.log(a)+p*np.log(np.arange(1,nmax+1,dtype=float))
    for n in range(1,nmax+1):
        js=np.arange(1,min(n,cutoff or nmax)+1)
        lu[n]=logsumexp(E[js,n-js])
        if n<nmax:
            ks=np.arange(1,n+1)
            terms=E[1:nmax-n+1,n-ks]+(np.log(ks)+lu[ks])[None,:]
            E[1:nmax-n+1,n]=loglam[:nmax-n]-math.log(n)+logsumexp(terms,axis=1)
    return lu

def bare_saddle(n: int,p: float,a: float=1.0):
    f=lambda r:math.log(r)+(p-1)*math.log1p(r)+p*r-math.log(a)-(p-1)*math.log(n)
    r=brentq(f,1e-15,max(2.,math.log(n)+abs(math.log(a))+5))
    j=n/(1+r);k=n-j;D=1+2*p*r+p*r*r
    logS=k*(1+p*r)-.5*math.log(D)
    return {'r':r,'j':j,'k':k,'t':k/(a*j**p),'logS':logS,'sigma':math.sqrt(k/D)}

def core_stats(q: float,u: float,M:int,p:float,a:float):
    js=np.arange(1,M+1,dtype=float); lam=a*js**p
    ts=np.exp(js*math.log(q)+lam*u)
    ph=float(ts.sum());pu=float(np.dot(lam,ts));pq=float(np.dot(js,ts))/q
    pqq=float(np.dot(js*(js-1),ts))/q**2
    pqu=float(np.dot(js*lam,ts))/q;puu=float(np.dot(lam*lam,ts))
    if pu>=1: raise ValueError('Core solution is beyond its regular branch.')
    up=pq/(1-pu);upp=(pqq+2*pqu*up+puu*up*up)/(1-pu)
    return ph,up,upp,1/(1-pu)

def finite_core_saddle(n:int,p:float,M:int,a:float=1.0):
    if n < 1 or M < 1 or p <= 1 or a <= 0:
        raise ValueError("Require n,M >= 1, p > 1 and a > 0.")
    base=bare_saddle(n,p,a)
    # Use logs to keep all unknowns positive. This solves all three equations.
    def fun(x):
        q,u,j=np.exp(x)
        js=np.arange(1,M+1,dtype=float);lam=a*js**p
        ex=js*math.log(q)+lam*u
        if np.max(ex)>600: return np.array([1e20,1e20,1e20])
        terms=np.exp(ex);ph=terms.sum();pu=np.dot(lam,terms)
        pq=np.dot(js,terms)/q
        up=pq/(1-pu)
        return [math.log(u/ph), (math.log(q)+a*p*j**(p-1)*u)/(1+abs(math.log(q))),
                (j+a*j**p*q*up)/n-1]
    x0=np.log([base['t'],base['t'],base['j']])
    sol=root(fun,x0,tol=1e-11)
    if not sol.success and np.max(np.abs(fun(sol.x)))>1e-8:
        raise RuntimeError(f'saddle failed n={n},p={p},M={M}: {sol.message}')
    q,u,j=np.exp(sol.x)
    if not (0 < j < n):
        raise ValueError('The computed saddle is outside 0 < j < n.')
    ph,up,upp,A=core_stats(q,u,M,p,a);k=n-j
    B=a*j**p*(q*up+q*q*upp);C=1+p*k/j
    H=a*p*(p-1)*j**(p-2)*u;Delta=C*C-H*B
    if Delta<=0: raise ValueError('Nonpositive saddle determinant.')
    return {'n':n,'p':p,'M':M,'q':q,'u':u,'j':j,'k':k,'sigma':math.sqrt(B/Delta),
            'log_approx':math.log(A)+a*j**p*u-k*math.log(q)-.5*math.log(Delta),
            'residual':float(np.max(np.abs(fun(sol.x))))}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--order',type=int,default=1000)
    ap.add_argument('--powers',type=float,nargs='+',default=[2.,3.]);args=ap.parse_args()
    if args.order < 50 or any(not math.isfinite(p) or p <= 1 for p in args.powers):
        ap.error('Require --order >= 50 and finite --powers greater than 1.')
    data=ROOT/'data';data.mkdir(exist_ok=True);rows=[];start=time.perf_counter()
    for p in args.powers:
        lu=log_coefficients(args.order,p)
        M=math.floor(1/(p-1)+1e-10)+1
        ns=sorted(set([n for n in [50,100,200,500,1000,1500,args.order] if n<=args.order]))
        for n in ns:
            bs=bare_saddle(n,p);cs=finite_core_saddle(n,p,M)
            corrected=bs['logS']+2*bs['k']**2/bs['j']**p
            row={**cs,'log_u':float(lu[n]),'u_over_finite_core':math.exp(lu[n]-cs['log_approx']),
                 'u_over_bare':math.exp(lu[n]-bs['logS']),
                 'u_over_first_correction':math.exp(lu[n]-corrected),
                 'bare_r':bs['r'],'bare_j':bs['j']}
            rows.append(row)
            print(f"p={p:g},n={n}: core ratio {row['u_over_finite_core']:.9g}, "
                  f"bare {row['u_over_bare']:.9g}, correction {row['u_over_first_correction']:.9g}",flush=True)
        np.savez_compressed(data/f'log_coefficients_p{p:g}.npz',n=np.arange(args.order+1),log_u=lu)
    with (data/'saddle_diagnostics.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
    (data/'numerical_verification.json').write_text(json.dumps({'order':args.order,
        'powers':args.powers,'rows':rows,'runtime_seconds':time.perf_counter()-start,
        'scope':'IEEE double precision, no interval arithmetic; asymptotic diagnostics only.'},indent=2)+'\n')
if __name__=='__main__':main()
