#!/usr/bin/env python3
"""Conditional lognormal fits, with high-precision linear algebra.

The reported fit precision is computational precision, not an uncertainty or
proof. Basis changes and interval changes are essential sensitivity checks.
"""
from pathlib import Path
import json
import mpmath as mp

ROOT=Path(__file__).resolve().parent
mp.mp.dps=90
def read(name):
    return {int(n):mp.mpf(v) for n,v in (l.split() for l in
            (ROOT/name).read_text().splitlines())}
exact=read('exact-counts-400.txt')
floating=read('floating-counts-1000.txt')
mu=8/(3*mp.pi**2)
h={n:mp.log(v) for n,v in floating.items()}
h.update({n:mp.log(v)-mp.loggamma(n+1)-n*mp.log(mu) for n,v in exact.items()})

def row(n,j1,j2):
    L=mp.log(n)
    return [mp.mpf(1),L,L**2]+[L**k/n for k in range(j1+1)]+[
            L**k/n**2 for k in range(j2+1)]

out={'caveat':'All inferred coefficients are conditional on the fitted ansatz. '
     'Small residuals and apparent stabilization do not establish asymptotics.',
     'model':'h_n=c0+c1 log(n)+c2 log(n)^2 + P_j1(log(n))/n + Q_j2(log(n))/n^2',
     'fits':[]}
for lo,hi in [(100,200),(200,400),(400,800),(500,1000)]:
    if hi>max(h):continue
    ns=list(range(lo,hi+1,max(1,(hi-lo)//80)))
    for j1,j2 in [(1,-1),(2,-1),(3,-1),(2,0),(2,1),(2,2),(2,3),(2,4)]:
        coeff,res=mp.qr_solve(mp.matrix([row(n,j1,j2) for n in ns]),
                              mp.matrix([h[n] for n in ns]))
        maxerr=max(abs(sum(x*y for x,y in zip(row(n,j1,j2),coeff))-h[n])
                   for n in ns)
        validation_end=min(2*hi,max(h))
        verr=max([abs(sum(x*y for x,y in zip(row(n,j1,j2),coeff))-h[n])
                    for n in range(hi+1,validation_end+1)] or [mp.mpf(0)])
        result=dict(lo=lo,hi=hi,j1=j1,j2=j2,
                    source='exact' if hi<=max(exact) else 'long-double',
                    alpha=mp.nstr(coeff[2],30),beta=mp.nstr(coeff[1],30),
                    gamma=mp.nstr(coeff[0],30),amplitude=mp.nstr(mp.exp(coeff[0]),30),
                    coefficients=[mp.nstr(c,30) for c in coeff],
                    max_fit_error=mp.nstr(maxerr,8),
                    validation_end=validation_end,
                    max_validation_error=mp.nstr(verr,8))
        out['fits'].append(result)
(ROOT/'log-polynomial-fits.json').write_text(json.dumps(out,indent=2)+'\n')
for fit in out['fits']:
    print(fit['lo'],fit['hi'],fit['j1'],fit['j2'],fit['alpha'],fit['beta'],fit['max_fit_error'],fit['max_validation_error'])
