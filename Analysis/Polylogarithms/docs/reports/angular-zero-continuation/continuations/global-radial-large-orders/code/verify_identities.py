#!/usr/bin/env python3
"""Exact positive Gaussian identities and independent elementary controls.

All acceptance tests use Fraction, not floating point. The infinite-series
conclusions use the remainder proofs in article.tex.
"""
from __future__ import annotations

if not __debug__:
    raise RuntimeError('Run without -O: exact assertion checks are required.')
from fractions import Fraction as Q
from math import comb
from pathlib import Path
import json
from verify_global import rat, dec_interval
ROOT=Path(__file__).resolve().parents[1]

def harmonic(n: int, b: int) -> Q:
    return sum((Q(1,k**b) for k in range(1,n+1)),Q(0))

def coeff(n: int, a: int, b: int) -> Q:
    return harmonic(n-1,b)/n**a

def gaussian(a: int, b: int, N: int) -> tuple[Q,Q,list[Q]]:
    if any(type(v) is not int for v in (a,b,N)):
        raise TypeError('a, b, N must be integers')
    if min(a,b,N)<1:
        raise ValueError('a, b, N must be positive')
    ms=[coeff(2*j+3,a,b)/Q(2*j+2) for j in range(N)]
    bs=[sum(((-1)**j*comb(k,j)*ms[j] for j in range(k+1)),Q(0)) for k in range(N)]
    assert all(x>0 for x in bs)
    partial=sum((Q(k+1,2**(k+1))*bs[k] for k in range(N)),Q(0))
    bound=Q(N+2,2**N)*coeff(3,a,b)/2
    return partial,partial+bound,bs

def atan_bounds(x: Q,N: int) -> tuple[Q,Q]:
    s=sum(((-1)**k*x**(2*k+1)/Q(2*k+1) for k in range(N)),Q(0))
    t=s+(-1)**N*x**(2*N+1)/Q(2*N+1)
    return min(s,t),max(s,t)

def elementary_bounds() -> tuple[Q,Q]:
    # Machin's identity: pi=16 atan(1/5)-4 atan(1/239).
    a=atan_bounds(Q(1,5),100); b=atan_bounds(Q(1,239),35)
    pi=(16*a[0]-4*b[1],16*a[1]-4*b[0])
    # log 2=2 atanh(1/3); positive tail bounded by its geometric majorant.
    N=110; x=Q(1,3)
    lo=2*sum((x**(2*k+1)/Q(2*k+1) for k in range(N)),Q(0))
    hi=lo+2*x**(2*N+1)/Q(2*N+1)/(1-x*x)
    return pi[0]*lo/8,pi[1]*hi/8

def run() -> dict:
    rows=[]; total=0
    for a,b in [(1,1),(1,2),(2,1),(2,2),(3,4),(8,1),(8,2),(9,4),(12,1)]:
        lo,hi,bs=gaussian(a,b,80); total+=len(bs)
        if (a,b)==(1,1):
            elo,ehi=elementary_bounds()
            assert lo<elo<ehi<hi
        rows.append({'a':a,'b':b,'terms':80,'minus_g_lower':rat(lo),
                     'minus_g_upper':rat(hi),'display_lower':dec_interval(lo,18)[0],
                     'display_upper':dec_interval(hi,18)[1],
                     'B0':rat(bs[0]),'B79':rat(bs[-1])})
    # Finite algebraic remainder identity for the differentiated geometric sum.
    # (1-q)^2 sum_{k=0}^{N-1}(k+1)q^k = 1-(N+1)q^N+Nq^{N+1}.
    from verify_global import mul
    for N in range(1,101):
        left=mul([Q(k+1) for k in range(N)],[Q(1),Q(-2),Q(1)])
        right=[Q(0)]*(N+2);right[0]=1;right[N]=-(N+1);right[N+1]=N
        assert left==right
    out={'status':'PASS','positive_binomial_moments_checked':total,
         'geometric_remainder_identities_checked':100,
         'independent_pi_log2_control':'strictly inside the (a,b)=(1,1) enclosure',
         'enclosures':rows}
    (ROOT/'data'/'identity_certificates.json').write_text(json.dumps(out,indent=2)+'\n')
    return out
if __name__=='__main__':
    r=run();print('PASS:',r['positive_binomial_moments_checked'],'positive rational moments; 100 remainder identities')
    for x in r['enclosures']:print(x['a'],x['b'],x['display_lower'],x['display_upper'])
