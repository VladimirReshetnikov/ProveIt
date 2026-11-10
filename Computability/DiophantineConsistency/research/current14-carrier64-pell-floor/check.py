#!/usr/bin/env python3
"""Finite exact controls for the external Pell-floor argument."""
from collections import Counter
from math import comb
import hashlib
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent;D=HERE.parents[1]
pins={'research/current14-carrier64-sharp-growth/result.json':'f7a18ac373fc9c37cbefd8e675b6e71b931ea51d80b6355cee0d164fbea37ea1',
      'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json':'f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'}
for p,h in pins.items():
    if hashlib.sha256((D/p).read_bytes()).hexdigest()!=h:raise RuntimeError('pin mismatch')

# Exact identity behind L=(2A-1)^2/(2P) > (X+1)^2/X.
one={(0,0):1};X={(1,0):1};Y={(0,1):1}
def scale(n,a):return {k:n*v for k,v in a.items() if n*v}
def add(a,b):
    c=Counter(a);c.update(b)
    return {k:v for k,v in c.items() if v}
def sub(a,b):return add(a,scale(-1,b))
def mul(a,b):
    c=Counter()
    for x,cx in a.items():
        for y,cy in b.items():
            c[tuple(s+t for s,t in zip(x,y))]+=cx*cy
    return {k:v for k,v in c.items() if v}
xp=add(X,one);Y2=mul(Y,Y)
A=add(mul(Y,xp),scale(2,one));P=add(scale(2,mul(X,Y2)),one)
lhs=sub(mul(X,mul(sub(scale(2,A),one),sub(scale(2,A),one))),mul(mul(xp,xp),scale(2,P)))
rhs=sub(add(scale(12,mul(mul(X,Y),xp)),scale(9,X)),scale(2,mul(xp,xp)))
if lhs!=rhs:raise RuntimeError('lower-base identity failed')

def psi(p,n):
    a,b=0,1
    for _ in range(n):a,b=b,2*p*b-a
    return a

ratio_cases=0
for N in range(13,21):
    R=2*N+1; x=1<<R
    head=sum(comb(2*N,i)*x**(N-i) for i in range(N+1))
    if head%2:raise RuntimeError('integer head failed')
    T=head//2; hn=(x+1)**(2*N);hd=2*x**N
    if not (0<hn-T*hd and 4*(hn-T*hd)<hd and 144*N<x):
        raise RuntimeError('fractional/error envelope control failed')
    for y in (x**N//2+1,T,T+1,x**N-1):
        A0=y*(x+1)+2;P0=2*x*y*y+1
        c=psi(A0,2*N+1);k=2*psi(P0,N+1)
        delta=c*hd-hn*k
        if not (delta>0 and x*delta<36*N*hd*k and c//k==T):
            raise RuntimeError('Pell-floor control failed')
        ratio_cases+=1

valuation_cases=0
for N in range(1,2001):
    middle=comb(2*N,N)//2
    v=(middle&-middle).bit_length()-1
    if v!=N.bit_count()-1:raise RuntimeError('central-binomial valuation failed')
    valuation_cases+=1

# Verify the rank-bound algebra at representative q (identity is polynomial).
for q in range(2,1000):
    if (q*q-q-1)*(q*q-1)+(2*q+1)*(q-1)!=q**4-q**3:
        raise RuntimeError('rank upper identity failed')
    if (4*q**3-1)-((4*q-2)*(q*q-1)+(2*q+1)*(q-1))!=5*q-2:
        raise RuntimeError('rank lower implication identity failed')
result={'pins':pins,'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'lower_base_identity':'exact sparse polynomial','ratio_controls':ratio_cases,
        'central_binomial_valuation_controls':valuation_cases,'rank_algebra_controls':998,
        'scope':'external proof controls; no Lean run or complete reverse equivalence'}
print(json.dumps(result,sort_keys=True,indent=2))
