#!/usr/bin/env python3
"""Separate rational checker using Lagrange interpolation coefficients in x=1/t.
Trust boundary: this checks propagation, not transcendental enclosures.
Regenerate the latter with certified_zeta.py and the analytic proof in paper.tex.
"""
import json
from pathlib import Path
from fractions import Fraction as Q
from math import floor,ceil,comb,prod
p=json.loads(Path(__file__).with_name('zeta_certificate.json').read_text())
s=int(p['scale']);ds=[Q(d) for d in p['ds']];n=len(ds)
tau=Q(p['tau']);km=p['km'];kp=p['kp']
assert 0<tau<1 and 1<=km<=kp<=n and len(set(ds))==n and all(d>0 for d in ds)
def iv(v):
    l,h=map(int,v);assert l<=h;return Q(l,s),Q(h,s)
M=iv(p['M']);vs=[iv(v) for v in p['samples']]
assert M[0]>=0 and len(vs)==len(ds) and all(l>=0 for l,h in vs)
def B(n,k,t):return sum(Q(comb(n,j))*t**j*(1-t)**(n-j) for j in range(k,n+1))
# Write B(t)/D(t) at t=1/x as P(x)/prod(x+d_i), where
# P(x)=sum_{j=k}^n choose(n,j)*(x-1)^(n-j).
# Its simple partial fraction at -d_i has residue P(-d_i)/prod_{h!=i}(d_h-d_i).
def linear(k,upper):
    ans=Q(0)
    for i,d in enumerate(ds):
        r=sum(comb(n,j)*(-d-1)**(n-j) for j in range(k,n+1)) / prod(e-d for h,e in enumerate(ds) if h!=i)
        ans+=r*vs[i][int((r>=0)==upper)]
    return ans
L=linear(kp,False)-Q(n,kp)*B(n-1,kp-1,tau)*M[1]
U=prod(1+d for d in ds)*linear(km,True)/B(n,km,tau)
l,u=map(Q,p['outward_bracket']);assert l<=L<=U<=u
assert tau==Q(p['a'],p['a']+p['threshold']**2)
assert max(0,ceil(L))==floor(U)==0
print('PASS: independent x=1/t rational propagation; integer count 0, conditional on the stored input enclosures and RH.')
