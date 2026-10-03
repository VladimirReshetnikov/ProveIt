#!/usr/bin/env python3
"""Finite numerical sanity checks only; not a replacement for the analytic proof.
Uses closed-form interval integrals for h, 64-point Gauss quadrature for its
antiderivative, and centered finite differences for the q derivative.
"""
from pathlib import Path
import math, numpy as np
from numpy.polynomial.legendre import leggauss
G,W=leggauss(64)
def h(q,r,z):
 E=math.exp(-q);R=2-E;om=1-E;out=0.
 pts=sorted(set([0.,r,z,1.]))
 for l,b in zip(pts,pts[1:]):
  mid=(l+b)/2;nu=int(mid>=z);A=int(mid>=r);de=-1+E*nu+R*A;w=b-l;d=l-r+(mid<r)
  mass=math.exp(-q*d)*(-math.expm1(-q*w))/om
  first=l*mass+math.exp(-q*d)*(-math.expm1(-q*w)-q*w*math.exp(-q*w))/(q*om)
  out+=(1/3+(3*R-7)*nu/6-de*z/6)*mass+de*first
 dr=-r*(1-z)/R if r<=z else -z*(1-r)/R
 zq=-E*z*(1-z)/R
 return q*out/R+r+q*E*dr-z/6-q*zq/6
def avg(q,z):
 E=math.exp(-q);R=2-E;I=(.5-(1-(1+q)*E)/q**2)/(1-E)
 return q*I-q/(3*R)+.5-q*E*z/(6*R*(1-E))
def eta(q,D,r,z):
 hb=avg(q,z);out=0.
 pts=sorted(set([0.,min(r,z),r]))
 for a,b in zip(pts,pts[1:]):
  mid=(a+b)/2;half=(b-a)/2
  out+=half*sum(w*(h(q,mid+half*g,z)-hb) for g,w in zip(G,W))
 return -(2-math.exp(-q))/D*(q*out-(h(q,r,z)-hb))
def lp(q,x):
 s,u,k=x;R=2-math.exp(-q);D=s+R*u;r=(min(k,s)+R*max(k-s,0))/D;z=s/D;p=.5*(q+math.log(R))
 return p*s+q*u-q*r+q*z/6+eta(q,D,r,z)
def children(x):
 s,u,k=x
 return [(s-1,u+int(i>=k),i) if i<s else (s+1,u-int(i<k),i+1) for i in range(s+u)]
rows=[]
for q in [2.,5.,10.,20.]:
 for m in [int(q*5),int(q*15)]:
  for s,k in [(0,0),(m//2,0),(m//2,m//2),(m//2,m-1),(m-1,m-1)]:
   x=s,m-s,k;base=lp(q,x);b=math.exp(.5*q)*math.sqrt(2-math.exp(-q))*(-math.expm1(-q))/q
   tr=sum(math.exp(lp(q,y)-base) for y in children(x))/b
   eps=1e-4
   deriv=(lp(q+eps,x)-lp(q-eps,x))/(2*eps)
   R=2-math.exp(-q);D=s+R*(m-s);mmean=avg(q,0)
   err=tr-deriv-mmean
   rows.append([q,*x,err,err/(q*q/D+q*math.exp(-q))])
   print(rows[-1],flush=True)
import json
assert len(rows)==40
assert max(abs(float(r[-1])) for r in rows)<1.0
Path(__file__).with_name('corrector-check.json').write_text(json.dumps(rows,indent=2)+'\n')
print('PASS: 40 finite residual checks; maximum scaled error',max(abs(float(r[-1])) for r in rows))
