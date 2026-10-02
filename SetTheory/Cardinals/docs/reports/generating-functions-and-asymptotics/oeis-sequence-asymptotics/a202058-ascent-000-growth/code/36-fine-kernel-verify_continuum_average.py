#!/usr/bin/env python3
"""Finite-grid checks of the fixed-q, large-state continuum mean formula."""
import math,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def geom(logfirst,step,count):
    if count<=0:return 0.
    return math.exp(logfirst)*(-math.expm1(-step*count))/(-math.expm1(-step))

def residual(q,s,u,k):
    R=2-math.exp(-q); D=s+R*u; m=s+u
    p=(q+math.log(R))/2
    logb=p+math.log(-math.expm1(-q))-math.log(q)
    r=(min(k,s)+R*max(k-s,0))/D
    dr=(-k*u if k<=s else -s*(m-k))/(D*D)
    B=r+q*math.exp(-q)*dr
    # Geometric sums of the exact child ψ ratios, already divided by b.
    val=0.
    n=min(s,k)
    if n:val+=geom(-p+q*r-logb,q/(D-1),n)
    if k<s:val+=geom(-p+q+q*r-q*k/(D+R-1)-logb,q/(D+R-1),s-k)
    i=max(s,k); n=m-i
    if n:val+=geom(p+q*r-q*(R*i+(1-R)*s+1)/(D+1)-logb,q*R/(D+1),n)
    if k>s:val+=geom(p-q+q*r-q*(s+1)/(D+1-R)-logb,q*R/(D+1-R),k-s)
    return val-D/R+B
out=[]
for q in [1.,5.,10.,20.]:
 for s,u in [(1000,2000),(3000,2000),(6000,2000)]:
    R=2-math.exp(-q);D=s+R*u;z=s/D
    measured=sum(residual(q,s,u,k)*(1 if k<s else R)/D for k in range(s+u))
    I=(.5-(1-(1+q)*math.exp(-q))/q**2)/(-math.expm1(-q))
    predicted=q*I+q*(z-1)/(2*R)+.5
    out.append({'q':q,'s':s,'u':u,'D':D,'z':z,'exact_discrete_rank_mean':measured,'continuum_limit':predicted,'absolute_error':abs(measured-predicted),'error_times_D_over_q_squared':abs(measured-predicted)*D/q**2})
assert max(x['error_times_D_over_q_squared'] for x in out)<3
result={'scope':'Finite checks of the continuum first-order formula, not proof of a uniform asymptotic or a lognormal equivalent.','all_assertions_passed':True,'cases':out}
(ROOT/'continuum-average-verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
