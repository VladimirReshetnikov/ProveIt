#!/usr/bin/env python3
"""Exact certificates for a multistage slope-four asymmetric schedule.
This checks local algebra/numerics; the all-size proof is in analytic_research.md.
"""
from fractions import Fraction as F
from math import isqrt
import json, sys

def require(ok, msg):
    if not ok: raise ValueError(msg)

def atan_interval(q, n=100):
    x=F(1,q)
    s=sum(((-1)**j*x**(2*j+1)/ (2*j+1) for j in range(n)), F(0))
    nxt=(-1)**n*x**(2*n+1)/(2*n+1)
    return min(s,s+nxt),max(s,s+nxt)

def pi_interval():
    a,b=atan_interval(5); c,d=atan_interval(239)
    return 16*a-4*d,16*b-4*c

def ln2_interval(n=100):
    x=F(1,3)
    s=2*sum((x**(2*j+1)/(2*j+1) for j in range(n)),F(0))
    err=2*x**(2*n+1)/((2*n+1)*(1-x*x))
    return s,s+err

def sqrt_interval(x, digits=32):
    scale=10**digits
    k=isqrt((x.numerator*scale*scale)//x.denominator)
    lo,hi=F(k,scale),F(k+1,scale)
    require(lo*lo<=x<=hi*hi,'sqrt certificate')
    return lo,hi

def coefficient_interval():
    rs=[13,14,8,6,5,4]
    caps=[F(27,2000),F(21,800),F(333,10000),F(193,5000),F(43,1000),F(499,10000)]
    us=[x-(caps[i-1] if i else 0) for i,x in enumerate(caps)]
    lo=hi=F(0); mass=F(1)
    for r,u in zip(rs,us):
        x,y=sqrt_interval(2*F(r-1,r)/u)
        lo+=mass*x; hi+=mass*y; mass*=F(2,r)
    require(mass==F(1,2730),'tail mass')
    R=F(63,1000)-caps[-1]; q=F(3,4); u=R*(1-q)
    require(R==F(131,10000) and u==F(131,40000),'tail taper')
    a,b=sqrt_interval(F(4,3)/u)
    s3lo,s3hi=sqrt_interval(F(3))
    dlow=1-F(4,3)/s3lo; dhigh=1-F(4,3)/s3hi
    require(0<dlow<=dhigh,'geometric convergence')
    lo+=mass*a/dhigh; hi+=mass*b/dlow
    plo,phi=pi_interval(); llo,lhi=ln2_interval()
    return plo*lo/lhi,phi*hi/llo

def main():
    # Strict packing margins, witnessed by integer inequalities.
    margins={
      'root13':13**27<2**100,
      'stage14':14**21<2**80,
      'stage8':3*F(333,10000)<F(1,10),
      'stage6':6**193<2**500,
      'stage5':5**43<2**100,
      'stage4':2*F(499,10000)<F(1,10),
      'tail3':3**63<2**100,
      'uniform_taper_growth':F(4,3)<F(10,7),
      'packet_degrees':F(63,1000)<F(9,10),
      'fresh_and_padding_bound':F(1,5)+F(63,1000)<1,
    }
    for key,ok in margins.items(): require(ok,key)
    lo,hi=coefficient_interval()
    lower=F(63781173756244,10**12)
    upper=F(63781173756245,10**12)
    require(lower<lo<=hi<upper,'display interval')
    require(hi<64,'safe coefficient64')
    require(hi<F(6619,100),'beats66.19')
    out={'status':'pass','scope':'exact component certificates; all-size proof is separate',
         'strict_margins':margins,'coefficient_interval':['63.781173756244','63.781173756245'],
         'safe_eventual_coefficient':64,'optimizations_enabled':not __debug__,
         'source':'new rational multistage schedule; inherited asymmetric packing and slope-four kernel'}
    print(json.dumps(out,indent=2))
if __name__=='__main__': main()
