#!/usr/bin/env python3
"""Exact arithmetic certificate for streamed-conditioning coefficient <54.
Imports no matrix multiplication or numerical optimization package.
"""
from fractions import Fraction as F
from math import isqrt
import json

def require(ok,msg='certificate check failed'):
    if not ok: raise ArithmeticError(msg)

SCALE=10**14

def sqrt_interval(x):
    x=F(x);q=isqrt(x.numerator*SCALE*SCALE//x.denominator)
    lo,hi=F(q,SCALE),F(q+1,SCALE)
    require(lo*lo<=x<=hi*hi)
    return lo,hi

def arctan_interval(x,N=64):
    s=sum(((-1)**k*x**(2*k+1)/F(2*k+1) for k in range(N)),F())
    t=(-1)**N*x**(2*N+1)/F(2*N+1)
    return min(s,s+t),max(s,s+t)

def add(x,y): return x[0]+y[0],x[1]+y[1]
def mul(x,y): return x[0]*y[0],x[1]*y[1]
def div(x,y): return x[0]/y[1],x[1]/y[0]
def pt(x):return F(x),F(x)
def encode(x):return {'lower':str(x[0]),'upper':str(x[1]),'decimal_lower':float(x[0]),'decimal_upper':float(x[1])}

a,b=arctan_interval(F(1,5)),arctan_interval(F(1,239))
pi=(16*a[0]-4*b[1],16*a[1]-4*b[0]);x=F(1,3);N=64
l=sum((2*x**(2*k+1)/F(2*k+1) for k in range(N)),F())
ln2=(l,l+2*x**(2*N+1)/F(2*N+1)/(1-x*x))
kappa=div(mul(pi,sqrt_interval(2)),ln2)

def cut_profile(r):
    if r==1:return 0
    a=r//2;b=r-a
    return 2*a*b+max(cut_profile(a),cut_profile(b))

rs=[16,16,8,6,5,4]
f=[F(12499,10**6),F(12499,10**6),F(2083,250000),F(107,20000),F(219,50000),F(513,200000)]
m=[F(1),F(1,8),F(1,64),F(1,256),F(1,768),F(1,1920)]
require([cut_profile(r) for r in rs]==[170,170,42,24,18,10])
for i in range(1,len(rs)):require(m[i]==m[i-1]*F(2,rs[i-1]))
A=[sum(f[:i+1]) for i in range(5)]
At=A[-1]+f[-1]/(1-F(5,8))
require(A==list(map(F,['.012499','.024998','.033330','.038680','.043060'])))
require(At==F(499,10000))
# Exact certificates for the needed logarithm upper bounds.
require(6**200<2**517)
require(5**500<2**1161)
logs=[F(4),F(4),F(3),F(517,200),F(1161,500),F(2)]
cum=A+[At]
high=[F(9,10)+(2 if i==0 else 1)*aa*lr for i,(aa,lr) in enumerate(zip(cum,logs))]
require(max(high)<1)
# These bounds dominate both fresh-side and packet-padding exponents.
other=[(2*lr+1)*aa for aa,lr in zip(cum,logs)]
require(max(other)<1)
require(F(5,8)>F(11,20))

gamma=sqrt_interval(F(2,5));denom=(1-gamma[1],1-gamma[0])

def coefficient(arities,fractions,masses):
    cs=[]
    for r,fi,mi in zip(arities,fractions,masses):
        beta=div(sqrt_interval(cut_profile(r)),pt(r))
        term=div(mul(mul(kappa,pt(mi)),beta),sqrt_interval(fi))
        cs.append(term)
    cs[-1]=div(cs[-1],denom)
    total=pt(0)
    for c in cs:total=add(total,c)
    return total,cs

C,contributions=coefficient(rs,f,m)
require(C[1]<54)
# Stronger prior composition: newly filed conditioning + earlier variable arities.
prs=[13,14,8,6,4]
pf=[F(27,2000),F(51,4000),F(141,20000),F(107,20000),F(27,6400)]
pm=[F(1),F(2,13),F(2,91),F(1,182),F(1,546)]
prior,prior_terms=coefficient(prs,pf,pm)
require(C[1]<prior[0])
# The newest packet's displayed fixed-r16 conditioning coefficient.
old=mul(div(mul(pt(F(5,2)),mul(pi,sqrt_interval(17))),ln2),add(pt(1),div(pt(1),mul(pt(3),sqrt_interval(3)))))
require(prior[1]<old[0])
print(json.dumps({'status':'passed','scope':'exact schedule arithmetic; contraction identities imported from reviewed sources','arities':rs,'fractions':[str(x) for x in f],'wire_masses':[str(x) for x in m],'cut_profiles':[cut_profile(r) for r in rs],'cumulative_capacities':[str(x) for x in cum],'high_degree_exponents':[str(x) for x in high],'other_exponents':[str(x) for x in other],'contributions':[encode(x) for x in contributions],'coefficient':encode(C),'stronger_prior_composition':encode(prior),'newest_packet_displayed_coefficient':encode(old)},indent=2))
