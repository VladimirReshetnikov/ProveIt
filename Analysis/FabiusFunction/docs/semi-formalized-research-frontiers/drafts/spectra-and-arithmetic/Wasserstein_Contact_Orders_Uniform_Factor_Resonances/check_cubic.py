#!/usr/bin/env python3
"""Exact endpoint coefficient checks and finite regressions; not a universal proof."""
from fractions import Fraction as F
import json
import math


def du(a,b):return [-1/(a*a*b),1/(2*a*b),F(0)]
def duu(a,b):return [2/(a*a*a*b),-1/(a*a*b),1/(4*a*b)]
def duv(a,b):return [1/(a*a*b*b),-1/(2*a*a*b)-1/(2*a*b*b),1/(4*a*b)]
def add(v,w,c=F(1)):
    for i in range(3):v[i]+=c*w[i]

a,b,c=F(1,2),F(1,4),F(1,8)
k1=[F(0)]*3
add(k1,du(a,b),F(1,2));add(k1,du(b,F(1)));add(k1,du(c,b),F(3,32))
k2=[F(0)]*3
add(k2,duu(a,b),F(1,2))
add(k2,duu(b,F(1)));add(k2,du(b,F(1)),F(2))
add(k2,duu(c,b),F(9,128));add(k2,du(c,b),F(3,8))
add(k2,duv(a,b),F(1));add(k2,duv(b,c),F(3,16));add(k2,duv(a,c),F(3,8))
assert k1==[F(-48),F(11,2),F(0)]
assert k2==[F(672),F(-122),F(121,16)]

def sinc(z):return 1.0 if z==0 else math.sin(z)/z
def uf(u,t):return sinc(math.pi*u*t)
def udf(u,t):
    z=math.pi*u*t
    return (math.cos(z)-sinc(z))/u
def uddf(u,t):
    z=math.pi*u*t
    return (-z*math.sin(z)-2*math.cos(z)+2*sinc(z))/(u*u)
def df(points,t):return sum(math.cos(2*math.pi*t*x) for x in points)/len(points)

checks=2
for t in [.1,.7,1.3,2.7,4.1,6.6,8.2,10.3]:
    A,B,C,D=[uf(u,t) for u in [.5,.25,.125,1]]
    Ap,Bp,Cp=[udf(u,t) for u in [.5,.25,.125]]
    App,Bpp,Cpp=[uddf(u,t) for u in [.5,.25,.125]]
    D2=df([-.25,.25],t)
    D8=df([(2*j-7)/16 for j in range(8)],t)
    E2=df([-1/16,1/16],t)
    kap1=D2*Ap*B+D*Bp+.75*D8*B*Cp
    kap2=D2*App*B+D*(Bpp+2*Bp)+D8*B*(9/16*Cpp+3*Cp)+2*D2*Ap*Bp+1.5*D8*Bp*Cp+1.5*D2*E2*Ap*Cp
    P1=D*(Ap*B*C+A*Bp*C+.75*A*B*Cp)
    P2=D*(App*B*C+A*(Bpp+2*Bp)*C+A*B*(9/16*Cpp+3*Cp)+2*Ap*Bp*C+1.5*Ap*B*Cp+1.5*A*Bp*Cp)
    assert abs(A*C*kap1-P1)<1e-12
    assert abs(A*C*kap2-P2)<1e-11
    checks+=2

for rho in [.01,.2,1,7]:
    for aa in [0,.01,.2,.5,1,2,10]:
        for bb in [0,.01,.2,.5,1,2,10]:
            negative=max(aa+bb-rho,0)
            bound=8*aa**3/rho**2+2*math.sqrt(2)*bb**1.5/math.sqrt(rho)
            assert negative<=bound+1e-12
            checks+=1

def tail(q):return math.prod(sinc(8*math.pi*q**k) for k in range(4,100))
P4=tail(.5)
rows=[]
for sign in [-1,1]:
    for j in range(2,8):
        delta=sign*10**(-j);q=.5+delta
        derivative=.125*uf(q,8)*uf(q*q,8)*uf(q*q*q,8)*tail(q)
        ratio=derivative/delta**3
        if j==7:assert abs(ratio+6*P4)<1e-5
        rows.append({'delta':delta,'defect_over_delta_cubed':ratio})
        checks+=1

out={
 'status':'PASS','checks':checks,
 'scope':'Exact rational endpoint coefficients; finite floating-point Fourier and clipping regressions only',
 'kappa1_endpoint_coefficients':[str(x) for x in k1],
 'kappa2_endpoint_coefficients':[str(x) for x in k2],
 'P4_truncation_k4_to99':P4,
 'cubic_lower_asymptotic_constant':3*P4/(math.pi*(1+16*math.pi)),
 'defect_ratio_rows':rows,
 'not_computed':['optimal Wasserstein distance','weighted-integral suprema','numerical cubic upper constant','cubic one-sided limits'],
}
print(json.dumps(out,indent=2))
