#!/usr/bin/env python3
"""Supplementary exact arithmetic and algebra tests, not the main certificate."""
from fractions import Fraction as Q
from math import comb
import random,json
import certify as c

rng=random.Random(20261002)
checks=0
for _ in range(2000):
    qs=sorted(Q(rng.randint(-10**6,10**6),rng.randint(1,10**5)) for j in range(2))
    rs=sorted(Q(rng.randint(-10**6,10**6),rng.randint(1,10**5)) for j in range(2))
    a=c.I.endpoints(*qs);b=c.I.endpoints(*rs)
    for got,vals in [(a+b,[x+y for x in qs for y in rs]),
                     (a-b,[x-y for x in qs for y in rs]),
                     (a*b,[x*y for x in qs for y in rs])]:
        c.require(Q(got.lo, c.S) <= min(vals) <= max(vals) <= Q(got.hi, c.S));checks += 1
    if b.lo*b.hi>0:
        got=a/b;vals=[x/y for x in qs for y in rs]
        c.require(Q(got.lo, c.S) <= min(vals) <= max(vals) <= Q(got.hi, c.S));checks += 1
    pos=c.I.endpoints(abs(qs[0]),abs(qs[0])+abs(qs[1]))
    root=pos.sqrt()
    c.require(Q(root.lo, c.S) ** 2 <= Q(pos.lo, c.S))
    c.require(Q(root.hi, c.S) ** 2 >= Q(pos.hi, c.S));checks += 1

def binom(x,n):
    ans=Q(1)
    for j in range(n):ans*=Q(x-j,j+1)
    return ans

def transfer(alpha,J):
    h=[Q(1)]
    for m in range(1,J+1):
        h.append(sum(h[j]*(binom(-alpha-1-j,m+1-j)-(-1)**(m+1-j)*(1+alpha))
                     for j in range(m))/m)
    return h
c.require(transfer(Q(1, 2), 3) == [Q(1), Q(3, 8), Q(25, 128), Q(105, 1024)])
c.require(transfer(Q(3, 2), 1) == [Q(1), Q(15, 8)])

# Algebraically independent formula check of the first Puiseux coefficients.
pi=c.pi_bound()
for d in (3,4):
    out=c.certify(d,pi);rho=out['rho'];aa=out['puiseux']
    a=c.enumerate_subset(d,c.N);f,_,_=c.jet_F(a,rho,out['tau'],d)
    Gyy=2*f[(0,2)];Gyyy=6*f[(0,3)];Gyyyy=24*f.get((0,4),c.I(0))
    Gzy=-f[(2,1)]/rho;Gzyy=-2*f[(2,2)]/rho;Gzz=2*f[(4,0)]/(rho*rho)
    a1=aa['a1']
    a2=rho*Gzy/Gyy-Gyyy*a1*a1/(6*Gyy)
    a3=-(Gyy*a2*a2/2-rho*Gzy*a2+rho*rho*Gzz/2+
         Gyyy*a1*a1*a2/2-rho*Gzyy*a1*a1/2+Gyyyy*a1**4/24)/(Gyy*a1)
    c.require(max(a2.lo, aa['a2'].lo) <= min(a2.hi, aa['a2'].hi))
    c.require(max(a3.lo, aa['a3'].lo) <= min(a3.hi, aa['a3'].hi))
print(json.dumps({'interval_primitive_exact_tests':checks,'seed':20261002,
                  'transfer_coefficients_verified':True,
                  'independent_a2_a3_formula_cross_checks':[3,4]},indent=2))
