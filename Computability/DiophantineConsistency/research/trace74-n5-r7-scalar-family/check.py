#!/usr/bin/env python3
"""Exact polynomial certificate for a conditional n=5,r=7 scalar family."""
import json,sys
from collections import defaultdict
from math import comb
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
def add(*ps):
    out=defaultdict(int)
    for p in ps:
        for i,c in p.items():out[i]+=c
    return {i:c for i,c in out.items() if c}
def scale(c,p):return {i:c*v for i,v in p.items() if c*v}
def mul(p,q):
    out=defaultdict(int)
    for i,u in p.items():
        for j,v in q.items():out[i+j]+=u*v
    return {i:c for i,c in out.items() if c}
def shifted(p,s):
    out=defaultdict(int)
    for i,v in p.items():
        for j in range(i+1):out[j]+=v*comb(i,j)*s**(i-j)
    return {j:v for j,v in out.items() if v}
def ordinate(d,n):
    a={};b={0:1}
    for _ in range(n-1):a,b=b,add(mul(d,b),scale(-1,a))
    return b
def yi(d,n):
    a,b=0,1
    for _ in range(n-1):a,b=b,d*b-a
    return b
q=32;d={7:1,0:2};z={5:1,2:1,0:2}
y5=ordinate(d,5);c=ordinate(z,7);k=scale(2,y5);ky=mul({2:1},y5)
eta=shifted(add(c,scale(-1,ky)),256)
zeta=shifted(add(ky,k,scale(-1,c)),256)
big=shifted(add(ky,{0:-2*q**4}),256)
factor=shifted(add(y5,{0:-1}),256)
assert len(eta)==28 and all(v>0 for v in eta.values())
assert len(zeta)==29 and all(v>0 for v in zeta.values())
assert all(v>0 for v in big.values())
assert all(v>0 for v in factor.values())

# m=1 sample: verify the weighted projection fails for these scalar values.
a=256;Y=a*a//2;X=a**3;h=q-1;t=2*Y
k0=2*yi(X*t*t+2,5);c0=yi(t*(X+1)+2,7)
H=4*Y*(X+1)-1
rem=(h*X*(X-128)*(128*X+1))%H
assert X%q==0 and Y%(q**3)==0 and k0*Y<c0<k0*(Y+1) and c0>2*q**4
assert H==2199023386623 and rem==1648680914823 and rem!=0
print(json.dumps({'status':'PASS','eta_terms':len(eta),'eta_min':min(eta.values()),
 'zeta_terms':len(zeta),'zeta_min':min(zeta.values()),'sample_H':H,
 'sample_projection_remainder':rem,'scope':'ordinary scalar family; sample fails projection; no graph claim'},sort_keys=True))
