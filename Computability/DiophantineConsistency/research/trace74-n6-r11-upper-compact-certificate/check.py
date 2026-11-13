#!/usr/bin/env python3
"""Univariate coefficient certificates for a factored n6/r11 upper bound."""
import json,sys
from collections import defaultdict
from math import comb
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
def add(*ps):
    r=defaultdict(int)
    for p in ps:
        for i,v in p.items():r[i]+=v
    return {i:v for i,v in r.items() if v}
def sc(c,p):return {i:c*v for i,v in p.items() if c*v}
def mul(p,q):
    r=defaultdict(int)
    for i,v in p.items():
        for j,w in q.items():r[i+j]+=v*w
    return {i:v for i,v in r.items() if v}
def pw(p,n):
    r={0:1}
    for _ in range(n):r=mul(r,p)
    return r
def shift(p,s):
    r=defaultdict(int)
    for i,v in p.items():
        for j in range(i+1):r[j]+=v*comb(i,j)*s**(i-j)
    return {j:v for j,v in r.items() if v}
def ordinate(d,n):
    a={};b={0:1}
    for _ in range(n-1):a,b=b,add(mul(d,b),sc(-1,a))
    return b
x={1:1};one={0:1};xp1=add(x,one)
ys=ordinate(add(x,{0:2}),6)
assert ys=={5:1,4:10,3:36,2:56,1:35,0:6}
yc=ordinate(add(x,{0:2}),11)
coeff=[11,220,1287,3432,5005,4368,2380,816,171,20,1]
assert yc=={j:v for j,v in enumerate(coeff)}
T=add(pw(x,5),sc(10,pw(x,4)),sc(45,pw(x,3)),sc(120,pw(x,2)),sc(210,x),{0:260})
C=add(*(sc(c,pw(xp1,j)) for j,c in enumerate(coeff[:-1])))
D=add(mul(pw(x,5),T),sc(-1,pw(xp1,10)))
P=add(mul(D,T),sc(-1,C))
ds=shift(D,32);ps=shift(P,32)
assert len(ds)==6 and all(v>0 for v in ds.values())
assert len(ps)==11 and all(v>0 for v in ps.values())
print(json.dumps({'status':'PASS','D_terms':len(ds),'D_min':min(ds.values()),
 'P_terms':len(ps),'P_min':min(ps.values()),'y11_coefficients':coeff,
 'scope':'conditional factored scalar bound; exact identities only; no Lean or graph binding'},sort_keys=True))
