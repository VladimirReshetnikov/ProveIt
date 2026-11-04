#!/usr/bin/env python3
"""Conditional n=5,r=9 scalar polynomial obstruction; exact arithmetic."""
import json,sys
from collections import defaultdict
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
def add(*ps):
    out=defaultdict(int)
    for p in ps:
        for m,c in p.items():out[m]+=c
    return {m:c for m,c in out.items() if c}
def scale(c,p):return {m:c*v for m,v in p.items() if c*v}
def mul(p,q):
    out=defaultdict(int)
    for (a,b),u in p.items():
        for (c,d),v in q.items():out[a+c,b+d]+=u*v
    return {m:c for m,c in out.items() if c}
def power(p,n):
    out={(0,0):1}
    for _ in range(n):out=mul(out,p)
    return out
def substitute(p,x,t):
    return add(*(scale(c,mul(power(x,i),power(t,j))) for (i,j),c in p.items()))
def ordinate(d,n):
    a={};b={(0,0):1}
    for _ in range(n-1):a,b=b,add(mul(d,b),scale(-1,a))
    return b
one={(0,0):1};x={(1,0):1};t={(0,1):1}
B=add(power(x,4),scale(8,power(x,3)),scale(28,power(x,2)),scale(56,x))
d=add(mul(x,power(t,2)),scale(2,one));z=add(mul(t,add(x,one)),scale(2,one))
y5=ordinate(d,5);c=ordinate(z,9);k=scale(2,y5);ky=mul(t,y5)
low=add(c,scale(-1,ky),scale(-1,k),
        scale(-1,mul(mul(power(x,4),power(t,8)),add(B,scale(68,one),scale(-1,t)))))
xs=add(scale(32,one),x)
lowcoeff=substitute(low,xs,add(one,t))
assert len(lowcoeff)==68 and all(v>0 for v in lowcoeff.values())
Bs=add(power(xs,4),scale(8,power(xs,3)),scale(28,power(xs,2)),scale(56,xs))
upcoeff=substitute(add(ky,scale(-1,c)),xs,add(Bs,scale(73,one),t))
assert len(upcoeff)==226 and all(v>0 for v in upcoeff.values())
print(json.dumps({'status':'PASS','lower_terms':len(lowcoeff),'lower_min':min(lowcoeff.values()),
 'upper_terms':len(upcoeff),'upper_min':min(upcoeff.values()),
 'scope':'formal polynomial coefficients; conditional scalar only; no graph or Lean binding'},sort_keys=True))
