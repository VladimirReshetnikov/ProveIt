#!/usr/bin/env python3
"""Exact scalar endpoint certificates for n=6,r=9."""
import json,sys
from collections import defaultdict
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
def add(*ps):
    out=defaultdict(int)
    for p in ps:
        for m,c in p.items():out[m]+=c
    return {m:c for m,c in out.items() if c}
def sc(c,p):return {m:c*v for m,v in p.items() if c*v}
def mul(p,q):
    out=defaultdict(int)
    for (a,b),u in p.items():
        for (c,d),v in q.items():out[a+c,b+d]+=u*v
    return {m:c for m,c in out.items() if c}
def pw(p,n):
    out={(0,0):1}
    for _ in range(n):out=mul(out,p)
    return out
def subst(p,x,t):
    return add(*(sc(c,mul(pw(x,i),pw(t,j))) for (i,j),c in p.items()))
def ordinate(d,n):
    a={};b={(0,0):1}
    for _ in range(n-1):a,b=b,add(mul(d,b),sc(-1,a))
    return b
one={(0,0):1};x={(1,0):1};t={(0,1):1}
d=add(mul(x,pw(t,2)),sc(2,one));z=add(mul(t,add(x,one)),sc(2,one))
y6=ordinate(d,6);c=ordinate(z,9);k=sc(2,y6);ky=mul(t,y6)

# X<=t-3: X=32+u, t=X+3+w. Then ky-c>0.
xs=add(sc(32,one),x);ts=add(xs,sc(3,one),t)
lower=subst(add(ky,sc(-1,c)),xs,ts)
assert len(lower)==137 and all(v>0 for v in lower.values())

# X>=t-2: t=2+u, X=t-2+w=u+w. Then c-ky-k>0.
ts=add(sc(2,one),x);xs=add(x,t)
upper=subst(add(c,sc(-1,ky),sc(-1,k)),xs,ts)
assert len(upper)==115 and all(v>0 for v in upper.values())
print(json.dumps({'status':'PASS','lower_terms':len(lower),'lower_min':min(lower.values()),
 'upper_terms':len(upper),'upper_min':min(upper.values()),
 'scope':'exact polynomial certificates; conditional scalar only; no graph or Lean binding'},sort_keys=True))
