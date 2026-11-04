#!/usr/bin/env python3
"""Exact coefficient certificates for conditional n=4,r=7 scalar exclusion."""
import json
import sys
from collections import defaultdict

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')

def add(*ps):
    out = defaultdict(int)
    for p in ps:
        for mon, c in p.items(): out[mon] += c
    return {m:c for m,c in out.items() if c}

def scale(c,p): return {m:c*v for m,v in p.items() if c*v}

def mul(p,q):
    out = defaultdict(int)
    for (a,b),u in p.items():
        for (c,d),v in q.items(): out[a+c,b+d] += u*v
    return {m:c for m,c in out.items() if c}

def power(p,n):
    out = {(0,0):1}
    for _ in range(n): out = mul(out,p)
    return out

def substitute(p,x,t):
    return add(*(scale(c,mul(power(x,i),power(t,j))) for (i,j),c in p.items()))

one={(0,0):1}; x={(1,0):1}; t={(0,1):1}
B=add(power(x,3),scale(6,power(x,2)),scale(15,x))
z=add(mul(t,add(x,one)),scale(2,one))
c=add(power(z,6),scale(-5,power(z,4)),scale(6,power(z,2)),scale(-1,one))
ky=add(mul(power(x,3),power(t,7)),scale(6,mul(power(x,2),power(t,5))),
       scale(10,mul(x,power(t,3))),scale(4,t))
k=add(scale(2,mul(power(x,3),power(t,6))),scale(12,mul(power(x,2),power(t,4))),
      scale(20,mul(x,power(t,2))),scale(8,one))

# c-kY-k = x³t⁶(B+18-t) + P. Substitute x=32+u,t=1+v.
lower=add(c,scale(-1,ky),scale(-1,k),
          scale(-1,mul(mul(power(x,3),power(t,6)),add(B,scale(18,one),scale(-1,t)))))
lower_coeff=substitute(lower,add(scale(32,one),x),add(one,t))
assert len(lower_coeff)==39 and all(v>0 for v in lower_coeff.values())
assert lower_coeff[(0,0)]==539298029 and min(lower_coeff.values())==12

# kY-c is positive when x=32+u,t=B+22+w.
xshift=add(scale(32,one),x)
bshift=add(power(xshift,3),scale(6,power(xshift,2)),scale(15,xshift))
upper_coeff=substitute(add(ky,scale(-1,c)),xshift,add(bshift,scale(22,one),t))
assert len(upper_coeff)==113 and all(v>0 for v in upper_coeff.values())

print(json.dumps({'status':'PASS','lower_terms':len(lower_coeff),
 'lower_min_coefficient':min(lower_coeff.values()),'lower_constant':lower_coeff[(0,0)],
 'upper_terms':len(upper_coeff),'upper_min_coefficient':min(upper_coeff.values()),
 'scope':'formal integer polynomial coefficients; conditional scalar arithmetic only; no Lean or graph binding'},sort_keys=True))
