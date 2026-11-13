#!/usr/bin/env python3
"""Verify the positive-definite binary-form identity over the integer polynomial ring."""
import json,sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
def add(p,q,sign=1):
 r=dict(p)
 for m,c in q.items():r[m]=r.get(m,0)+sign*c
 return {m:c for m,c in r.items() if c}
def mul(p,q):
 r={}
 for a,x in p.items():
  for b,y in q.items():
   m=tuple(sorted(a+b));r[m]=r.get(m,0)+x*y
 return {m:c for m,c in r.items() if c}
def k(n):return {():n} if n else {}
a,b,c,r,s=({(x,):1} for x in ('a','b','c','r','s'))
q=add(add(mul(a,mul(r,r)),mul(b,mul(r,s))),mul(c,mul(s,s)))
left=mul(mul(k(4),a),q)
w=add(mul(mul(k(2),a),r),mul(b,s));disc=add(mul(mul(k(4),a),c),mul(b,b),-1)
right=add(mul(w,w),mul(disc,mul(s,s)))
if left!=right:raise RuntimeError('certificate identity failed')
forms=[(aa,bb,cc) for aa in range(1,4) for cc in range(1,4) for bb in range(-4,5) if 4*aa*cc>bb*bb]
assert len(forms)==61 and all(aa>0 and 4*aa*cc-bb*bb>0 for aa,bb,cc in forms)
print(json.dumps({'status':'PASS_EXACT_INTEGER_POLYNOMIAL_IDENTITY','forms':len(forms),'identity':'4*a*(a*r^2+b*r*s+c*s^2)=(2*a*r+b*s)^2+(4*a*c-b^2)*s^2','implication':'for integer r,s, a>0 and 4*a*c-b^2>0 imply Q>=0 and Q=0 iff r=s=0'},sort_keys=True))
