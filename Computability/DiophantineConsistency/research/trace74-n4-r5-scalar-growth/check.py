#!/usr/bin/env python3
"""Exact polynomial identities supporting a conditional scalar size bound."""
import json
import sys
from math import comb

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')

def add(a,b):
    r=dict(a)
    for k,v in b.items(): r[k]=r.get(k,0)+v
    return {k:v for k,v in r.items() if v}
def scale(n,a): return {k:n*v for k,v in a.items() if n*v}
def mul(a,b):
    r={}
    for i,u in a.items():
        for j,v in b.items(): r[i+j]=r.get(i+j,0)+u*v
    return {k:v for k,v in r.items() if v}
def power(a,n):
    r={0:1}
    for _ in range(n): r=mul(r,a)
    return r
def shift(a,c):
    return {j:sum(v*comb(i,j)*c**(i-j) for i,v in a.items() if i>=j)
            for j in range(max(a)+1)}

# In any ordered ring, x>=32 makes 2x^4-(x+2)^4 nonnegative:
# every coefficient after x=32+u is positive.
x={1:1};one={0:1}
quartic=add(scale(2,power(x,4)),scale(-1,power(add(x,{0:2}),4)))
shifted=shift(quartic,32)
assert len(shifted)==5 and all(v>0 for v in shifted.values())

# The coefficient needed at q>=32 is exact, not a numerical approximation.
# 16q³−16368q = 16q(q²−1024)+16q.
q={1:1}
lhs=add(scale(16,power(q,3)),scale(-16368,q))
rhs=add(scale(16,mul(q,add(power(q,2),{0:-1024}))),scale(16,q))
assert lhs==rhs

print(json.dumps({'status':'PASS','quartic_shift_coefficients':shifted,
                  'q_coefficient_identity':True,
                  'scope':'integer polynomial certificates; conditional scalar growth only; no Lean or graph binding'},sort_keys=True))
