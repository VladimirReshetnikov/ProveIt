#!/usr/bin/env python3
"""Independent bounded carrier enumeration and first-index interval search."""
import hashlib
import json
import math
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B without optimization')
root=Path(__file__).resolve().parents[2]
packet=root/'research/p64-qcube72-windowed-first-index-screen'
graph=root/'research/p64-qcube72-free-main-candidate/graph.json'
pins={packet/'check.py':'1f9a2333b6629415336d5ea3dfab534e60090d8c81c455665e0c4f446c45dad1',
      packet/'result.json':'8630a705f39eb022225d8793dd140671327e29aab97718b2d350e5ba67225d91',
      graph:'875a9d0972c350e6858e25b68f2dc794b1f330e61f29cd52a5853ece90b24806'}
for p,h in pins.items():
    if hashlib.sha256(p.read_bytes()).hexdigest()!=h: raise RuntimeError('pin mismatch '+str(p))

# Cancel gcd(H,U) in the exact projection divisibility. This enumerates the
# same domain using a different necessary-filter expression and loop order.
survivors=[]
for R in (43,47):
    power=2**R
    for w in range(1,10001):
        X=3*w
        for s in range(1,301):
            Y=27*s; U=Y*Y; H=4*(X+1)*Y+3
            if (power-X) % (H//math.gcd(H,U))==0:
                survivors.append((R,s,w))
if len(survivors)!=4 or sorted(survivors)!=[(43,57,24),(47,8,6351),(47,46,48),(47,84,24)]:
    raise RuntimeError('unexpected projected survivors')

def first_coord(P,j):
    # First Pell coefficient from an independent left-to-right pair power.
    a,b=1,0; D=P*(P+1); x,y=2*P+1,2
    for ch in bin(j)[2:]:
        a,b=a*a+D*b*b,2*a*b
        if ch=='1':a,b=a*x+D*b*y,a*y+b*x
    return b

for R,s,w in survivors:
    Y=27*s; U=Y*Y; X=3*w; a=(X+1)*Y; H=4*a+3; D=(a+2)**2-1
    g,c=1,0
    for _ in range(R):g,c=(a+2)*g+D*c,g+(a+2)*c
    if g*g-D*c*c!=1: raise RuntimeError('main norm')
    numerator=U*(g-X-a*c); h,rem=divmod(numerator,H)
    if rem or h<=0: raise RuntimeError('carrier is not a positive integer')
    # The sequence k(j) is strictly increasing. Binary search the first j
    # for which c<(Y+1)k, then test the other strict inequality Yk<c.
    lo,hi=1,R+1; P=X*U
    while lo<hi:
        mid=(lo+hi)//2
        if mid<=R and c<(Y+1)*first_coord(P,mid):hi=mid
        else:lo=mid+1
    if lo<=R and Y*first_coord(P,lo)<c: raise RuntimeError('first-index scale survivor')

source=json.loads((packet/'result.json').read_text())
if sorted(map(tuple,source['projection_candidates']))!=sorted(survivors) or source['scale_candidates'] or source['nonpositive_h']:
    raise RuntimeError('author result disagreement')
print(json.dumps({'status':'PASS','projection_candidates':sorted(survivors),'checked_triples':6000000,
 'scale_candidates':[],'scope':'Finite noncompact carrier projection and first index 1..R only; no full graph or congruence result.'},sort_keys=True))
