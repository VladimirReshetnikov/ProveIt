#!/usr/bin/env python3
"""Independent exact checks of the two binary-profile witnesses.
Standard library only. Polynomial coefficient arrays have increasing degree.
"""
import json, math
from fractions import Fraction

def add(a,b):
    c=[0]*max(len(a),len(b))
    for k,x in enumerate(a):c[k]+=x
    for k,x in enumerate(b):c[k]+=x
    return c

def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return c

def der(a):return [k*a[k] for k in range(1,len(a))]
def shift_one(a):return [sum(x*math.comb(i,k) for i,x in enumerate(a) if i>=k) for k in range(len(a))]
def v2(x):
    n=0
    while x%2==0:x//=2;n+=1
    return n

def require(ok,detail):
    if not ok:raise AssertionError(detail)

cases=[dict(t=6,F=[65501,128,-140,0,70,0,-28,0,5],
            shifted=[65536,0,0,0,0,112,112,40,5],p=3,
            U=[-1,0,0,1,0,0,1],V=[0,1,1,1,1,1,0,1],
            vertices=[(0,16),(5,4),(8,0)],depth=Fraction(4,3)),
       dict(t=7,F=[65571,-192,420,-448,210,0,-28,0,3],
            shifted=[65536,0,0,0,0,0,56,24,3],p=5,
            U=[0,0,0,0,0,1],V=[2,0,1,0,-2,0,-2],
            vertices=[(0,16),(6,3),(8,0)],depth=Fraction(3,2))]
output=[]
for c in cases:
    F=c['F'];shift=shift_one(F)
    require(shift==c['shifted'],'binomial expansion')
    require(sum(x!=0 for x in F)==c['t'],'support cardinality')
    bez=add(mul(c['U'],F),mul(c['V'],der(F)))
    require([x%c['p'] for x in bez]==[1]+[0]*(len(bez)-1),'Bezout squarefree certificate')
    pts=[(k,v2(a)) for k,a in enumerate(shift) if a]
    hull=[]
    for pt in pts:
        while len(hull)>=2:
            a,b=hull[-2:]
            if Fraction(b[1]-a[1],b[0]-a[0])>=Fraction(pt[1]-b[1],pt[0]-b[0]):hull.pop()
            else:break
        hull.append(pt)
    require(hull==c['vertices'],'Newton polygon vertices')
    slopes=[Fraction(b[1]-a[1],b[0]-a[0]) for a,b in zip(hull,hull[1:])]
    require(min(-s for s in slopes)==c['depth'],'minimum root depth')
    weights=[(v2(a)+c['depth']*k,k) for k,a in enumerate(shift) if a]
    m=min(w for w,k in weights)
    count=max(k for w,k in weights if w==m)
    require(count==8,'closed endpoint root count')
    output.append(dict(terms=c['t'],support=[k for k,x in enumerate(F) if x],
                       coefficients=[x for x in F if x],shifted_coefficients=shift,
                       newton_vertices=hull,
                       root_groups=[dict(multiplicity=b[0]-a[0],depth=str(-s))
                                    for a,b,s in zip(hull,hull[1:],slopes)],
                       squarefree_prime=c['p'],bezout_verified=True,endpoint_root_count=count))
print(json.dumps(dict(all_checks_pass=True,witnesses=output),indent=2))
