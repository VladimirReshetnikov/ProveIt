#!/usr/bin/env python3
"""Exact finite icosahedron brightness certificates using only integer arithmetic.

Pair (a,b) represents a+b*phi, phi^2=phi+1.  No floating point, CAS,
nonstandard package, or empirical search is used in the verification.
"""
from itertools import combinations, product
from collections import Counter
import json

Z=(0,0); ONE=(1,0); PHI=(0,1); T=(-1,1)
def add(x,y): return x[0]+y[0],x[1]+y[1]
def neg(x): return -x[0],-x[1]
def sub(x,y): return add(x,neg(y))
def mul(x,y):
    a,b=x;c,d=y
    return a*c+b*d,a*d+b*c+b*d

def sign(x):
    a,b=x;d=2*a+b
    if b==0: return (d>0)-(d<0)
    if d>=0 and b>=0: return 1
    if d<=0 and b<=0: return -1
    delta=d*d-5*b*b
    assert delta!=0  # sqrt(5) is irrational; checked for the concrete inputs.
    return ((delta>0)-(delta<0)) * ((d>0)-(d<0))

def absq(x):return neg(x) if sign(x)<0 else x
def total(xs):
    s=Z
    for x in xs:s=add(s,x)
    return s

def vec(xs):return tuple((x,0) if isinstance(x,int) else x for x in xs)
def vadd(x,y):return tuple(add(a,b) for a,b in zip(x,y))
def dot(x,y):return total(mul(a,b) for a,b in zip(x,y))
def cross(x,y):
    return tuple(sub(mul(x[(i+1)%3],y[(i+2)%3]),mul(x[(i+2)%3],y[(i+1)%3])) for i in range(3))

g=[vec(x) for x in [(1,1,1),(1,1,-1),(1,-1,1),(-1,1,1),
 (0,T,PHI),(0,T,neg(PHI)),(T,PHI,0),(T,neg(PHI),0),
 (PHI,0,T),(PHI,0,neg(T))]]
def F(x):return total(absq(dot(a,x)) for a in g)

pairs=[]
for i,j in combinations(range(10),2):
    r=cross(g[i],g[j]);d=dot(r,r);f=F(r);a=absq(dot(g[i],g[j]))
    if a==ONE:
        kind='A';assert d==(8,0) and f==(4,12)
        assert mul(f,f)==mul(d,(20,30)) # 35+15sqrt5=20+30phi
    else:
        kind='B';assert a==(-1,2) and d==(4,0) and f==(4,8)
        assert mul(f,f)==mul(d,(20,32)) # 36+16sqrt5=20+32phi
    pairs.append({'i':i+1,'j':j+1,'type':kind,'cross':r,'norm_sq':d,'F':f})
assert Counter(r['type'] for r in pairs)=={'A':30,'B':15}

base=[vec(x) for x in [(1,1,1),(2,0,0),(0,2,0),(0,0,2)]]
options=[list(map(vec,x)) for x in [[(T,0,0),(0,PHI,0)],[(0,T,0),(0,0,PHI)],[(PHI,0,0),(0,0,T)]]]
coefficients=[]
for bi,inds in product(range(4),product(range(2),repeat=3)):
    c=base[bi]
    for k,j in enumerate(inds):c=vadd(c,options[k][j])
    q=dot(c,c)
    assert sign(sub((6,9),q))>=0
    coefficients.append({'base':bi,'choices':inds,'coefficient':c,'norm_sq':q})
assert len(coefficients)==32
assert sum(r['norm_sq']==(6,9) for r in coefficients)==4

determinants=Counter()
for i,j,k in combinations(range(10),3):
    d=absq(dot(g[i],cross(g[j],g[k])))
    assert d!=Z
    determinants[d]+=1
assert determinants=={(4,0):20,(-2,2):30,(2,0):30,(-2,4):10,(0,2):30}

print(json.dumps({'status':'all exact checks passed','ring':'a+b*phi, phi^2=phi+1',
 'minimum_pairs':pairs,'maximum_coefficients':coefficients,
 'triple_determinants':[{'abs_value':k,'count':v} for k,v in sorted(determinants.items())]},indent=2))
