#!/usr/bin/env python3
"""Independent finite checks of the proof's arithmetic, not a CA theorem test."""
from itertools import product
from math import gcd
from functools import reduce
from random import Random
from pathlib import Path
import json

rng=Random(20261003)
counts={}
def check(v,msg):
    if not v: raise RuntimeError(msg)
def add(a,b): return tuple(x+y for x,y in zip(a,b))
def sub(a,b): return tuple(x-y for x,y in zip(a,b))
def mul(k,a): return tuple(k*x for x in a)
def norm(a): return max(map(abs,a),default=0)
def egcd(a,b):
    if b==0: return abs(a), (1 if a>=0 else -1), 0
    g,x,y=egcd(b,a%b)
    return g,y,x-(a//b)*y
def primitive(D):
    g=reduce(gcd,map(abs,D)); v=tuple(x//g for x in D)
    if next(x for x in v if x)<0: v=mul(-1,v); g=-g
    coeff=[0]*len(v); h=0
    for i,a in enumerate(v):
        nh,u,w=egcd(h,a); coeff=[u*x for x in coeff]; coeff[i]+=w; h=nh
    check(h==1,'primitive bezout gcd')
    return v,g,tuple(coeff)
def dot(a,b): return sum(x*y for x,y in zip(a,b))
def ray_k(v,a,D):
    i=next(i for i,x in enumerate(D) if x)
    z=v[i]-a[i]
    if z%D[i]: return None
    k=z//D[i]
    return k if k>=0 and add(a,mul(k,D))==v else None

def candidates(phases,D,radius):
    dim=len(D)
    return [(r,add(pt,z)) for r,pts in enumerate(phases) for pt in pts
            for z in product(range(-radius,radius+1),repeat=dim)]
def first_ray(v,D,p,cand):
    hits=[]
    for r,a in cand:
        k=ray_k(v,a,D)
        if k is not None: hits.append((r+p*k,r,k,a))
    return min(hits) if hits else None
def first_brute(v,D,phases,radius,limit):
    p=len(phases)
    for t in range(limit+1):
        k,r=divmod(t,p)
        if any(norm(sub(v,add(pt,mul(k,D))))<=radius for pt in phases[r]): return t
    return None

# Exact phase/support contact versus time-step brute force in d=1,2,3.
counts['contact_profiles']=0; counts['huge_ray_shifts']=0; counts['ties']=0
for case in range(600):
    dim=1+case%3; p=rng.randint(1,6)
    D=tuple(rng.randint(-3,3) for _ in range(dim))
    if not any(D): D=(1,)+(0,)*(dim-1)
    phases=[list({tuple(rng.randint(-4,4) for _ in range(dim)) for _ in range(2)}) for _ in range(p)]
    cand=candidates(phases,D,2)
    if case%2:
        _,a=rng.choice(cand); v=add(a,mul(rng.randrange(30),D))
    else: v=tuple(rng.randint(-50,50) for _ in range(dim))
    h=first_ray(v,D,p,cand); hb=first_brute(v,D,phases,2,220)
    check((h[0] if h and h[0]<=220 else None)==hb,('first_contact',case,h,hb))
    counts['contact_profiles']+=1
    nu,m,lam=primitive(D)
    check(dot(lam,nu)==1 and mul(m,nu)==D,'bezout decomposition')
    a=rng.choice(cand)[1]
    K0=10+max(abs(dot(lam,b)) for _,b in cand)
    v=add(a,mul(K0,D)); h=first_ray(v,D,p,cand)
    shift=10**60+case
    hv=first_ray(add(v,mul(shift,D)),D,p,cand)
    check(h is not None and hv is not None and hv[0]==h[0]+p*shift,'affine huge clock')
    check(hv[1]==h[1] and hv[3]==h[3],'huge seed phase')
    n=dot(lam,v); z=sub(v,mul(n,nu))
    check(dot(lam,z)==0 and add(mul(n,nu),z)==v,'unique transverse decomposition')
    counts['huge_ray_shifts']+=1
    if h:
        ties=[(r,a) for r,a in cand if ray_k(v,a,D) is not None and r+p*ray_k(v,a,D)==h[0]]
        if len(ties)>1: counts['ties']+=1

# Two finite-phase walkers: common-period interval calculation versus direct trace.
def earliest_inequalities(offset,vel,radius):
    lo,hi=0,None
    for a,b in zip(offset,vel):
        if b==0:
            if abs(a)>radius:return None
        else:
            L,U=-radius-a,radius-a
            if b<0: L,U,b=-U,-L,-b
            l=-((-L)//b); u=U//b
            lo=max(lo,l); hi=u if hi is None else min(hi,u)
    return lo if hi is None or lo<=hi else None
counts['two_packet_clocks']=0
for case in range(500):
    dim=1+case%5;p=rng.randint(1,6);q=rng.randint(1,6); common=p*q//gcd(p,q)
    D=tuple(rng.randint(-3,3) for _ in range(dim)); E=tuple(rng.randint(-3,3) for _ in range(dim))
    P=[tuple(rng.randint(-6,6) for _ in range(dim)) for _ in range(p)]
    Q=[tuple(rng.randint(-6,6) for _ in range(dim)) for _ in range(q)]
    vel=sub(mul(common//p,D),mul(common//q,E)); got=[]
    for r in range(common):
        off=sub(add(P[r%p],mul(r//p,D)),add(Q[r%q],mul(r//q,E)))
        k=earliest_inequalities(off,vel,2)
        if k is not None:got.append(r+common*k)
    exact=min(got) if got else None
    brute=None
    for t in range(801):
        if norm(sub(add(P[t%p],mul(t//p,D)),add(Q[t%q],mul(t//q,E))))<=2:
            brute=t;break
    check((exact if exact is not None and exact<=800 else None)==brute,('two_clocks',case,exact,brute))
    counts['two_packet_clocks']+=1

# Nonparallel switch equation: unique rational solution with all coordinates checked.
def solve_switch(D,E,H):
    pair=next(((i,j) for i in range(len(D)) for j in range(i+1,len(D)) if D[i]*E[j]-D[j]*E[i]),None)
    if pair is None:return None
    i,j=pair;det=D[i]*E[j]-D[j]*E[i]
    nk=H[i]*E[j]-H[j]*E[i];nl=D[i]*H[j]-D[j]*H[i]
    if nk%det or nl%det:return None
    k,l=nk//det,nl//det
    return (k,l) if k>=0 and l>=0 and add(mul(k,D),mul(l,E))==H else None
counts['nonparallel_switches']=0
for case in range(500):
    dim=2+case%5
    while True:
        D=tuple(rng.randint(-5,5) for _ in range(dim));E=tuple(rng.randint(-5,5) for _ in range(dim))
        if any(D[i]*E[j]-D[j]*E[i] for i in range(dim) for j in range(i+1,dim)):break
    if case%2:
        k,l=rng.randrange(16),rng.randrange(16);H=add(mul(k,D),mul(l,E))
    else:H=tuple(rng.randint(-20,20) for _ in range(dim))
    got=solve_switch(D,E,H)
    brute=[(k,l) for k in range(41) for l in range(41) if add(mul(k,D),mul(l,E))==H]
    check(len(brute)<=1,'nonparallel uniqueness')
    check(([got] if got and max(got)<=40 else [])==brute,('cramer',case,got,brute))
    counts['nonparallel_switches']+=1
M=10**6
D=(M,1); E=(-M-1,-1); H=(0,1)
check(solve_switch(D,E,H)==(M+1,M),'near-parallel large exceptional switch')
counts['near_parallel_exception_norm']=norm(mul(M+1,D))

# Expanded bounding boxes have holes in dimension two.
pts=[(0,0),(1,1)]; target=(-2,3)
check(all(min(p[i] for p in pts)-2<=target[i]<=max(p[i] for p in pts)+2 for i in range(2)),'hull membership')
check(not any(norm(sub(target,p))<=2 for p in pts),'hull false positive')
counts['hull_hole_regression']=1

# Coordinatewise two-unit intersection bound in d up to four.
counts['dimer_intersection_boxes']=0
for dim in range(1,5):
    for S in (1,2):
        for v in product(range(-S,S+1),repeat=dim):
            if not any(v):continue
            lows=[max(0,x)-S for x in v];highs=[min(0,x)+S for x in v]
            check(all(lo<=0<=hi and lo<=x<=hi and hi-lo<=2*S for lo,hi,x in zip(lows,highs,v)),'intersection bound')
            counts['dimer_intersection_boxes']+=1

# Original-frame escape cutoff: quadratic time dominates arbitrary linear spatial drift.
counts['frame_cutoffs']=0
for case in range(1000):
    A=rng.randrange(1,100);C=rng.randrange(1,100);T0=rng.randrange(1000)
    delta=rng.randrange(1,10);K0=rng.randrange(10**6);K1=rng.randrange(10**6);window=rng.randrange(-1000,1000)
    def f(n):return delta*(T0+A*n*(n-1)//2+C*n)-K0-K1*n-window
    # f is discretely convex; require positive and nonnegative forward difference.
    n=1
    while f(n)<=0 or f(n+1)<f(n):n*=2
    check(f(n)>0 and f(n+1)>=f(n),'cutoff selection')
    for h in (0,1,2,10,10**20):check(f(n+h)>0,'uniform later cutoff')
    counts['frame_cutoffs']+=1

receipt={'status':'PASS','seed':20261003,'checks':counts,'scope':'Finite arithmetic/formula audit only; no general CA compiler or formal proof'}
path=Path(__file__).with_name('arithmetic-results.json');path.write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
