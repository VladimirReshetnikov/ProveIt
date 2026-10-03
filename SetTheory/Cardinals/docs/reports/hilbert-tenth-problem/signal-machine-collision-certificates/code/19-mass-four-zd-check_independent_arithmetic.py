#!/usr/bin/env python3
"""Independent finite tests of arithmetic identities, not a CA theorem verifier."""
import argparse
import hashlib
import itertools
import json
import math
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--proof', type=Path, required=True, help='The frozen PROOF.md to bind this run to')
PROOF = parser.parse_args().proof
EXPECTED = 'a2cc2bda22d1f3a68435f0f3f7b1c694278e6941f46cdd2ad3de69e512124511'

def require(v, s):
    if not v:
        raise RuntimeError(s)

def add(a, b): return tuple(x+y for x,y in zip(a,b))
def scale(k, a): return tuple(k*x for x in a)
def dot(a,b): return sum(x*y for x,y in zip(a,b))
def sub(a,b): return add(a,scale(-1,b))
def norm(a): return max(map(abs,a), default=0)

def offsets(shapes, radius):
    dim=len(shapes[0][0])
    return [(r,add(q,e)) for r,shape in enumerate(shapes)
            for q in shape for e in itertools.product(range(-radius,radius+1),repeat=dim)]

def exact_contact(shapes,D,v,radius):
    p=len(shapes)
    nz=next((i for i,z in enumerate(D) if z),None)
    candidates=[]
    for r,a in offsets(shapes,radius):
        if nz is None:
            if a==v: candidates.append((r,r,0,a))
            continue
        numer=v[nz]-a[nz]
        if numer%D[nz]: continue
        k=numer//D[nz]
        if k>=0 and add(a,scale(k,D))==v:
            candidates.append((r+p*k,r,k,a))
    if not candidates: return None
    t,r,k,a=min(candidates)
    seed=tuple(sorted(sub(q,a) for q in shapes[r]))
    return t,seed


def brute_contact(shapes,D,v,radius,periods):
    for t in range(len(shapes)*(periods+1)):
        k,r=divmod(t,len(shapes))
        if any(norm(sub(v,add(q,scale(k,D))))<=radius for q in shapes[r]):
            return t
    return None


def nonparallel_solution(D,E,b):
    n=len(D)
    for i in range(n):
        for j in range(i+1,n):
            det=D[i]*E[j]-D[j]*E[i]
            if not det: continue
            ka=b[i]*E[j]-b[j]*E[i]
            kb=D[i]*b[j]-D[j]*b[i]
            if ka%det or kb%det: return None
            k,l=ka//det,kb//det
            if k<0 or l<0 or add(scale(k,D),scale(l,E))!=b: return None
            return k,l
    raise ValueError('parallel')

require(hashlib.sha256(PROOF.read_bytes()).hexdigest()==EXPECTED,'proof hash mismatch')
counts={}

# Exact supports, phase ties, both drift signs, zero drift, and off-ray misses.
profiles=[(((0,0),(1,1)),((1,0),(1,1)),((0,1),(1,1))),
          (((0,0),),),
          (((-1,0),(0,1)),((0,0),(1,-1)))]
count=0
for shapes in profiles:
    for D in ((0,0),(1,0),(-2,0),(1,2),(2,-1)):
        for v in itertools.product(range(-8,9),repeat=2):
            exact=exact_contact(shapes,D,v,2)
            brute=brute_contact(shapes,D,v,2,30)
            require((exact[0] if exact else None)==brute,'contact formula mismatch')
            count+=1
counts['exact_contact_vs_direct_support']=count
# Bounding-box false positive: inside expanded box, but outside every actual box.
require(exact_contact((((0,0),(1,1)),),(0,0),(-2,3),2) is None,'support hole')
counts['bounding_box_false_positive_rejected']=1

# Same transverse vector and residue give identical contact seed and affine time.
count=0
for nu,lam in (((1,0),(1,0)),((2,1),(0,1)),((1,-2),(1,0)),((2,3),(-1,1))):
    require(dot(nu,lam)==1,'Bezout functional')
    for m in (-3,-2,-1,1,2,3):
        D=scale(m,nu)
        for shapes in profiles:
            offs=offsets(shapes,2)
            threshold=max(abs(dot(a,lam)) for _,a in offs)+10
            transverses={sub(a,scale(dot(a,lam),nu)) for _,a in offs}
            for z in transverses:
                for residue in range(abs(m)):
                    n=threshold+((residue-threshold)%abs(m))
                    if m<0: n=-n
                    n2=n+(abs(m) if m>0 else -abs(m))
                    first=exact_contact(shapes,D,add(scale(n,nu),z),2)
                    second=exact_contact(shapes,D,add(scale(n2,nu),z),2)
                    require((first is None)==(second is None),'residue eligibility')
                    if first:
                        require(first[1]==second[1],'contact seed changed')
                        require(second[0]-first[0]==len(shapes),'flight slope')
                    count+=1
counts['finite_control_seed_and_time_invariance']=count

# Exact Cramer enumeration, including coordinates outside the selected minor.
count=0
vectors=[v for v in itertools.product(range(-2,3),repeat=3) if any(v)]
for D in vectors[::7]:
    for E in vectors[::5]:
        if all(D[i]*E[j]==D[j]*E[i] for i in range(3) for j in range(3)): continue
        for k,l in itertools.product(range(4),repeat=2):
            b=add(scale(k,D),scale(l,E))
            require(nonparallel_solution(D,E,b)==(k,l),'Cramer recovery')
            count+=1
counts['nonparallel_solution_recovery']=count
P=10**6
D=(P,1); E=(-P-2,-1); b=(0,2)
require(nonparallel_solution(D,E,b)==(P+2,P),'large exceptional solution')
counts['large_exception_norm']=norm(scale(P+2,D))
require(nonparallel_solution((1,0,1),(0,1,1),(1,1,3)) is None,'unchecked remaining coordinate')
counts['inconsistent_remaining_coordinate_rejected']=1

# Small |lambda(v)| gives a finite launch list even with huge transverse scale.
count=0
for nu,lam in (((1,0),(1,0)),((1000,1),(0,1)),((2,3),(-1,1))):
    for m in (-3,-1,1,3):
        D=scale(m,nu)
        for a in itertools.product(range(-3,4),repeat=2):
            N=7
            ell=dot(a,lam)
            kmax=(N+abs(ell))//abs(m)
            for k in range(100):
                n=dot(add(a,scale(k,D)),lam)
                if abs(n)<=N: require(k<=kmax,'small launch escaped finite bound')
                count+=1
counts['small_launch_finiteness']=count

# Quadratic section time dominates a phase-uniform linear support bound.
count=0
for A,C,K0,K1,delta,window in itertools.product((1,2,5),(1,3),(0,4),(0,7),(-3,-1,1,2),(-5,0,11)):
    # For either drift sign, the outward magnitude bound is the same expression.
    f=lambda n: abs(delta)*(A*n*(n-1)//2+C*n)-K0-K1*n
    diff=lambda n: abs(delta)*(A*n+C)-K1
    n=0
    while not (f(n)>window and diff(n)>=0): n+=1
    for k in range(n,n+100):
        require(f(k)>window,'cutoff did not persist')
        require(diff(k)>=0,'cutoff derivative not outward')
        count+=1
counts['outward_cutoff_verified_indices']=count

result={'proof_sha256':EXPECTED,'scope':'Independent finite arithmetic tests only; not a general CA implementation or a formal proof.','counts':counts,'status':'passed'}
print(json.dumps(result,indent=2,sort_keys=True))
