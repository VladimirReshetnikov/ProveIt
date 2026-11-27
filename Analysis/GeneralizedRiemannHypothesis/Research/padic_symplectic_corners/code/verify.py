#!/usr/bin/env python3
"""Exact finite-ring checks for p-adic symplectic corner laws.

This is an independent exhaustive enumeration of symplectic pairs, not a
simulation. It checks the complete corner law, not only its determinant.
Run: python3 code/verify.py  (NumPy required for exhaustive enumeration).
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path
import time

import numpy as np


@dataclass
class Ring:
    name: str
    q: int
    e: int
    add: np.ndarray
    mul: np.ndarray
    neg: np.ndarray
    valuation: np.ndarray

    @property
    def size(self):
        return len(self.neg)


def make_ring(name, q, e, add, mul, valuation):
    m = q**e
    at = np.array([[add(a, b) for b in range(m)] for a in range(m)], dtype=np.int64)
    mt = np.array([[mul(a, b) for b in range(m)] for a in range(m)], dtype=np.int64)
    ng = np.array([next(b for b in range(m) if at[a,b] == 0) for a in range(m)])
    # Sanity checks of the independently specified finite rings.
    assert np.array_equal(at, at.T) and np.array_equal(mt, mt.T)
    assert np.array_equal(mt[1], np.arange(m))
    for a,b,c in product(range(m), repeat=3):
        assert at[at[a,b],c] == at[a,at[b,c]]
        assert mt[mt[a,b],c] == mt[a,mt[b,c]]
        assert mt[a,at[b,c]] == at[mt[a,b],mt[a,c]]
    return Ring(name,q,e,at,mt,ng,np.array([valuation(a) for a in range(m)]))


def integer_ring(p,e):
    m=p**e
    def valuation(a):
        if not a: return e
        v=0
        while a%p==0:
            a//=p; v+=1
        return v
    return make_ring(f"Z/{m}Z",p,e,lambda a,b:(a+b)%m,lambda a,b:a*b%m,valuation)


def binary_truncated_ring(e):
    def mul(a,b):
        c=0
        for j in range(e):
            if b>>j&1: c ^= a<<j
        return c&((1<<e)-1)
    def valuation(a):
        return e if not a else (a&-a).bit_length()-1
    return make_ring(f"F2[t]/(t^{e})",2,e,lambda a,b:a^b,mul,valuation)


def field4():
    def mul(a,b):
        c=0
        for j in range(2):
            if b>>j&1: c^=a<<j
        if c&4: c^=7 # t^2+t+1
        return c
    return make_ring("F4",4,1,lambda a,b:a^b,mul,lambda a:0 if a else 1)


def ramified_binary_ring():
    # Z_2[sqrt(2)]/(sqrt(2)^3): a+b*pi, a mod 4 and b mod 2.
    def add(x,y): return ((x%4+y%4)%4)+4*((x//4+y//4)%2)
    def mul(x,y):
        a,b=x%4,x//4; c,d=y%4,y//4
        return ((a*c+2*b*d)%4)+4*((a*d+b*c)%2)
    def valuation(x):
        a,b=x%4,x//4
        return 0 if a%2 else (1 if b else (2 if a else 3))
    return make_ring("Z2[sqrt(2)]/(sqrt(2)^3)",2,3,add,mul,valuation)


def density(q,g,e,v):
    """Likelihood at precision e and truncated valuation v of 1-det A."""
    n=2*g-2
    b=F(1,q**(n-1))
    denominator=1-F(1,q**(n+2))
    if v<e:
        numerator=(1-F(1,q**n))*sum((b**r for r in range(v+1)),F(0))
    else:
        numerator=(1-F(1,q**n))*sum((b**r for r in range(e)),F(0))+b**e
    return numerator/denominator


def formula_tv(q,g):
    return (1-F(1,q)+F(1,q**3))*F(q*q-1,q**(2*g)-1)


def formula_lift_tv(q,g,k=1):
    return F(q-1,q)*F(q*q-1,(q**(2*g)-1)*q**((2*g-2)*k))


def defect_masses(q,e):
    b=F(1,q)-F(1,q**3)
    return [1-b]+[b*(1-F(1,q))*F(1,q**(r-1)) for r in range(1,e)]+[b*F(1,q**(e-1))]


def exact_formula_checks():
    count=0
    for q,g,e in product((2,3,4,5,8,9,16,27),range(2,13),range(1,9)):
        masses=defect_masses(q,e)
        hs=[density(q,g,e,v) for v in range(e+1)]
        assert sum(masses)==1
        assert sum(p*h for p,h in zip(masses,hs))==1
        assert hs[0]<1 and all(h>1 for h in hs[1:])
        tv=sum(p*abs(h-1) for p,h in zip(masses,hs))/2
        assert tv==formula_tv(q,g)
        lift=sum(p*abs(h-density(q,g,1,min(v,1))) for v,(p,h) in enumerate(zip(masses,hs)))/2
        assert lift==(F(0) if e==1 else formula_lift_tv(q,g))
        for k in range(1,e):
            lift_k=sum(p*abs(h-density(q,g,k,min(v,k))) for v,(p,h) in enumerate(zip(masses,hs)))/2
            assert lift_k==formula_lift_tv(q,g,k)
        assert all(h<=F(8,5) for h in hs)
        count+=1
    for q in (2,3,4,5,8,9,16,27):
        u=(1-F(1,q))*(1-F(1,q*q))
        diagonal=u/(1-F(1,q**4))
        offdiag=(1-F(1,q*q))**2*F(1,q)/((1-F(1,q))*(1-F(1,q**4)))
        assert diagonal+offdiag==1
    return {"parameter_triples":count,"assertions":"normalization, sign, exact TV, every lower-precision lift TV, Smith normalization, 8/5 rejection envelope", "passed":True}


def enumerate_pairs(ring,g):
    """Enumerate all (v,w) with <v,w>=1 in R^(2g), using J=diag(J2,...)."""
    start=time.monotonic()
    m=ring.size
    vectors=np.array(list(product(range(m),repeat=2*g)),dtype=np.int64)
    counts=np.zeros(m**4,dtype=np.int64)
    w=vectors
    for v in vectors:
        pairing=np.zeros(len(w),dtype=np.int64)
        for j in range(g):
            z=ring.add[ring.mul[v[2*j],w[:,2*j+1]],ring.neg[ring.mul[v[2*j+1],w[:,2*j]]]]
            pairing=ring.add[pairing,z]
        ww=w[pairing==1]
        # A=(v_0,w_0;v_1,w_1); multiplication on left by J2 gives compression.
        idx=((v[0]*m+ww[:,0])*m+v[1])*m+ww[:,1]
        np.add.at(counts,idx,1)
    total=int(counts.sum())
    assert total==F(m**(4*g-1))*(1-F(1,ring.q**(2*g)))
    tv=F(0)
    lift=F(0)
    lift_by_k={k:F(0) for k in range(1,ring.e)}
    defect_counts=[0]*(ring.e+1)
    for idx,a in enumerate(product(range(m),repeat=4)):
        det=ring.add[ring.mul[a[0],a[3]],ring.neg[ring.mul[a[1],a[2]]]]
        defect=ring.add[1,ring.neg[det]]
        v=int(ring.valuation[defect])
        h=density(ring.q,g,ring.e,v)
        actual=F(int(counts[idx]),total)
        assert actual==h/F(m**4), (ring.name,g,a,actual,h)
        tv+=abs(actual-F(1,m**4))/2
        lift+=abs(actual-density(ring.q,g,1,min(v,1))/F(m**4))/2
        for k in lift_by_k:
            lift_by_k[k]+=abs(actual-density(ring.q,g,k,min(v,k))/F(m**4))/2
        defect_counts[v]+=int(counts[idx])
    assert tv==formula_tv(ring.q,g)
    assert lift==(0 if ring.e==1 else formula_lift_tv(ring.q,g))
    assert all(value==formula_lift_tv(ring.q,g,k) for k,value in lift_by_k.items())
    return {"ring":ring.name,"q":ring.q,"precision":ring.e,"g":g,
            "ordered_pairs_examined":len(vectors)**2,"symplectic_pairs":total,
            "corner_matrices_compared":m**4,"tv":str(tv),"tv_decimal":float(tv),
            "tv_from_uniform_digit_lift":str(lift),"defect_counts":defect_counts,
            "tv_from_each_lower_precision":{str(k):str(value) for k,value in lift_by_k.items()},
            "seconds":round(time.monotonic()-start,3),"passed":True}


def rank_mod2(rows):
    pivots={}
    for x in rows:
        while x:
            k=x.bit_length()-1
            if k in pivots: x^=pivots[k]
            else: pivots[k]=x;break
    return len(pivots)


def subspaces_mod2(dim):
    # Each subspace is represented canonically by its complete sorted vector set.
    seen={tuple([0])}
    queue=[(tuple([0]),())]
    out=[]
    while queue:
        points,basis=queue.pop()
        out.append((points,basis))
        for v in range(1,1<<dim):
            if v in points: continue
            span=tuple(sorted(set(points)|{x^v for x in points}))
            if span not in seen:
                seen.add(span);queue.append((span,basis+(v,)))
    return out


def tangent_checks():
    spaces=subspaces_mod2(4)
    assert len(spaces)==67
    cnt=0
    for pts_a,a in spaces:
        for pts_b,b in spaces:
            intersection=len(set(pts_a)&set(pts_b))
            d=intersection.bit_length()-1
            images=[]
            for i in range(4):
                for j in range(i,4):
                    row=0
                    for ai,x in enumerate(a):
                        for bi,y in enumerate(b):
                            val=((x>>i&1)&(y>>j&1))
                            if i!=j: val^=((x>>j&1)&(y>>i&1))
                            row|=val<<(ai*len(b)+bi)
                    images.append(row)
            rank=rank_mod2(images)
            assert rank==len(a)*len(b)-d*(d-1)//2
            cnt+=1
    return {"field":"F2","ambient_dimension":4,"subspaces":len(spaces),"pairs":cnt,"passed":True}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--quick",action="store_true",help="Skip the largest exhaustive ring cases")
    args=parser.parse_args()
    result={"method":"exact rational formulas and exhaustive finite-ring symplectic-pair enumeration",
            "formula_checks":exact_formula_checks(),"tangent_checks":tangent_checks()}
    cases=[(integer_ring(2,1),2),(integer_ring(2,2),2),(integer_ring(3,1),2),
           (field4(),2),(binary_truncated_ring(2),2),(integer_ring(2,1),3)]
    if not args.quick:
        cases += [(integer_ring(2,3),2),(integer_ring(3,2),2),
                  (binary_truncated_ring(3),2),(ramified_binary_ring(),2),
                  (integer_ring(2,2),3),(integer_ring(3,1),3)]
    result["enumerations"]=[]
    for ring,g in cases:
        item=enumerate_pairs(ring,g)
        result["enumerations"].append(item)
        print(json.dumps(item),flush=True)
    result["totals"]={k:sum(x[k] for x in result["enumerations"]) for k in
                      ("ordered_pairs_examined","symplectic_pairs","corner_matrices_compared")}
    out=Path(__file__).resolve().parents[1]/"results"/"verification.json"
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"saved":str(out),"totals":result["totals"]}),flush=True)


if __name__=="__main__":
    main()
