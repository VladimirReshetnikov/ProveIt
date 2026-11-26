#!/usr/bin/env python3
"""Exact finite checks of the finite-slope Gauss lemma; not a proof.

No external dependencies. The proof is in non_tower_specialization.md.
Tests every nonzero polynomial supported on {1,X,Y,X^2,XY,Y^2}
with coefficients in {-2,-1,0,1,2}, at p=2 and rho=1, plus seeded
higher-degree examples and simultaneous packets at several radii.
"""
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import comb
import json, random
from pathlib import Path


def vp(x, p):
    assert x
    x=abs(x); ans=0
    while x%p==0:
        x//=p; ans+=1
    return ans


def gauss(F,p,rho):
    # F is a dictionary from a tuple of exponents to a nonzero integer.
    if not F: return None  # +infinity
    return min(Fraction(vp(c,p))+sum(a)*rho for a,c in F.items() if c)


def mul(f,g):
    out={}
    for a,c in f.items():
        for b,d in g.items(): out[a+b]=out.get(a+b,0)+c*d
    return {a:c for a,c in out.items() if c}


@lru_cache(None)
def bpow(n,b):
    f={0:1}; g={j:comb(n,j) for j in range(1,n+1)}
    for _ in range(b):f=mul(f,g)
    return f


def restrict(F,n):
    out={}
    for (a,b),c in F.items():
        for j,d in bpow(n,b).items(): out[(a+j,)]=out.get((a+j,),0)+c*d
    return {a:c for a,c in out.items() if c}


def packet_check(packet,p,rho):
    A=[gauss(f,p,rho) for f in packet]
    B=sum(A,Fraction(0)); M=int(B//rho)+1; r=rho/M**2
    bads=[]
    for f,a in zip(packet,A):
        bad=[]
        for n in range(1,M+1):
            value=gauss(restrict(f,n),p,r)
            if value is None or value>a:bad.append(n)
        assert len(bad)<=int(a//rho),(f,p,rho,a,M,bad)
        bads.append(set(bad))
    bad_union=set().union(*bads)
    good=sorted(set(range(1,M+1))-bad_union)
    assert good
    return {"p":p,"rho":str(rho),"B":str(B),"M":M,"r":str(r),"good":good,
            "bad_counts":[len(b) for b in bads]}


def main():
    monomials=[(0,0),(1,0),(0,1),(2,0),(1,1),(0,2)]
    exhaustive=0
    for cs in product(range(-2,3),repeat=len(monomials)):
        f={a:c for a,c in zip(monomials,cs) if c}
        if not f:continue
        packet_check([f],2,Fraction(1));exhaustive+=1
    rng=random.Random(20261125)
    random_cases=0
    for p in [2,3,5]:
        for rho in map(Fraction,['1/3','1/2','1','2']):
            for _ in range(25):
                packet=[]
                for _ in range(rng.randrange(1,5)):
                    f={}
                    for _ in range(rng.randrange(3,15)):
                        a,b=rng.randrange(9),rng.randrange(9)
                        c=rng.choice([-1,1])*p**rng.randrange(5)*rng.randrange(1,p)
                        f[a,b]=f.get((a,b),0)+c
                    f={a:c for a,c in f.items() if c}
                    if f:packet.append(f)
                packet_check(packet,p,rho);random_cases+=1
    # A packet that defeats slopes 1,2,3 individually; slope 4 survives.
    packet=[]
    for n in range(1,4):
        f={(0,1):1}
        for j in range(1,n+1):f[j,0]=-comb(n,j)
        packet.append(f)
    illustrative=packet_check(packet,2,Fraction(1))
    assert illustrative['M']==4 and 4 in illustrative['good']
    result={"status":"PASS","exhaustive_polynomials":exhaustive,
            "seeded_random_packets":random_cases,"seed":20261125,
            "illustrative_three_curve_obstruction":illustrative,
            "scope":"Exact integer arithmetic checks; the theorem is proved symbolically in the manuscript."}
    dest=Path(__file__).with_suffix('.json');dest.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
