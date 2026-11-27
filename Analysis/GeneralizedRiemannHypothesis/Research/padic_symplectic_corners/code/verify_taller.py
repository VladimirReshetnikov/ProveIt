#!/usr/bin/env python3
"""Exhaustive checks of the symplectic-pair to taller-corner corollary."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
import numpy as np


def check(p,g,a):
    vectors=np.array(list(product(range(p),repeat=2*g)),dtype=np.int64)
    counts=np.zeros(p**(4*a),dtype=np.int64)
    weights=p**np.arange(4*a-1,-1,-1,dtype=np.int64)
    for v in vectors:
        pair=sum(v[2*j]*vectors[:,2*j+1]-v[2*j+1]*vectors[:,2*j] for j in range(g))%p
        w=vectors[pair==1]
        corner=np.empty((len(w),4*a),dtype=np.int64)
        corner[:,0::2]=v[:2*a]
        corner[:,1::2]=w[:,:2*a]
        np.add.at(counts,corner@weights,1)
    total=int(counts.sum());tv=F(0);n=2*g-2*a
    assert total==p**(4*g-1)*(1-F(1,p**(2*g)))
    for i,m in enumerate(product(range(p),repeat=4*a)):
        omega=sum(m[4*j]*m[4*j+3]-m[4*j+2]*m[4*j+1] for j in range(a))%p
        h=(1-F(1,p**n)+(F(1,p**(n-1)) if omega==1 else 0))/(1-F(1,p**(2*g)))
        probability=F(int(counts[i]),total)
        assert probability==h/F(p**(4*a))
        tv+=abs(probability-F(1,p**(4*a)))/2
    assert tv==(1-F(1,p)+F(1,p**(2*a+1)))*F(p**(2*a)-1,p**(2*g)-1)
    return dict(p=p,g=g,target_half_dimension=a,ordered_pairs=len(vectors)**2,frames=total,
                matrices=p**(4*a),tv=str(tv),passed=True)


def main():
    data=[check(2,3,2),check(2,4,2),check(3,3,2)]
    path=Path(__file__).resolve().parents[1]/"results"/"taller_corner_checks.json"
    path.write_text(json.dumps(data,indent=2)+"\n")
    print(json.dumps(data,indent=2))


if __name__=="__main__":main()
