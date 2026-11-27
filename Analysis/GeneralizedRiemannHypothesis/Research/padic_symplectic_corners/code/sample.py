#!/usr/bin/env python3
"""Exact sampling of a 2x2 corner of Haar Sp(2g,Z/p^e Z).

Uses four independent uniform entries followed by an exact rational rejection
test. No ambient 2g x 2g symplectic matrix is constructed. Expected proposals:
8/5, independent of g, p and e. The CLI uses Python's pseudorandom generator;
the exactness claim concerns the ideal discrete-uniform randomness model.
"""
from fractions import Fraction as F
import argparse
import json
import random


def prime(p):
    return p>=2 and all(p%d for d in range(2,int(p**0.5)+1))


def likelihood(p,g,e,matrix):
    if g<2 or e<1 or not prime(p):
        raise ValueError("Require prime p, g>=2, e>=1")
    a,b,c,d=matrix
    modulus=p**e
    t=(1-a*d+b*c)%modulus
    v=e if t==0 else 0
    if t:
        while t%p==0:
            t//=p;v+=1
    n=2*g-2
    ratio=F(1,p**(n-1))
    f=(1-F(1,p**n))*sum((ratio**r for r in range(min(v,e-1)+1)),F(0))
    if v==e:
        f+=ratio**e
    return f/(1-F(1,p**(2*g)))


def sample(p,g,e,rng=None):
    if g<2 or e<1 or not prime(p):
        raise ValueError("Require prime p, g>=2, e>=1")
    rng=random if rng is None else rng
    proposals=0
    while True:
        proposals+=1
        a=tuple(rng.randrange(p**e) for _ in range(4))
        acceptance=likelihood(p,g,e,a)*F(5,8)
        assert 0<acceptance<=1
        if rng.randrange(acceptance.denominator)<acceptance.numerator:
            return ((a[0],a[1]),(a[2],a[3])),proposals


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--p",type=int,default=2)
    ap.add_argument("--g",type=int,default=2)
    ap.add_argument("--e",type=int,default=4)
    ap.add_argument("--count",type=int,default=10)
    ap.add_argument("--seed",type=int,default=0)
    a=ap.parse_args()
    rng=random.Random(a.seed)
    for _ in range(a.count):
        matrix,proposals=sample(a.p,a.g,a.e,rng)
        print(json.dumps({"matrix":matrix,"proposals":proposals}))


if __name__=="__main__":
    main()
