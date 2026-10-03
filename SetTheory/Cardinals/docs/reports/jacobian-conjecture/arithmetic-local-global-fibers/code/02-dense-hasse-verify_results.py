#!/usr/bin/env python3
"""Reproduce the exact companion checks; write ../data/verification.json."""
from __future__ import annotations
import json
import platform
import random
import sys
import time
from fractions import Fraction
from itertools import product
from pathlib import Path
from math import gcd
import numpy as np
import sympy as sp
from split_fibres import (keller, coefficients, split_fibre, locally_integral,
    denominator_primes, is_p_integral, universal_family, integral_exceptions,
    modular_witness, factor_integer, v2, certificate)

ROOT=Path(__file__).resolve().parents[1]
records=[]

def record(name, **details):
    records.append(dict(name=name,status="PASS",**details))
    print("PASS", name, flush=True)

start=time.monotonic()
x,y,z,w,t,C=sp.symbols('x y z w t C')
F=sp.Matrix(keller(x,y,z))
assert sp.expand(F.jacobian([x,y,z]).det()+2)==0
record("original polynomial Jacobian", determinant=-2)
source=[1/w,t-w,5*w*w-3*t*w-C*w**3]
chart=sp.Matrix([w*t+t*t-C*t**3,2*w+4*t-3*C*t*t,C])
assert all(sp.cancel(a-b)==0 for a,b in zip(F.subs(dict(zip([x,y,z],source)),simultaneous=True),chart))
record("complete inverse chart identities")

c,a,b,s,u=sp.symbols('c a b s u')
r=2-a-b
P=a*b*r;Q=2*(a+b)-a*a-a*b-b*b
T=sp.symbols('T')
assert sp.expand(c*(T-a/c)*(T-b/c)*(T-r/c)-(c*T**3-2*T*T+(Q/c)*T-P/c**2))==0
record("split numerator cubic factorization")
ss,tt=sp.symbols('s t')
phi=sp.Matrix([ss*tt-c*ss*tt*(ss+tt)/2,2*(ss+tt)-c*(ss*ss+ss*tt+tt*tt),c])
u=c*(2*ss+tt)-2;v=c*(ss+2*tt)-2
assert sp.expand(phi.jacobian([c,ss,tt]).det()+(ss-tt)*u*v/2)==0
record("dominant three-parameter Jacobian")
S,J=sp.symbols('S J')
K=1-3*S+2*S*S+J
L=J-16*S*S+24*S**3+12*S*J-8*S**4-8*S*S*J-2*J*J
assert sp.expand(5*K-3*(1-S)-2*K*K-L)==0
record("dyadic cancellation polynomial")

E=np.zeros((8,8,8),dtype=bool)
for xx,yy,zz in product(range(8),repeat=3):
    aa,bb,cc=keller(xx,yy,zz);E[aa%8,bb%8,cc%8]=True
assert int(E.sum())==176
record("independent modulo-eight image", source_classes=512,image_classes=176)

local_rows=[]
for cc in [1,2,3,4,5,6,8,12,16]:
    modulus=16*cc*cc
    bs=np.arange(modulus,dtype=np.int64)
    count=0
    for aa in range(modulus):
        pp=aa*bs*(2-aa-bs)
        qq=2*(aa+bs)-aa*aa-aa*bs-bs*bs
        good=(pp%(2*cc*cc)==0)&(qq%cc==0)
        AA=pp[good]//(2*cc*cc);BB=qq[good]//cc
        count+=int(E[AA%8,BB%8,cc%8].sum())
    e=v2(cc)
    expected=Fraction(3,8) if e==0 else Fraction(3,16) if e in (1,2) else Fraction(3,2**(2*e-1))
    for p,exponent in factor_integer(cc).items():
        if p!=2:expected*=Fraction(3,p**(2*exponent))
    actual=Fraction(count,modulus*modulus)
    assert actual==expected
    local_rows.append(dict(c=cc,modulus=modulus,count=count,density=str(actual)))
record("finite bad-prime density formula",rows=local_rows)

cases=0
for p,e in [(3,1),(5,1),(7,1),(3,2)]:
    modulus=p**(2*e);pe=p**e
    for aa in range(modulus):
        for bb in range(modulus):
            rr=2-aa-bb
            lhs=(aa*bb*rr)%(pe*pe)==0 and (aa*bb+aa*rr+bb*rr)%pe==0
            rhs=(aa%pe,bb%pe) in [(0,0),(0,2%pe),(2%pe,0)]
            assert lhs==rhs
            cases+=1
record("odd-prime integrality residue lemma",cases=cases)

rng=random.Random(20260929)
checked=0
for _ in range(5000):
    cc=rng.choice([i for i in range(-12,13) if i])
    aa,bb=rng.randrange(-40,41),rng.randrange(-40,41)
    if len({aa,bb,2-aa-bb})!=3:continue
    AA,BB,_=coefficients(cc,aa,bb)
    if AA.denominator!=1 or BB.denominator!=1:continue
    pts=split_fibre(cc,aa,bb)
    assert all(keller(*point)==(AA,BB,cc) for point in pts)
    all_local=all(any(is_p_integral(point,p) for point in pts) for p in denominator_primes(pts))
    assert all_local==locally_integral(cc,aa,bb)
    checked+=1
record("independent exact rational/local comparisons",tested_integral_split_fibres=checked,seed=20260929)

family_cases=0
for cc in [-8,-3,-2,-1,1,2,3,4,8]:
    for q in range(4):
        for rr in range(1,4):
            target,pts=universal_family(cc,q,rr)
            assert all(keller(*point)==target for point in pts)
            assert all(not all(v.denominator==1 for v in point) for point in pts)
            assert all(any(is_p_integral(point,p) for point in pts) for p in denominator_primes(pts))
            family_cases+=1
record("universal Zariski-dense family",cases=family_cases)

exrows=[]
for cc in [1,2,3,4,8,12,16]:
    exc=integral_exceptions(cc)
    exrows.append(dict(c=cc,targets=[list(tar) for tar in sorted(exc)]))
assert list(integral_exceptions(1))==[(-1,-1,1)]
assert not integral_exceptions(2)
record("complete divisor enumeration of integral exceptions",rows=exrows)

example=certificate(1,1,3)
assert example['target']==['-3','-5','1']
for modulus in [1,2,3,8,40,105,1000,2**8*3**4*5**3*7]:
    modular_witness(1,1,3,modulus)
record("constructive all-modulus witnesses",moduli=[1,2,3,8,40,105,1000,2**8*3**4*5**3*7])

report=dict(python=platform.python_version(),sympy=sp.__version__,numpy=np.__version__,
            elapsed_seconds=round(time.monotonic()-start,3),records=records,
            proof_boundary="Finite exact checks supplement, but do not replace, the universal proofs in article.tex.")
(ROOT/'data'/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
(ROOT/'data'/'example.json').write_text(json.dumps(example,indent=2)+'\n')
print(f"{len(records)} groups passed; {report['elapsed_seconds']} seconds")
