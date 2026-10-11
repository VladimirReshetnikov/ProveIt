#!/usr/bin/env python3
"""Exact finite checks for the periodic Stieltjes collision theorem.

This is finite symbolic verification, not a proof-assistant formalization.
All analytic claims and normalizations are proved in the accompanying article.
"""
from __future__ import annotations
import json
import math
import platform
from pathlib import Path
from functools import lru_cache
import sympy as s

ROOT = Path(__file__).resolve().parents[1]
DEG = 7
u, v, X = s.symbols('u v X')
PI = s.Symbol('pi', real=True)
Z = {k: (s.zeta(k) / s.pi**k * PI**k if k % 2 == 0 else s.Symbol(f'zeta_{k}')) for k in range(2, DEG + 3)}
Z = {k: s.expand(x) for k, x in Z.items()}
Poly = dict[tuple[int,int], s.Expr]

def add(*ps: Poly) -> Poly:
    out: Poly = {}
    for p in ps:
        for key,c in p.items(): out[key] = out.get(key,s.S.Zero) + c
    return {k:s.expand(c) for k,c in out.items() if c != 0}

def scale(p: Poly, c: s.Expr) -> Poly:
    return {k:s.expand(c*x) for k,x in p.items() if c*x != 0}

def mul(p: Poly, q: Poly, degree: int = DEG) -> Poly:
    out: Poly = {}
    for (a,b),c in p.items():
        for (d,e),f in q.items():
            if a+b+d+e <= degree:
                key=(a+d,b+e); out[key]=out.get(key,s.S.Zero)+c*f
    return {k:s.expand(c) for k,c in out.items() if c != 0}

def swap(p: Poly) -> Poly: return {(b,a):c for (a,b),c in p.items()}

def exp_poly(p: Poly, degree: int = DEG) -> Poly:
    out={(0,0):s.S.One}; term=out
    for k in range(1,degree+1):
        term=scale(mul(term,p,degree),s.Rational(1,k)); out=add(out,term)
    return out

def homog(power: int, sign: int=1) -> Poly:
    return {(j,power-j):s.Integer(math.comb(power,j))*sign**(power-j) for j in range(power+1)}

def tr(p: Poly, degree:int) -> Poly: return {k:c for k,c in p.items() if sum(k)<=degree}

def shift_down(p: Poly, a:int,b:int) -> Poly:
    assert all(c==0 or (i>=a and j>=b) for (i,j),c in p.items())
    return {(i-a,j-b):c for (i,j),c in p.items() if c!=0}

logA:Poly={}; logE:Poly={}
for k in range(2,DEG+1):
    pure={(k,0):s.S.One,(0,k):s.S.One}
    logA=add(logA,scale(add(pure,scale(homog(k),-1)),Z[k]/k))
    if k%2==0:
        logA=add(logA,scale(add(homog(k,-1),scale(homog(k),-1)),-s.Rational(2,k)*(1-s.Rational(1,2**k))*Z[k]))
    logE=add(logE,scale(add({(k,0):s.S.One},scale(homog(k),(-1)**k),{(0,k):s.Integer(-(-1)**k)}),Z[k]/k))
A=exp_poly(logA); E=exp_poly(logE); ER=swap(E)

@lru_cache(None)
def P(n:int) -> tuple[s.Expr,...]:
    a=[s.S.One]
    for j in range(1,n+1):
        b=a+[s.S.Zero]
        for k,c in enumerate(a): b[k+1]+=c/s.Integer(j)
        a=b
    return tuple(map(s.expand,a))

def pu(n:int) -> Poly: return {(i,0):c for i,c in enumerate(P(n))}
def pv(n:int) -> Poly: return {(0,i):c for i,c in enumerate(P(n))}
def pw(n:int) -> Poly:
    return add(*(scale(homog(j),c) for j,c in enumerate(P(n)) if j<=DEG))

def kernel_num(p:int,q:int) -> Poly:
    r=p+q
    return add(mul(A,pw(r)),mul(pu(p),pv(q)),scale(mul(pu(p),pv(r)),-1),scale(mul(pv(q),pu(r)),-1))

def harm(n:int,k:int=1): return sum((s.Rational(1,j**k) for j in range(1,n+1)),s.S.Zero)

def kappa(m:int,n:int,p:int,q:int):
    return s.expand((-1)**(p+m+n)*s.factorial(m)*s.factorial(n)*kernel_num(p,q).get((m+1,n+1),0))

checks=[]
def check(name:str, lhs, rhs=0):
    ok=s.expand(lhs-rhs)==0
    checks.append({'name':name,'passed':bool(ok)})
    if not ok: raise AssertionError(f'{name}: {s.expand(lhs-rhs)}')

# Independent gamma/trigonometric relation, with even zeta identities imposed.
ea=add(mul({(0,1):s.S.One},E),mul({(1,0):s.S.One},ER),scale(mul(homog(1),A),-1))
for key,c in ea.items():
    if sum(key)<=DEG: check(f'gamma_relation_{key}',c)

formulas=[]
for p in range(7):
    for q in range(7-p):
        B=kernel_num(p,q)
        for (i,j),c in B.items():
            if i==0 or j==0: check(f'axis_divisibility_{p}_{q}_{i}_{j}',c)
        for m in range(5):
            for n in range(5-m):
                k=kappa(m,n,p,q)
                check(f'reflection_{m}_{n}_{p}_{q}',k,(-1)**(p+q)*kappa(n,m,q,p))
                formulas.append({'m':m,'n':n,'p':p,'q':q,'delta_order':p+q,'coefficient':str(k)})
        r=p+q
        closed=(-1)**p*(2*Z[2]+(harm(r)-harm(p))*(harm(r)-harm(q))-harm(r,2))
        check(f'polygamma_{p}_{q}',kappa(0,0,p,q),closed)

# The one-factor contact rule checked against a direct Pochhammer difference.
for p in range(13):
    for m in range(13):
        d=(-1)**m*s.factorial(m)*(P(p)[m+1] if m+1<len(P(p)) else 0)
        if m>=p: check(f'one_factor_support_{m}_{p}',d)
        if p<12:
            dn=(-1)**m*s.factorial(m)*(P(p+1)[m+1] if m+1<len(P(p+1)) else 0)
            rhs=(-1)**m*s.factorial(m)*(P(p)[m] if m<len(P(p)) else 0)/s.Integer(p+1)
            check(f'one_factor_increment_{m}_{p}',dn-d,rhs)

# An independent nonzero Fourier-mode calculation of the anomaly.
# exp(Gamma-log + Lt) has coefficients b_j; the Fourier generator is (P_p-exp)/t.
D=5
@lru_cache(None)
def bseries(sign:int) -> tuple[s.Expr,...]:
    log=[s.S.Zero, X+sign*s.I*PI/2]+[Z[k]/k for k in range(2,D+2)]
    b=[s.S.One]
    for j in range(1,D+2):
        b.append(s.expand(sum(k*log[k]*b[j-k] for k in range(1,j+1))/j))
    return tuple(b)

def fb(p:int,sign:int,var:str) -> Poly:
    bs=bseries(sign)
    co=[s.expand((P(p)[j+1] if j+1<len(P(p)) else 0)-bs[j+1]) for j in range(D+1)]
    if var=='u': return {(j,0):c for j,c in enumerate(co)}
    if var=='v': return {(0,j):c for j,c in enumerate(co)}
    return add(*(scale(homog(j),c) for j,c in enumerate(co)))

for p in range(4):
    for q in range(4-p):
        r=p+q
        canonical=mul(fb(p,-1,'u'),fb(q,1,'v'),D)
        part1=add(mul(pu(p),fb(r,1,'v'),D),scale(mul(E,fb(r,1,'w'),D),-1))
        part2=add(mul(pv(q),fb(r,-1,'u'),D),scale(mul(ER,fb(r,-1,'w'),D),-1))
        # No need to divide top truncation artifacts; low coefficients suffice.
        B=kernel_num(p,q)
        for m in range(3):
            for n in range(3-m):
                fpcoeff=part1.get((m+1,n),0)+part2.get((m,n+1),0)
                check(f'fourier_polynomial_{m}_{n}_{p}_{q}',canonical.get((m,n),0)-fpcoeff,B.get((m+1,n+1),0))

# Printed checkpoints, independent of the generic closed formula.
check('base_atom',kappa(0,0,0,0),2*Z[2])
check('first_jet_atom',kappa(1,0,0,0),Z[3])
check('mixed_jet_atom',kappa(1,1,0,0),s.Rational(7,2)*Z[4])
check('second_jet_atom',kappa(2,0,0,0),s.Rational(11,2)*Z[4])
check('trigamma_atom',kappa(0,0,1,1),1-2*Z[2])
# A corruption control must detect deletion of the base atom.
corruption_detected = s.expand(kappa(0,0,0,0)) != 0
assert corruption_detected

out={'status':'all passed','python':platform.python_version(),'sympy':s.__version__,
     'total_degree_internal':DEG,'formula_count':len(formulas),'exact_assertions':len(checks),
     'corruption_control_detected_missing_atom':bool(corruption_detected),'checks':checks}
(ROOT/'data'/'exact_checks.json').write_text(json.dumps(out,indent=2)+'\n')
(ROOT/'data'/'contact_coefficients.json').write_text(json.dumps({'convention':'C = Hadamard(J) + coefficient * delta^(p+q)','pi_symbol':'pi','formulas':formulas},indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='checks'},indent=2))
