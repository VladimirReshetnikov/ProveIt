#!/usr/bin/env python3
"""Exact finite checks for the weighted polynomial norm theorem.

These checks are regression evidence for formulas, not proofs of their
universal validity or of iPRA derivability. Requires SymPy.
"""
from __future__ import annotations
import json
import sys
from math import gcd
from pathlib import Path
from random import Random
import sympy as sp

X, Y, T, Z = sp.symbols('X Y T Z')

def weight(poly, m, d):
    p = sp.Poly(poly, X, Y)
    assert not p.is_zero
    return max(m*i+d*j for (i,j), a in p.terms() if a != 0)

def lead_weight(poly, m, d):
    p=sp.Poly(poly, X, Y)
    W=weight(poly,m,d)
    return [(i,j,a) for (i,j),a in p.terms() if m*i+d*j==W]

def matrix_of_mul(F, G, m):
    cols=[]
    for j in range(m):
        rem=sp.rem(G*Y**j,F,Y)
        p=sp.Poly(rem,Y)
        cols.append([p.nth(k) for k in range(m)])
    return sp.Matrix(m,m,lambda i,j:cols[j][i])

def norm(F,G,m):
    return sp.Poly(sp.expand(matrix_of_mul(F,G,m).det()),X)

def finite_basis(m,d,L):
    return [(i,j) for j in range(m) for i in range(L+1) if m*i+d*j<=L]

def verify_case(F,G,m,d,c):
    assert gcd(m,d)==1
    mon=lead_weight(G,m,d)
    assert len(mon)==1
    i,j,a=mon[0]
    W=m*i+d*j
    N=norm(F,G,m)
    assert N.degree()==W
    expected=a**m*((-1)**(m-1)*c)**j
    assert sp.expand(N.LC()-expected)==0
    FT=sp.expand(T**(m*d)*F.subs({X:T**(-m),Y:T**(-d)*Z},simultaneous=True))
    GT=sp.expand(T**W*G.subs({X:T**(-m),Y:T**(-d)*Z},simultaneous=True))
    assert all(e[0]>=0 for e in sp.Poly(FT,T,Z).monoms())
    assert all(e[0]>=0 for e in sp.Poly(GT,T,Z).monoms())
    assert sp.expand(FT.subs(T,0)-(Z**m-c))==0
    assert sp.expand(GT.subs(T,0)-a*Z**j)==0
    return {'m':m,'d':d,'weight':W,'degree':int(N.degree()),'leading_coefficient':str(N.LC())}

def main():
    rng=Random(20261115)
    records=[]
    # A fixed finite deterministic sample, including mixed equations.
    for m,d in [(2,1),(2,3),(2,5),(3,2),(3,4),(4,3)]:
        c=sp.Integer(rng.choice([-3,-1,1,2]))
        lower=[X**i*Y**j for j in range(m) for i in range(d+1) if m*i+d*j<m*d]
        F=Y**m-c*X**d+sum(rng.randrange(-2,3)*z for z in lower)
        for k in range(3):
            G=sum(rng.randrange(-2,3)*X**i*Y**j for j in range(m) for i in range(3))
            if G==0: G=sp.Integer(1)
            records.append(verify_case(F,G,m,d,c))
    # Exact formula and threshold, including d=1 and L=0.
    dims=0
    for m in range(2,9):
        for d in range(1,10):
            if gcd(m,d)!=1: continue
            threshold=max(0,m*d-m-d)
            genus_numerator=(m-1)*(d-1)
            assert genus_numerator%2==0
            for L in range(threshold,threshold+15):
                assert len(finite_basis(m,d,L))==L+1-genus_numerator//2
                dims+=1
    # Sharp zero-count example, all four zeros listed.
    f=X*(X-1)*(X-2)*(X-3)
    F=Y**3-f; G=Y
    N=norm(F,G,3)
    pts=[(i,0) for i in range(4)]
    assert N.as_expr()==sp.expand(f)
    assert len(pts)==weight(G,3,4)
    for x,y in pts:
        assert F.subs({X:x,Y:y})==0 and G.subs({X:x,Y:y})==0
    # Two points in one fiber force multiplicity 2, not merely one X root.
    # F=Y^3-Y-X^4 has three rational roots 0,+1,-1 in the X=0 fiber.
    F2=Y**3-Y-X**4; G2=X
    N2=norm(F2,G2,3)
    assert N2.as_expr()==X**3
    fibers=[(0,-1),(0,0),(0,1)]
    assert all(F2.subs({X:x,Y:y})==G2.subs({X:x,Y:y})==0 for x,y in fibers)
    # Initial determinant certificate beyond coprime weights: F=Y²-2X⁴-X-1.
    F3=Y**2-2*X**4-X-1; G3=X**2+Y
    N3=norm(F3,G3,2)
    assert N3.degree()==4 and N3.LC()==-1
    out={
        'status':'all checks passed',
        'scope':'finite regression checks; not formal proofs',
        'seed':20261115,
        'randomized_exact_cases':records,
        'dimension_checks':dims,
        'sharp_example':{'F':str(F),'G':str(G),'norm':str(N.as_expr()),'points':pts,'bound':4},
        'repeated_fiber_example':{'F':str(F2),'G':str(G2),'norm':str(N2.as_expr()),'points':fibers,'bound':3},
        'noncoprime_certificate':{'F':str(F3),'G':str(G3),'norm':str(N3.as_expr()),'initial_norm':-1,'bound':4},
        'sympy_version':sp.__version__,
    }
    dst=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name('weighted_norm_checks.json')
    dst.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ['randomized_exact_cases']},indent=2))

if __name__=='__main__': main()
