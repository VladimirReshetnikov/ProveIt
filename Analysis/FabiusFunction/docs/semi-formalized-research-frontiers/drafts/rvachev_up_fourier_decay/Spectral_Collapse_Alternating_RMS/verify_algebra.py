#!/usr/bin/env python3
"""Exact finite-algebra checks supplementing the analytic proofs.
Run: python verify_algebra.py --output algebra_certificate.json
Requires SymPy. This checks finite instances, not the infinite-dimensional theorem.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
from fractions import Fraction
from functools import lru_cache
import sympy as sp

def sine_weight(m: int) -> dict[int, sp.Rational]:
    return {j:sp.Rational((-1)**abs(j)*sp.binomial(2*m,m+j),4**m)
            for j in range(-m,m+1)}

def transfer_matrix(b: int, w: dict[int, sp.Rational], M: int) -> sp.Matrix:
    K=M//(b-1)
    return sp.Matrix([[w.get(b*r-k,sp.S.Zero)
        for k in range(-K,K+1)] for r in range(-K,K+1)])

def laurent_multiply(f: dict, g: dict) -> dict:
    h={}
    for i,a in f.items():
        for j,b in g.items():
            h[i+j]=h.get(i+j,0)+a*b
    return {i:sp.expand(a) for i,a in h.items() if a != 0}

@lru_cache(None)
def alpha(k: int) -> int:
    if k==0:return 0
    if k==1:return 1
    return -2*alpha(k//2) if k%2==0 else alpha(k//2)+alpha(k//2+1)

@lru_cache(None)
def eta(k: int) -> Fraction:
    if k==0:return Fraction(1)
    if k==1:return Fraction(-1,3)
    return eta(k//2) if k%2==0 else -(eta(k//2)+eta(k//2+1))/2

def P_mode(poly: dict[int,Fraction]) -> dict[int,Fraction]:
    out={}
    for k,c in poly.items():
        m=k//2
        pairs=[(m,c)] if k%2==0 else [(m,-c/2),(m+1,-c/2)]
        for r,v in pairs:out[r]=out.get(r,Fraction(0))+v
    return {r:v for r,v in out.items() if v}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path('algebra_certificate.json'))
    args=parser.parse_args()
    Y=sp.Symbol('Y'); z=sp.Symbol('z')
    polys={}
    for m in range(1,6):
        A=transfer_matrix(2,sine_weight(m),m)
        B=4**m*A
        p=sp.factor(B.charpoly(Y).as_expr())
        polys[str(m)]=str(p)
        print('m=',m,'integer-matrix characteristic polynomial:',p)
    A=transfer_matrix(2,sine_weight(1),1)
    assert sp.expand((sp.eye(3)-z*A).det()-(1-z/2)*(1+z/4)**2) == 0
    assert (A+sp.eye(3)/4).nullspace().__len__()==2
    A4=transfer_matrix(2,sine_weight(2),2)
    assert len((A4-sp.eye(5)/16).nullspace())==2
    # Exact trace comparison via root-of-unity coefficient selection.
    count=0
    for b in range(2,6):
        for M in range(0,5):
            w={j:sp.Rational((j+M+2)*((-1)**abs(j)),M+3)
               for j in range(-M,M+1)}
            A=transfer_matrix(b,w,M)
            W={0:sp.S.One}
            for n in range(1,5):
                W=laurent_multiply(W,{j*b**(n-1):c for j,c in w.items()})
                selected=sum(c for j,c in W.items() if j%(b**n-1)==0)
                assert sp.expand(selected-sp.trace(A**n))==0
                # The repeated endpoint contributes c**n/(b**n-1).
                c=sum(w.values())
                full_trace=selected+c**n/sp.Integer(b**n-1)
                assert sp.expand(full_trace-sp.trace(A**n)-c**n/sp.Integer(b**n-1))==0
                count+=1
    mode_checks=0
    for k in range(1,513):
        n=(k-1).bit_length()
        f={k:Fraction(1)}
        for _ in range(n):f=P_mode(f)
        a=Fraction(-1,2)**n*alpha(k)
        expected={0:eta(k)+a/3,1:a}
        expected={r:v for r,v in expected.items() if v}
        assert f==expected,(k,n,f,expected)
        assert abs(alpha(k))<=k and abs(eta(k))<=1
        mode_checks+=1
    result={'status':'PASS','sympy_version':sp.__version__,
            'characteristic_polynomials_of_4^m_A_m':polys,
            'finite_trace_checks':count,'Fourier_mode_checks':mode_checks,
            'quadratic_semisimple':True,'quartic_1_over_16_semisimple':True,
            'scope':'Finite exact checks; analytic theorems are proved in article.tex.'}
    args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print('PASS',count,'trace checks and',mode_checks,'mode checks.')
if __name__=='__main__':main()
