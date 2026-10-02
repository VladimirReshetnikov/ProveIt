#!/usr/bin/env python3
"""Generate the logarithmic and inverse coefficients by exact formal algebra.
A stands for pi**2/(6*s**2). Coefficients are polynomials in A over Q.
"""
from __future__ import annotations
import argparse, json
from pathlib import Path
import sympy as sp

def generate(order: int = 6):
    if order < 1 or order > 10:
        raise ValueError('Use 1 <= order <= 10 (higher orders need more resources).')
    z,A=sp.symbols('z A'); N=order+2
    def tr(e,n=N): return sp.series(e,z,0,n).removeO().expand()
    def T(e): return tr(-z*z/(1-z)*sp.diff(e,z))
    derivative=tr(1/(1-z)); C=sp.Integer(0)
    for j in range((N+1)//2):
        if j: derivative=T(T(derivative))
        moment=sp.simplify(2*(1-sp.Rational(1,2)**(2*j+1))*
                           sp.zeta(2*j+2)*(6*A/sp.pi**2)**(j+1))
        C=tr(C+moment*derivative)
    B=tr(C+T(C)); shift=sp.Integer(0)
    for _ in range((N+2)//3+2):
        zi=tr(z/(1+z*shift))
        shift=tr(-sp.log(1+2*tr(B.subs(z,zi))*zi**2)/2)
    zi=tr(z/(1+z*shift))
    H=tr(sp.exp(shift)*(1/z+shift-1+zi*tr((2*C+T(C)).subs(z,zi))),order+1)
    correction=tr(H-1/z+1,order+1)
    delta=sp.Integer(0)
    for _ in range((N+2)//2+2):
        logd=tr(sp.log(1+delta))
        cp=tr(correction.subs(z,tr(z/(1+z*logd))))
        delta=tr(-z*(tr((1+delta)*logd-delta)+tr((1+delta)*cp)),order+1)
    inv=tr((1+delta)**2,order+1)
    result={'parameter':'A = pi^2/(6*s^2)',
            'log_coefficients':{str(j):str(sp.factor(H.coeff(z,j))) for j in range(1,order+1)},
            'inverse_n_coefficients':{str(j):str(sp.factor(inv.coeff(z,j))) for j in range(1,order+1)}}
    expected=[A,A,A-A**2/2,A+sp.Rational(9,10)*A**2,
              A+sp.Rational(41,5)*A**2+A**3/2,
              A+27*A**2+sp.Rational(1973,210)*A**3]
    for j in range(1,min(order,6)+1): assert sp.expand(H.coeff(z,j)-expected[j-1])==0
    expected_inverse=[sp.Integer(0),-2*A,-2*A,4*A**2-2*A,
                      sp.Rational(6,5)*A**2-2*A,
                      -8*A**3-sp.Rational(77,5)*A**2-2*A]
    for j in range(1,min(order,6)+1):
        assert sp.expand(inv.coeff(z,j)-expected_inverse[j-1])==0
    return result

def main():
    p=argparse.ArgumentParser();p.add_argument('--order',type=int,default=6);args=p.parse_args()
    result=generate(args.order)
    out=Path(__file__).resolve().parent.parent/'data'/'formal_coefficients.json'
    out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps(result,indent=2)+'\n'); print(json.dumps(result,indent=2))
if __name__=='__main__': main()
