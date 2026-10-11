#!/usr/bin/env python3
"""Generate exact all-depth logarithmic-moment identities from Theorem 5.1.

Examples:
  python code/generate_identities.py --depth 2 --weights 2,0 --center --expand-central
  python code/generate_identities.py --depth 3 --weights 1,1,0 --center --tex

C(r,a,v,mu), E(a,v), and Eta(a,v) denote the entire functions in the
article. The output is a symbolic formula, not a numerical integration.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import sympy as sp
from verify import cp, rp, X, T, U, P

A, MU = sp.symbols('a mu')
Cfun, Efun, Etafun = (sp.Function(n) for n in ('C', 'E', 'Eta'))

def central(r: int, v, a=A):
    """Pole-free central formula, retaining E(a,0)=1 analytically."""
    if r < 1:
        raise ValueError('depth must be positive')
    value=0
    for (j,),co in sp.Poly(cp(r),X).terms():
        value += co*(sp.rf(v,j-1)*Efun(a,v+j-1) if r%2==0
                     else sp.rf(v,j)*Etafun(a,v+j))
    return value/sp.factorial(r-1)

def moment(weights: list[int], *, center: bool=False, expand_central: bool=False):
    """Return (orders, exact expression) for any finite nonnegative weights."""
    if not weights or any(not isinstance(k,int) or k<0 for k in weights):
        raise ValueError('weights must be a nonempty list of nonnegative integers')
    r=len(weights)
    orders=sp.symbols('s1:'+str(r+1))
    total=sum(orders)
    pol=sp.expand(sp.prod(rp(k,z) for k,z in zip(weights,orders)))
    out=0
    for (bt,du),co in sp.Poly(pol,T,U).terms():
        k=bt//2
        for q in range(k+1):
            rr=r+2*q; v=total+du
            c=co*sp.binomial(k,q)*(-P)**(k-q)
            if bt%2:
                out+=c*(MU*Cfun(rr,A,v,MU)-v*Cfun(rr,A,v+1,MU))/rr
            else:
                out+=c*Cfun(rr,A,v,MU)
    if center:
        out=out.subs(MU,0)
        if expand_central:
            out=out.replace(lambda x:x.func==Cfun,
                            lambda x:central(int(x.args[0]),x.args[2],x.args[1]))
    elif expand_central:
        raise ValueError('--expand-central requires --center')
    out=sp.factor(sp.expand(out).subs(P,sp.pi**2))
    return orders,out

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--depth',type=int,default=2)
    parser.add_argument('--weights',default='1,0')
    parser.add_argument('--center',action='store_true')
    parser.add_argument('--expand-central',action='store_true')
    parser.add_argument('--tex',action='store_true')
    args=parser.parse_args()
    try:
        weights=[int(x.strip()) for x in args.weights.split(',')]
        if len(weights)!=args.depth:
            raise ValueError('the number of weights must equal --depth')
        _,value=moment(weights,center=args.center,expand_central=args.expand_central)
    except ValueError as exc:
        parser.error(str(exc))
    print(sp.latex(value) if args.tex else value)

if __name__=='__main__':
    main()
