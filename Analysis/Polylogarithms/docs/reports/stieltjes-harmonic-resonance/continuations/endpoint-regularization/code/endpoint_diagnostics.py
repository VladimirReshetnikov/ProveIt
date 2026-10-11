#!/usr/bin/env python3
"""Direct Abel sums minus the predicted complete endpoint polynomial.

These are floating-point convergence diagnostics, not interval certificates.
The truncation cutoff is 35/epsilon. No extrapolated limit is used in a proof.
"""
from __future__ import annotations
import json, math
from pathlib import Path
from functools import lru_cache
import numpy as np
import mpmath as mp
import sympy as s
from coefficients import cutoff_polynomials, abel_polynomial, G, L

ROOT=Path(__file__).resolve().parents[1]
mp.mp.dps=45
contents=[(1,1),(2,1),(0,2),(1,2)]
Q={alpha:abel_polynomial(cutoff_polynomials(alpha)[alpha]) for alpha in contents}

@lru_cache(None)
def value(symbol_name, astr):
    a=mp.mpf(astr)
    if symbol_name=='G':return mp.euler
    if symbol_name.startswith('g'):
        r=int(symbol_name[1:]);return -mp.digamma(a) if r==0 else mp.stieltjes(r,a)
    tail=symbol_name[1:]
    if '_' in tail:
        k,r=map(int,tail.split('_'));return mp.diff(lambda x:mp.zeta(x,a),k,r)
    return mp.zeta(int(tail))

def evaluate(expr, astr, lv):
    syms=sorted(expr.free_symbols,key=str)
    func=s.lambdify(syms,expr,'mpmath')
    return func(*(lv if str(x)=='L' else value(str(x),astr) for x in syms))

rows=[]
for astr in ['1','0.5']:
    a=float(astr)
    for eps in [1e-2,1e-3,1e-4,1e-5]:
        N=math.ceil(35/eps)
        x=np.arange(N,dtype=np.float64)+a
        f=1/x; h=np.log(x)/x
        A=np.cumsum(f)-f; B=np.cumsum(h)-h
        AA=np.cumsum(f*f)-f*f
        AB=np.cumsum(f*h)-f*h
        BB=np.cumsum(h*h)-h*h
        weight=np.exp(-eps*x)
        increments={
            (1,1):f*B+h*A,
            (2,1):f*(A*B-AB)+h*(A*A-AA)/2,
            (0,2):h*B,
            (1,2):f*(B*B-BB)/2+h*(A*B-AB),
        }
        lv=mp.log(1/mp.mpf(str(eps)))
        for alpha,inc in increments.items():
            actual=float(np.dot(weight,inc))
            prediction=evaluate(Q[alpha],astr,lv)
            constant=evaluate(Q[alpha].subs(L,0),astr,0)
            rows.append({'a':astr,'epsilon':eps,'terms':N,'content':alpha,
                         'direct_sum':actual,'predicted_polynomial':float(prediction),
                         'difference':float(mp.mpf(actual)-prediction),
                         'proved_endpoint_constant':mp.nstr(constant,35)})
        del x,f,h,A,B,AA,AB,BB,weight,increments
out={'meaning':'Floating-point endpoint diagnostics; differences include analytic remainder, truncation and rounding.',
     'rows':rows,'numpy':np.__version__}
(ROOT/'results/endpoint_diagnostics.json').write_text(json.dumps(out,indent=2)+'\n')
for row in rows:
    print(row['a'],row['content'],row['epsilon'],f"{row['difference']:.10e}")
