#!/usr/bin/env python3
"""Additional checks of higher primitives and universal residues."""
import json, platform, time
from pathlib import Path
import sympy as sp
import mpmath as mp
from commensurate import *
from verify import records, exact, numerical, negative
ROOT=Path(__file__).resolve().parents[1]
mp.mp.dps=55
start=time.time();failed=False
_nodes,_weights=mp.gauss_quadrature(32, 'legendre')
def fixed_integral(f,a,b):
    return (b-a)/2*mp.fsum(_weights[j]*f((a+b)/2+(b-a)*_nodes[j]/2) for j in range(32))
def cauchy_first(f,k):
    radius=mp.mpf('.025'); M=48
    return mp.fsum(f(k+radius*mp.exp(2j*mp.pi*j/M))/mp.exp(2j*mp.pi*j/M) for j in range(M))/(M*radius)

try:
    w=sp.symbols('w')
    for d in range(1,7):
        P=sp.prod(w-j for j in range(1,d+1))
        for k in range(1,d+1):
            exact(f'primitive denominator derivative d={d} k={k}',sp.diff(P,w).subs(w,k)-(-1)**(d-k)*sp.factorial(k-1)*sp.factorial(d-k))
    A0,A=mp.mpf('.2'),mp.mpf('.7')
    tab=pole_table((1,2))
    def remainder(w,d):
        return central(tab,w-d,A)-mp.fsum((A-A0)**j/mp.factorial(j)*(-1)**j*rising(w-d,j)*central(tab,w-d+j,A0) for j in range(d))
    for d in [1,2,3]:
        w=mp.mpf('.6')
        formula=(-1)**d*remainder(w,d)/rising(w-d,d)
        direct=fixed_integral(lambda u:(A-u)**(d-1)/mp.factorial(d-1)*central(tab,w,u),A0,A)
        print('primitive check',d,flush=True);numerical(f'anchored primitive d={d} nonresonant',formula,direct)
    for d,k in [(1,1),(2,1),(2,2)]:
        deriv=cauchy_first(lambda w:remainder(w,d),mp.mpf(k))
        formula=(-1)**k*deriv/(mp.factorial(k-1)*mp.factorial(d-k))
        direct=fixed_integral(lambda u:(A-u)**(d-1)/mp.factorial(d-1)*central(tab,k,u),A0,A)
        print('primitive check',d,flush=True);numerical(f'anchored primitive d={d} resonance={k}',formula,direct)
    first=contour((1,1),1,shifts=[0,1],orders=[1,0])
    second=contour((1,1),1,shifts=[0,1],orders=[0,1])
    numerical('unequal-center allocation first',first,mp.zeta(2))
    numerical('unequal-center allocation second',second,mp.zeta(2)-1)
    negative('reject unaligned order addition',first,second)
    for qs in [(1,2),(2,3),(1,4)]:
        A=mp.mpf('.3')
        numerical(f'center reflection at -2 q={qs}',contour(qs,-2,A)-contour(qs,-2,-A),2*A)
    for q in [mp.sqrt(2),mp.mpf(3)]:
        def kernel2(x):
            return mp.mpf(1) if x==0 else x/(-mp.expm1(-x))
        direct=mp.quad(lambda x:kernel2(x)/(1+mp.exp(q*x)),[-mp.inf,0,mp.inf])
        numerical(f'ordinary cubic integral rates=(1,1,{q})',direct,mp.pi**2/12*(2+q**(-2)))
    qs=(1,1,1,2,3)
    exact('printed universal fifth-depth polynomial',odd_resonance(qs,0)-sp.pi**4/720*(7*sum(sp.Rational(q)**(-4) for q in qs)+10*sum(sp.Rational(qs[i])**(-2)*sp.Rational(qs[j])**(-2) for i in range(5) for j in range(i+1,5))))
    numerical('universal fifth-depth contour',contour(qs,0),mval(odd_resonance(qs,0)))
except Exception:
    failed=True;raise
finally:
    counts={k:sum(r['kind']==k for r in records) for k in ['exact','numerical','negative_control']}
    out={'part':'extra','python':platform.python_version(),'sympy':sp.__version__,'mpmath':mp.__version__,'working_decimal_digits':55,'elapsed_seconds':round(time.time()-start,3),'counts':counts,'passed':not failed and all(r['passed'] for r in records),'records':records}
    (ROOT/'verification'/'extra-results.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='records'},indent=2))
