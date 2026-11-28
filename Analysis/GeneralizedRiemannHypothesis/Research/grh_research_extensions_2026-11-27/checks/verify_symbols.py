#!/usr/bin/env python3
"""Exact symbolic checks for the identities used in the five-observation paper.

Requires SymPy.  Does not search for roots or replace the analytic proofs.
"""
import json
from pathlib import Path
import sympy as S

a,b,c,s,t,z,u,X = S.symbols('a b c s t z u X', real=True)
R=a*a+b*b+c*c
weights=[a,b-2*a,a-2*b+c,b-2*c,c]
assert S.expand(sum(weights))==0
assert S.expand(sum(i*w for i,w in enumerate(weights)))==0
poly=sum(w*z**i for i,w in enumerate(weights))
assert S.expand(poly-(1-z)**2*(a+b*z+c*z**2))==0
lags=[S.expand(sum(weights[i]*weights[i+k] for i in range(5-k))) for k in range(1,5)]
expected=[-4*R+7*b*(a+c)-4*a*c,
          R-4*b*(a+c)+6*a*c,
          b*(a+c)-4*a*c,a*c]
assert all(S.expand(v-w)==0 for v,w in zip(lags,expected))
A=-4+7*s-4*t
B=8-32*s+48*t
C=27*s-108*t
D=64*t
sym=A+B*z+C*u+D*z*z
assert S.expand(sym-(4*(2*z-1)*(1+2*t*(4*z-3))+(s-4*t)*(7-32*z+27*u)))==0
assert S.expand(sym.subs({z:1,u:1})-(4+2*s))==0
corners=[S.expand(sym.subs({z:zz,u:uu})) for zz,uu in [(1,-1),(-1,1),(-1,-1)]]
assert corners==[4-52*s+216*t,-12+66*s-96*t,-12+12*s+120*t]
special=S.factor(sym.subs({s:S.Rational(2,7),t:S.Rational(1,14)}))
assert S.expand(special-S.Rational(16,7)*(z+1)*(2*z-1))==0
AA,BB,CC,DD=S.symbols('AA BB CC DD',real=True)
mod=S.expand((AA+BB*z+DD*z*z)*(AA+BB/z+DD/z**2))
mod2=4*AA*DD*X*X+2*BB*(AA+DD)*X+(AA-DD)**2+BB*BB
assert S.expand(mod-mod2.subs(X,(z+1/z)/2))==0
response=(1+2*s*X+2*t*(2*X*X-1))
assert S.expand(response.subs({s:S.Rational(2,7),t:S.Rational(1,14)})-
                S.Rational(4,7)*(1+(2+2*X)**2/8))==0
result={'status':'PASS','exact_checks':[
 'moment cancellations','quadratic factorization','all four lag autocorrelations',
 'two-shape elimination identity','positive zero-frequency value',
 'three robustness lines','unique infinite-shape factorization',
 'quadratic unit-circle modulus','special two-scale kernel identity'],
 'lags':[str(x) for x in lags], 'corner_lines':[str(x) for x in corners]}
print(json.dumps(result,indent=2))
out=Path(__file__).resolve().parent.parent/'verification'/'symbol_checks.json'
out.parent.mkdir(parents=True,exist_ok=True)
out.write_text(json.dumps(result,indent=2)+'\n')
