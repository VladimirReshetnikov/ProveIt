#!/usr/bin/env python3
"""Exact beta--Bernoulli transport and selector coefficient checks."""
import json
from pathlib import Path
import sympy as S
ROOT=Path(__file__).resolve().parents[1]
v=S.symbols('v'); count=0

def check(ok,label):
    global count
    if not ok: raise ArithmeticError(label)
    count+=1


def P(r):
    return S.bernoulli(2*r,(v+1)/2)-S.bernoulli(2*r)

for r in range(2,15):
    transported=(-1)**r*2**(2*r)*sum(S.binomial(r,2*j-r-1)*P(j)/j for j in range(2,r+1))
    check(S.expand(transported-(1-v*v)**r)==0,f'beta--Bernoulli r={r}')
    for j in range(2,r+1):
        expected=S.factorial(2*r)/2**(2*r) if j==r else 0
        check(S.diff(P(r),v,2*j-1).subs(v,1)==expected,f'odd-derivative diagonal {r},{j}')
    L0=S.Rational(r,2**(2*r-2))*S.zeta(1-2*r)
    for j in range(2,2*r+1):
        d=S.factorial(2*r)*S.bernoulli(2*r-j,1)/(2**j*S.factorial(2*r-j))
        L0+=(-1)**j*d/S.factorial(j)*(1+2**j)
    check(S.factor(L0)==-2*S.bernoulli(2*r),f'selector Stieltjes residue r={r}')

for R in range(2,13):
    weight=(1-v*v)**2*sum(S.Rational((-1)**j*(j+1),j+2)*v**(2*j) for j in range(R-1))
    reconstruction=sum(2**(2*r)*S.diff(weight,v,2*r-1).subs(v,1)/S.factorial(2*r)*P(r) for r in range(2,R+1))
    check(S.expand(weight-reconstruction)==0,f'general selector inverse R={R}')

# The convention B_1(1)=+1/2 is essential to the nonlocal coefficient.
check(S.bernoulli(1,1)!=S.bernoulli(1,0),'mutation: wrong Bernoulli endpoint')
result={'status':'PASS','exact_assertions':count,'beta_indices':'2..14',
        'generic_inverse_max_degree':24,
        'scope':'Finite algebra checks; functional independence uses the article proof, not numerical tests.'}
(ROOT/'data/selector_results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
