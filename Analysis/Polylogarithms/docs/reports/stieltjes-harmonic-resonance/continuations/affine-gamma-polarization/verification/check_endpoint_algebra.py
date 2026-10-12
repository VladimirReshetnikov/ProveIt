#!/usr/bin/env python3
"""Exact endpoint, residue, harmonic-coefficient and Bernoulli checks."""
import json
from pathlib import Path
import sympy as S
ROOT=Path(__file__).resolve().parents[1]
v,e=S.symbols('v e')
count=0

def check(ok,label):
    global count
    if not ok: raise ArithmeticError(label)
    count+=1


def homogeneous(j,m):
    h=[S.S.One]
    for n in range(1,m+1):
        h.append(S.factor(sum(S.harmonic(j,k)*h[n-k] for k in range(1,n+1))/n))
    return h


def bernoulli_rational(r):
    out=0
    for j in range(2,2*r+1):
        d=S.factorial(2*r)*S.bernoulli(2*r-j,1)/(S.factorial(2*r-j)*2**j)
        out-=(-1)**j*d/S.factorial(j-1)*(S.harmonic(j-1)-1)*(1+2**(j-1))
    return S.factor(out)

for r in range(2,15):
    P=(1-v*v)**r
    for j in range(2*r+1):
        expected=0 if j<r else (-1)**r*S.factorial(j)*S.binomial(r,j-r)*2**(2*r-j)
        check(S.diff(P,v,j).subs(v,1)==expected,f'endpoint derivative {r},{j}')
        check(S.diff(P,v,j).subs(v,-1)==(-1)**j*expected,f'reflected derivative {r},{j}')
    for aa,bb in [(S.Rational(2),S.Rational(1)),(S.Rational(7,3),S.Rational(1,2)),(S.Rational(5,4),S.Rational(1,4))]:
        res=0
        for j in range(r,2*r+1):
            D=(-1)**j*S.binomial(r,j-r)/(2**(j+2)*S.factorial(r)*S.factorial(r+1)*bb**(j+1))
            F=(-S.bernoulli(j+1,aa+bb)+(-1)**j*S.bernoulli(j+1,aa-bb))/(j+1)
            res-=D*F
        check(S.factor(res)==S.Rational((-1)**r,S.factorial(2*r+2)),f'residue {r},{aa},{bb}')

for j in range(1,21):
    hs=homogeneous(j,8)
    # Independent multiplication of finite geometric coefficient vectors.
    direct=[S.S.One]+[S.S.Zero]*8
    for k in range(1,j+1):
        direct=[sum(direct[n-l]/S.Integer(k)**l for l in range(n+1)) for n in range(9)]
    for m in range(9):
        check(S.factor(direct[m]-hs[m])==0,f'complete homogeneous {j},{m}')

rows=[]
for r in range(2,13):
    P=S.bernoulli(2*r,(v+1)/2)-S.bernoulli(2*r)
    for point in [-1,1]:
        check(P.subs(v,point)==0,f'Bernoulli endpoint {r},{point}')
        check(S.diff(P,v).subs(v,point)==0,f'Bernoulli first derivative {r},{point}')
    odds=[]
    for j in range(3,2*r,2):
        d=S.diff(P,v,j).subs(v,1)
        if d: odds.append(j)
    check(odds==[2*r-1],f'single odd derivative {r}')
    logcoef=sum((-1)**j*S.diff(P,v,j).subs(v,1)*2**(j-1)/S.factorial(j-1) for j in range(2,2*r+1))
    check(S.factor(logcoef)==0,f'log cancellation {r}')
    rows.append({'r':r,'rational':str(bernoulli_rational(r)),
                 'zeta_derivative_coefficient':str(-S.Rational(r*(2*r-1),2**(2*r-2))),
                 'odd_zeta_coefficient_without_pi':str(S.Rational((-1)**r*S.factorial(2*r),2**(4*r-2))),
                 'pi_denominator_power':2*r-2})

# Deliberately omit the j! factor of the endpoint derivative in the r=2 case.
r=2; aa=2; bb=1
wrong=0
for j in range(r,2*r+1):
 D=(-1)**j*S.binomial(r,j-r)/(2**(j+2)*S.factorial(r)*S.factorial(r+1)*S.factorial(j))
 F=(-S.bernoulli(j+1,aa+bb)+(-1)**j*S.bernoulli(j+1,aa-bb))/(j+1)
 wrong-=D*F
check(wrong!=S.Rational(1,720),'corruption: missing factorial is rejected')
(ROOT/'data/bernoulli_trigamma_constants.json').write_text(json.dumps(rows,indent=2)+'\n')
result={'status':'PASS','exact_assertions':count,'beta_indices':'2..14',
        'harmonic_coefficients':'j=1..20, degree=0..8',
        'bernoulli_indices':'2..12','scope':'Finite exact checks, not a replacement for the proofs.'}
(ROOT/'data/endpoint_algebra_results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
