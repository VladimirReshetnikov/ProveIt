#!/usr/bin/env python3
"""Independent exact Bell/IBP verification of the all-index square theorem."""
import json, sys
from pathlib import Path
from fractions import Fraction as Q
from math import factorial
import sympy as s
from algebra import *
ROOT=Path(__file__).resolve().parents[1]
count=0

def check(condition,label):
    global count
    if not condition:
        raise ArithmeticError(label)
    count+=1

A={():Q(1)}; examples={}
for m in range(19):
    N,H=normal_form(A)
    check(add(N,derivative(H))==A,f'full decomposition {m}')
    for mon in N:
        check(not mon or mon[-1]==0 or mon.count(mon[-1])>=2,f'normal support {m}')
        check((len(mon)-m)%2==0,f'factor parity {m}')
    if m<=14:
        examples[str(m)]={'A':serial(A),'N':serial(N),'H':serial(H)}
    for mon,c in N.items():
        high=[j for j in mon if j>=2]
        if len(high)==2:
            r=high[0]
            check(high[1]==r,'equal high pair')
            check(c==square_coefficient(mon.count(0),mon.count(1),r),f'full coefficient {m},{mon}')
    A=next_gamma(A)

rows=[]
for r in range(2,9):
    for k in range(0,9):
        for a in (0,1,3):
            if k+2*r>22:
                continue
            A=bell_sector(a,k,r); N,H=normal_form(A)
            target=(0,)*a+(1,)*k+(r,r)
            expected=square_coefficient(a,k,r)
            check(N.get(target,Q(0))==expected,f'isolated Bell sector {a},{k},{r}')
            check(add(N,derivative(H))==A,f'sector certificate {a},{k},{r}')
            rows.append({'a':a,'k':k,'r':r,'weight':a+2*k+2*r+2,'coefficient':str(expected)})

# Beta integral coefficient, direct expansion rather than 0F1.
for r in range(2,15):
    for l in range(0,18):
        integral=sum(Q((-1)**j*int(s.binomial(r,j)),2*l+2*j+1) for j in range(r+1))
        beta=Q((-1)**r,2**(2*r+1)*factorial(r)*factorial(r+1))*integral/factorial(2*l)
        hyper=Q((-1)**r,factorial(2*r+2))*Q(1,4**l*factorial(l))/Q(s.rf(s.Rational(2*r+3,2),l))
        deriv=Q((-1)**r*factorial(l+r+1),factorial(r+1)*factorial(l)*factorial(2*l+2*r+2))
        check(beta==hyper==deriv,f'kernel coefficients {r},{l}')

# A non-normal projection is not a ring map: a deliberate incorrect rule fails.
check(normal_form({(1,1):Q(1)})[0] != {},'corruption: multiplying discarded derivatives')
check(square_coefficient(0,0,3) != -square_coefficient(0,0,3),'corruption: sign')
(ROOT/'data/gamma_normal_forms.json').write_text(json.dumps(examples,indent=2)+'\n')
(ROOT/'data/derivative_square_coefficients.json').write_text(json.dumps(rows,indent=2)+'\n')
result={'status':'PASS','exact_assertions':count,'full_hierarchy_through_weight':18,
        'isolated_Bell_sectors':len(rows),'kernel_coefficient_cases':13*18,
        'scope':'Finite exact verification; the infinite-family proof is in the article.'}
(ROOT/'data/algebra_results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
