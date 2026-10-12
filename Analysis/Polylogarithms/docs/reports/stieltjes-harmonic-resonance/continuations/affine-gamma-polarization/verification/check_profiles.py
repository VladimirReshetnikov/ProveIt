#!/usr/bin/env python3
"""Test the arbitrary symmetric-profile theorem against exact IBP reduction."""
from fractions import Fraction as Q
from collections import Counter
from pathlib import Path
from math import factorial
import json
import sympy as S
from algebra import partitions, normal_form
ROOT=Path(__file__).resolve().parents[1]
h,y,w,z=S.symbols('h y w z')
count=0; cases=[]
profiles=[{0:Q(1),2:Q(1,3),4:Q(-2,5)},
          {0:Q(1),2:Q(1,24),4:Q(1,1920),6:Q(1,322560)},
          {0:Q(1),4:Q(2),8:Q(-1,7)}]
for idx,coeff in enumerate(profiles):
    K=sum(S.Rational(c.numerator,c.denominator)*z**j for j,c in coeff.items())
    raw=S.Poly(S.expand(K.subs(z,h-y)*K.subs(z,h+y)/2),h)
    if any(m[0]%2 for m,c in raw.terms() if c): raise ArithmeticError('Not even in h')
    symbol=S.expand(sum(c*(y*y-w)**(m[0]//2) for m,c in raw.terms()))
    for r in range(2,7):
        for k in range(5):
            d=k+2; n=k+2*r; weight=d+n
            A={}
            for part in partitions(n):
                if len(part)>d: continue
                mon=(0,)*(d-len(part))+part
                c=Q(factorial(weight))
                for j,mult in Counter(mon).items():
                    c *= coeff.get(j,Q(0))**mult/factorial(mult)
                if c: A[mon]=c
            N,_=normal_form(A)
            observed=N.get((1,)*k+(r,r),Q(0))
            predicted=S.expand(symbol).coeff(w,r).coeff(y,k)*S.factorial(weight)/2**k
            if observed!=predicted: raise ArithmeticError((idx,r,k,observed,predicted))
            count+=1; cases.append({'profile':idx,'r':r,'k':k,'coefficient':str(observed)})
result={'status':'PASS','exact_assertions':count,'profiles':3,'scope':'Finite independent check of the general-profile theorem.'}
(ROOT/'data/profile_results.json').write_text(json.dumps(result,indent=2)+'\n')
(ROOT/'data/profile_coefficients.json').write_text(json.dumps(cases,indent=2)+'\n')
print(json.dumps(result,indent=2))
