"""Finite regression checks. These are not proof-assistant verification."""
from __future__ import annotations
from fractions import Fraction as F
from pathlib import Path
import json, platform
import sympy as s
from dougall_tail import (L,T,Z,gamma_coefficients,harmonic_sum_coefficient,
                         reduce_even_zetas,rational_divisor,classify,
                         composition_coefficient)
ROOT=Path(__file__).resolve().parents[1]
counts={}
def check(name, condition):
    if not condition: raise AssertionError(name)
    counts[name]=counts.get(name,0)+1

# Independently construct gamma divisors on a finite rational grid.
for N in range(6):
    for kap in (F(j,4) for j in range(1,13)):
        for b in (F(j,4) for j in range(1,29)):
            for c in (F(j,4) for j in range(1,29)):
                d0=1+2*kap-b-c
                if d0<=0: continue
                d=d0+N
                divisor=rational_divisor([kap,b-kap,c-kap,d-kap])
                pred=classify(N,kap,b,c)
                check('rationality_grid',pred['rational']==(divisor is not None))
                finite=divisor is not None and all(e>=0 or a==0 for a,e in divisor.items())
                check('termination_grid',pred['terminates']==finite)

co=gamma_coefficients(7,3)
for m in range(6):
    for k in range(1,4):
        expr=harmonic_sum_coefficient(m,k,co)
        for term in s.Add.make_args(expr):
            powers=term.as_powers_dict()
            weight=powers.get(L,0)+sum(int(str(z)[1:])*p
                    for z,p in powers.items() if str(z).startswith('Z'))
            check('weight_homogeneity',weight==m+2*k+1)

printed={
  1: s.Rational(45,32)*Z(4)-s.Rational(7,4)*L*Z(3),
  2: s.Rational(31,8)*Z(5)-s.Rational(45,8)*L*Z(4)
      +s.Rational(7,2)*L**2*Z(3)-s.Rational(7,8)*Z(2)*Z(3),
  3: -14*L**3*Z(3)+s.Rational(21,2)*L*Z(2)*Z(3)
      -s.Rational(21,4)*Z(3)**2+s.Rational(135,4)*L**2*Z(4)
      -s.Rational(93,2)*L*Z(5)+s.Rational(945,64)*Z(6),
  4: 14*L**4*Z(3)-21*L**2*Z(2)*Z(3)+21*L*Z(3)**2
      -45*L**3*Z(4)+93*L**2*Z(5)-s.Rational(945,16)*L*Z(6)
      -s.Rational(39,2)*Z(3)*Z(4)-s.Rational(93,4)*Z(2)*Z(5)
      +s.Rational(1143,16)*Z(7)}
scales={1:s.Rational(1,2),2:s.Rational(1,2),3:s.Rational(3,2),4:s.Rational(3,2)}
for m in printed:
    check('printed_harmonic_identity',reduce_even_zetas(
        scales[m]*harmonic_sum_coefficient(m,1,co)-printed[m])==0)

u=s.symbols('u')
for n in range(8):
    # Multiply truncated rational factors, without composition enumeration.
    p=[s.Integer(1)]+[s.Integer(0)]*6
    for j in range(1,n+1):
        factor=[s.Integer(1)]+[2*s.Rational((-1)**r,j**r) for r in range(1,7)]
        p=[sum(p[h]*factor[r-h] for h in range(r+1)) for r in range(7)]
    for m in range(7):
        check('finite_composition_identity',p[m]==(-1)**m*composition_coefficient(n,m))

# Derivatives of products at positive integer zeros, no log of zero.
for M in range(1,6):
    for n in range(M,M+6):
        product=s.prod((j-u)/(j+u) for j in range(1,n+1))
        exact=s.diff(product,u).subs(u,M)
        expected=(-1)**M*s.factorial(M)*s.factorial(M-1)*s.factorial(n-M)/s.factorial(n+M)
        check('revived_zero_derivative',s.simplify(exact-expected)==0)

# Formal resolvent coefficients at u=0, independent zeta values.
for k in range(1,4):
    check('unweighted_odd_sum',s.expand(harmonic_sum_coefficient(0,k,co)
       -(1-s.Rational(1,2**(2*k+1)))*Z(2*k+1))==0)

records=[]
for m in range(6):
    for k in range(1,4):
        expr=harmonic_sum_coefficient(m,k,co)
        records.append({'m':m,'k':k,'weight':m+2*k+1,
                        'expression':str(expr),'latex':s.latex(expr)})
(ROOT/'results'/'coefficient_table.json').write_text(json.dumps(records,indent=2)+'\n')
report={'status':'PASS','scope':'finite exact regression, not formal verification',
        'python':platform.python_version(),'sympy':s.__version__,
        'counts':counts,'total_assertions':sum(counts.values())}
(ROOT/'results'/'exact_checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
