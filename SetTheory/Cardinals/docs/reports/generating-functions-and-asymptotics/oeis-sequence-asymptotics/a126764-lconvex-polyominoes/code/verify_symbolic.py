#!/usr/bin/env python3
"""Symbolic checks of finite identities and expansion coefficients.
Requires sympy and mpmath; the main exact checker uses only the standard library.
"""
from __future__ import annotations
import csv,json
from pathlib import Path
import sympy as s
import mpmath as mp

q,w,t,A=s.symbols('q w t A', positive=True)
Q=[s.Integer(1),s.Integer(2)]
h=[s.Integer(1),s.Integer(1)]
for n in range(1,6):
    Q.append(s.expand(2*Q[-1]-(1-q**n)**2*Q[-2]))
    h.append(s.expand(2*h[-1]-(1-q**n)**2*h[-2]))
for n in range(6):
    assert s.expand(h[n]*Q[n+1]-h[n+1]*Q[n]-s.prod((1-q**j)**2 for j in range(1,n+1)))==0
assert s.expand(Q[3]+2*(q+1)*(q**3-q**2-2))==0
D=s.series(h[5].subs(q,1-w)/Q[5].subs(q,1-w),w,0,9).removeO()
F=s.series(4*D.subs(w,1-s.exp(-t))**2,t,0,9).removeO().expand()
expected=1-t**2/2+t**3/2-s.Rational(41,48)*t**4+s.Rational(7,4)*t**5-s.Rational(6317,1440)*t**6+s.Rational(1529,120)*t**7-s.Rational(1702513,40320)*t**8
assert s.expand(F-expected)==0
S=s.series(s.exp(-t/6)*F,t,0,4).removeO()
coefs=[]
for ell in range(4):
    value=0
    for j in range(ell+1):
        k=ell-j; nu=s.Rational(5,2)+j
        b=s.prod(4*nu**2-(2*r-1)**2 for r in range(1,k+1))*(-1)**k/(s.factorial(k)*8**k)
        value+=S.coeff(t,j)*A**(s.Rational(j,2))*b/(2*s.sqrt(A))**k
    coefs.append(s.simplify(value))
expected_coefs=[1,-s.sqrt(A)/6-s.Rational(3,2)/s.sqrt(A),
                s.Rational(1,2)+s.Rational(3,4)/A-s.Rational(35,72)*A,
                s.Rational(755,1296)*A**s.Rational(3,2)+s.Rational(175,72)*s.sqrt(A)-s.Rational(5,8)/s.sqrt(A)]
assert all(s.simplify(x-y)==0 for x,y in zip(coefs,expected_coefs))
base=Path(__file__).parent
(base/'checks'/'symbolic_checks.txt').write_text('All symbolic assertions passed.\nQ3='+str(Q[3])+'\nh3='+str(h[3])+'\n4D(t)^2='+str(F)+'\nCoefficient corrections='+str(coefs)+'\n')
mp.mp.dps=60
AA=13*mp.pi**2/24; B=2*mp.sqrt(AA); c=13*mp.sqrt(2)/768
d=mp.sqrt(AA)/6+3/(2*mp.sqrt(AA))
e=mp.mpf('0.5')+3/(4*AA)-35*AA/72
f=755*AA**mp.mpf('1.5')/1296+175*mp.sqrt(AA)/72-5/(8*mp.sqrt(AA))
Dconst=B*d
alpha2=B**2*(e-d*d/2)
alpha3=B**3*(f+d*e-d**3/3)
rows=[]
with (base/'checks'/'coefficients.csv').open() as fh:
    for row in csv.DictReader(fh):
        n=int(row['n'])
        if n not in [50,100,200,500,1000,2000]:continue
        an=mp.mpf(row['a_n']);pn=mp.mpf(row['p_n'])
        lead=c*mp.exp(B*mp.sqrt(n))/mp.mpf(n)**mp.mpf('1.5')
        factors=[1,1-d/mp.sqrt(n),1-d/mp.sqrt(n)+e/n,1-d/mp.sqrt(n)+e/n+f/mp.mpf(n)**mp.mpf('1.5')]
        L=mp.log(an/(c*B**3))
        s0=-3*mp.lambertw(-mp.exp(-L/3)/3,-1)
        inv0=s0*s0/B**2
        inv1=(s0*s0+2*Dconst+2*(3*Dconst-alpha2)/s0+(18*Dconst-6*alpha2-Dconst**2-2*alpha3)/s0**2)/B**2
        rows.append([n]+[mp.nstr(an/(lead*v),14) for v in factors]+[mp.nstr(n*(1-4*an/pn),14),mp.nstr(inv0-n,12),mp.nstr(inv1-n,12)])
with (base/'checks'/'expanded_table.csv').open('w',newline='') as fh:
    writer=csv.writer(fh);writer.writerow(['n','exact_over_leading','exact_over_2terms','exact_over_3terms','exact_over_4terms','scaled_deficit','inverse_leading_error','inverse_corrected_error']);writer.writerows(rows)
print('All symbolic assertions passed.')
print('coefficients:',mp.nstr(-d,18),mp.nstr(e,18),mp.nstr(f,18))
print('deficit limit:',mp.nstr(AA/2,18))
for row in rows:print(row)
