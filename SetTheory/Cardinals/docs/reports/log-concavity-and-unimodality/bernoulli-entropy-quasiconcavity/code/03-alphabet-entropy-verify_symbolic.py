#!/usr/bin/env python3
"""Symbolic identity diagnostics; requires SymPy, not a proof assistant."""
from pathlib import Path
import sympy as s

ROOT=Path(__file__).resolve().parents[1]
y,K,lam,h=s.symbols('y K lam h',positive=True)
checks=[]
def zero(expr,label):
    if s.simplify(expr)!=0: raise AssertionError(label)
    checks.append(label)
R=(y+K)*(y**3+K)/(y*y+K)**2
zero(s.diff(R,y)+K*(y-1)*(y**3-3*y*y-3*K*y+K)/(y*y+K)**3,
     'half-order optimizer cubic')
z=4+(lam**2-32)*h**2/3
small=h*z
r=s.sinh(lam*h*(1+h*small)/2)**2/s.cosh(small/2)**2
rseries=s.series(r,h,0,7).removeO().expand()
zero(rseries.coeff(h,2)-lam**2/4,'window power sum leading term')
zero(rseries.coeff(h,4)-(lam**2+lam**4/48),'window power sum correction')
# This coefficient does not require the next term of z, by stationarity.
zero(rseries.coeff(h,6)-(lam**6/1440+lam**4/4-4*lam**2/3),
     'window power sum second correction')
rr=lam**2*h**2/4+(lam**2+lam**4/48)*h**4
th=(1-lam*h*h)*(rr/(lam*h*h+rr))
tseries=s.series(th,h,0,4).removeO().expand()
zero(tseries.coeff(h,0)-lam/(4+lam),'window profile limit')
zero(tseries.coeff(h,2)-(16*lam-4*lam**2-s.Rational(2,3)*lam**3)/(lam+4)**2,
     'window profile correction')
x=s.symbols('x',real=True)
g=(s.sqrt(81+17*x)+17*s.sqrt(1-x))/s.sqrt(98)
zero(s.diff(2*(g**3-1),x,2).subs(x,0)-s.Rational(10387,83349)*s.sqrt(2),
     'eighteen-symbol second derivative')
text='PASS: '+str(len(checks))+' symbolic identities\n'+'\n'.join(checks)+'\n'
(ROOT/'verification'/'symbolic_checks.txt').write_text(text)
print(text,end='')
