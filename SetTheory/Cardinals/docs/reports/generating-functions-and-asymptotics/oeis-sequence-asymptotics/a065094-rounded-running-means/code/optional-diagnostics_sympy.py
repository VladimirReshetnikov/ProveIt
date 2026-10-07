#!/usr/bin/env python3
"""Optional independent symbolic diagnostics, not an asymptotic or interval proof."""
import sys
sys.dont_write_bytecode=True
import sympy as s
from fractions import Fraction

def check(condition, message):
    if not condition: raise RuntimeError(str(message))
h=s.symbols('h'); order=11
c=[s.S(1),-s.Rational(17,48),s.Rational(649,4608),-s.Rational(56533,3317760),s.Rational(7946069,637009920),s.Rational(937900373,42807066624),s.Rational(2719850722091,308210879692800)]
# Compute the normalized forward/backward ratio via logarithms,
# a distinct route from expanding each amplitude directly.
C=sum(x*h**j for j,x in enumerate(c))
logC=s.series(s.log(C),h,0,7).removeO()
ratios=[]
for sign in [1,-1]:
    v=1+sign*h*h
    logratio=(2/h)*(s.sqrt(v)-1)-s.log(v)/4
    for j in range(1,7):logratio+=logC.coeff(h,j)*h**j*(v**(-s.Rational(j,2))-1)
    logratio=s.series(logratio,h,0,10).removeO()
    ratios.append(s.series(s.exp(logratio),h,0,10).removeO())
res=s.expand(ratios[0]+(1-h*h)*ratios[1]-2)
check(all(res.coeff(h,j)==0 for j in range(10)), res)
print('P coefficients through c6 satisfy recurrence to h^9:',c)
# Direct compose the claimed inverse n(t) into log(a_n / (D e^t/sqrt(t))).
t=s.symbols('t',positive=True)
B=[s.Rational(17,48),s.Rational(1,48),-s.Rational(539,2880),-s.Rational(51,640),-s.Rational(25517,241920)]
# t=1/h, n=t^2/4+sum B_j/t^j; ratio sqrt(n)/(t/2) = sqrt(v).
v=1+4*sum(B[j]*h**(j+2) for j in range(5))
# log leading ratio: 2 sqrt(n)-t -1/4 log(4n/t²)
r=s.series((s.sqrt(v)-1)/h-s.log(v)/4,h,0,6).removeO()
for j in range(1,6):r+=s.series(logC.coeff(h,j)*(2*h)**j*v**(-s.Rational(j,2)),h,0,6).removeO()
r=s.expand(r)
check(all(r.coeff(h,j)==0 for j in range(6)), r)
print('Inverse coefficients verified by direct composition through t^-5:',B)
print('log coefficients:',logC)
