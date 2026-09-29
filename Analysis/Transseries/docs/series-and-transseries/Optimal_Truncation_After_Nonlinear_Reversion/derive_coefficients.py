#!/usr/bin/env python3
"""Symbolic audit of the first two exponentially small error coefficients."""
from pathlib import Path
import sympy as sp
r,d,e,sigma,u=sp.symbols('r d e sigma u')
pi=sp.pi
J=3
f=1/(1+u**2)
mean=0
for j in range(2*J+1):
    mu=sp.expand(sum(sp.binomial(j,l)*(-1)**(j-l)*sp.rf(1/r+d,l)*r**l for l in range(j+1)))
    mean += sp.diff(f,u,j).subs(u,1)/sp.factorial(j)*mu
mean=sp.series(mean,r,0,J+1).removeO().expand()
lg=sum((-1)**(j+1)*sp.bernoulli(j+1,d)/(j*(j+1))*r**j for j in range(1,J+1))
st=sp.series(sp.exp(lg),r,0,J+1).removeO().expand()
G=sp.series(2*mean*st,r,0,J+1).removeO().expand()
print('gamma remainder coeffs',[sp.factor(G.coeff(r,i)) for i in range(J+1)])
c1=sp.Rational(1,24);h1=-c1;h2=sp.Rational(3,640)
v=1+h1*e**2+h2*e**4 # w/X
rr=e/(2*pi*v)
dd=2*sigma+2*pi*(1-v)/e
B=sp.series(G.subs({r:rr,d:dd}),e,0,3).removeO()
B=sp.series(B*sp.sqrt(v)*sp.exp(2*pi*(1-v)/e)/(1-2*c1*(e/v)**2),e,0,3).removeO().expand()
print('B1',sp.factor(B.coeff(e,1)))
print('B2',sp.factor(B.coeff(e,2)))
cut1=pi/6
cut2=sigma**2/6-sigma/4+sp.Rational(25,144)
D1=sp.factor(B.coeff(e,1)-cut1)
D2=sp.factor(B.coeff(e,2)-cut2)
print('D1',D1)
print('D2',D2)
print('D2 latex',sp.latex(sp.expand(D2)))
Path(__file__).with_name('symbolic_results.txt').open('w').write('B1 = '+str(sp.factor(B.coeff(e,1)))+'\nB2 = '+str(sp.factor(B.coeff(e,2)))+'\nD1 = '+str(D1)+'\nD2 = '+str(D2)+'\n')

# The corrected next-term weight is D(sigma)/(D(sigma)+D(sigma+1)).
Den=2+(D1+D1.subs(sigma,sigma+1))*e+(D2+D2.subs(sigma,sigma+1))*e**2
Theta=sp.series((1+D1*e+D2*e**2)/Den,e,0,3).removeO().expand()
print('theta1 =',sp.factor(Theta.coeff(e,1)))
print('theta2 =',sp.factor(Theta.coeff(e,2)))
assert sp.simplify(Theta.coeff(e,1)-(1-4*sigma)/(8*pi))==0
assert sp.simplify(B.coeff(e,1)-(pi/12+(2*sigma**2-3*sigma+sp.Rational(7,12))/(2*pi)))==0
assert sp.simplify(D1-(-pi/12+(2*sigma**2-3*sigma+sp.Rational(7,12))/(2*pi)))==0
D2_expected = (sigma**4/(2*pi**2)-11*sigma**3/(6*pi**2)
    -sigma**2/12+5*sigma**2/(3*pi**2)+sigma/(48*pi**2)
    +5*sigma/24-sp.Rational(43,288)-sp.Rational(203,1152)/pi**2+pi**2/288)
theta2_expected = (24*sigma**2+12*sigma-9-2*pi**2)/(96*pi**2)
assert sp.simplify(D2-D2_expected) == 0
assert sp.simplify(Theta.coeff(e,2)-theta2_expected) == 0
# An independent gamma-ratio expansion for the leading cutoff diagonal.
# Its normalized form is 2*c1*((2*M+1)/X^2) times the gamma amplitude at M.
dm=2*sigma-2
shift1=dm*(dm-1)/2+sp.Rational(1,12)
cut2_independent=sp.expand(2*c1*((2*sigma-1)+shift1))
assert sp.simplify(cut2_independent-cut2)==0
print('All symbolic assertions passed (B1, D1, D2, theta1, theta2, cutoff2).')
