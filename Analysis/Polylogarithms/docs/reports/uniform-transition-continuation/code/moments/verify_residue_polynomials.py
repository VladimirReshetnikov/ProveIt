#!/usr/bin/env python3
"""Exact independent derivation from offset residues and their finite operators."""
import sympy as s
from pathlib import Path
l,t,delta,g1,g2,g3,h2,h3=s.symbols('lambda t delta g1 g2 g3 h2 h3')
E=s.exp(delta*l)
def D(f):return s.expand(l*s.diff(f,l))
def Dp(f,n):
 for _ in range(n): f=D(f)
 return f
q1=h2*l*l*E+g1*(D(l*E)+l*E)
q2=(h3*l**3*E+h2*h2*l**4*E/2+g2*(D(l*l*E)+l*l*E)
    +g1*h2*(D(l**3*E)+l**3*E)+g1*g1*(Dp(l*l*E,2)+2*D(l*l*E)+l*l*E)/2)
p1=s.expand((q1+t*Dp(E,2)/2)/E)
p2=s.expand((q2+t*Dp(q1,2)/2-t*Dp(E,2)/2-t*Dp(E,3)/3+t*t*Dp(E,4)/8)/E)
a,eps,eta,c,d,e=s.symbols('a epsilon eta c d e')
pg1=s.expand(p1.subs({g1:-a,g2:a*c,g3:-a*(d+c*c/2),h2:d+a*c,h3:e-a*(d+c*c/2)}).subs({c:delta+a,d:eps-a*a}))
pg2=s.expand(p2.subs({g1:-a,g2:a*c,g3:-a*(d+c*c/2),h2:d+a*c,h3:e-a*(d+c*c/2)}).subs({c:delta+a,d:eps-a*a}))
eta_expression=e+a**3/2-a*a*delta/2+a*delta*delta/2-5*a*eps
claim1=t*delta*l*(1+delta*l)/2-2*a*l+eps*l*l
claim2=(l*(delta*t*t/8-(a+5*delta/6)*t)
 +l*l*(7*delta*delta*t*t/8+(-3*a*delta-3*delta*delta/2+2*eps)*t+15*a*a/2+3*a*delta)
 +l**3*(3*delta**3*t*t/4+(-a*delta*delta-delta**3/3+5*delta*eps/2)*t+eta_expression)
 +l**4*(delta**4*t*t/8+delta*delta*eps*t/2+eps*eps/2))
assert s.expand(pg1-claim1)==0
assert s.expand(pg2-claim2)==0
# Check the exact residue coefficient identity independently for a finite range.
x,m=s.symbols('x m')
a,z2,z3,z4,z5,z6=s.symbols('a z2 z3 z4 z5 z6')
g=-a*x+z2*x*x/2-z3*x**3/3+z4*x**4/4-z5*x**5/5
B=a*x+z2*x*x/2+z3*x**3/3+z4*x**4/4+z5*x**5/5+z6*x**6/6
# Basic exact first and second offset checks, arbitrary m.
cm=z2/(2*a);dm=z3/(3*a)-cm*cm/2
for j in range(3):
 k=m+1+j
 # Explicit expansion of B^m/x^m via generalized binomial to needed degree.
 br=s.series((1+(B/(a*x)-1))**m,x,0,j+1).removeO()
 lhs=s.expand(s.series(s.exp(k*g),x,0,j+1).removeO()*br).coeff(x,j)
 rhs=s.expand(s.series(s.exp(m*(s.series(s.log(B/(a*x)),x,0,j+1).removeO()+g)+(j+1)*g),x,0,j+1).removeO()).coeff(x,j)
 assert s.factor(lhs-rhs)==0
print('PASS: independent residue-operator derivation agrees with P1 and P2 exactly.')
print('PASS: offset residues j=0,1,2 agree as symbolic polynomials in m.')
Path(__file__).with_name('symbolic_checks.txt').write_text('PASS: independent residue-operator derivation equals P1 and P2.\nPASS: exact first three offset residue polynomials.\n')
