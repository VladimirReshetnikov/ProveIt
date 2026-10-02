import sympy as s
from math import comb
from block_formula import C
v=s.symbols('v')
for j in range(1,15):
 N=1 if j==1 else sum(s.Rational(comb(j-1,l)*comb(j-1,l+1),j-1)*v**l for l in range(j-1))
 F=N/(1-v)**(2*j-1)
 ode=v*(1-v)*s.diff(F,v,2)+(2-(2*j+2)*v)*s.diff(F,v)-j*(j+1)*F
 assert s.factor(ode)==0
 if j>=2:
  for l in range(j-2):
   nl=s.expand(N).coeff(v,l);nx=s.expand(N).coeff(v,l+1)
   assert (l+1)*(l+2)*nx==(l+2-j)*(l+1-j)*nl
 print('j',j,'fixed-gap rational formula ODE PASS')
print('PASS all fixed-gap rational identities')
