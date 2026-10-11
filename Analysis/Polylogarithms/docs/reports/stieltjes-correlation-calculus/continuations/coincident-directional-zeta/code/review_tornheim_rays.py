#!/usr/bin/env python3
"""Independent symbolic review of the spectral agent's ray coefficients."""
from pathlib import Path
import sympy as S
import json
p=Path(__file__).resolve().parents[1]
a,b,c,t,g,l,z2,zp1,zpp0,zpp1=S.symbols('a b c t gamma L zeta2 zetaPrimeMinus1 zetaSecond0 zetaSecondMinus1')
h0=zp1+l/2-S.Rational(5,12)*g
hc=(zpp1-zpp0)/2-g*(zp1+l/2)+S.Rational(5,24)*(g*g+z2)
ha=l*l/8-zpp0/2+g*zp1-g*l/4-(g*g+z2)/24
gam=lambda x: 1+g*x+(g*g+z2)*x*x/2
zet0=lambda x: -S.Rational(1,2)-l*x/2+zpp0*x*x/2
zet1=lambda x: -S.Rational(1,12)+zp1*x+zpp1*x*x/2
raw=(zet0(a*t)*zet0(b*t)-c/(a+c)*gam(a*t)*zet1(b*t)-c/(b+c)*gam(b*t)*zet1(a*t)+c*t*(h0+ha*(a+b)*t+hc*c*t))
ans=S.expand(raw*(1+g*c*t+(g*g-z2)*c*c*t*t/2))
B=c*(c*c+a*b-a*a-b*b)/((a+c)*(b+c))
expected=[S.Rational(1,4)+c/(12*(a+c))+c/(12*(b+c)),(a+b+2*c)*l/4+B*zp1,((2*a*b+c*(a+b))*l*l/4-(a*a+b*b+2*c*(a+b)+2*c*c)*zpp0/2+(a+b+c)*B*zpp1)/2]
rows=[]
for k in range(3):
 residual=S.factor(ans.coeff(t,k)-expected[k])
 rows.append({'coefficient':k,'residual':str(residual),'pass':residual==0})
# Independent diagonal equation: cubic residue fixes its second derivative.
x0,x1,x2=S.symbols('x0 x1 x2')
A=1-(g+l)*t+((g+l)**2+z2)*t*t/2
rhs=S.expand(6*A**3*(1-3*z2*t*t/4)*(x0+x1*t+x2*t*t/2)+6*A*A*(-S.Rational(1,2)-l*t+2*zpp0*t*t)+1)
sol=S.solve([rhs.coeff(t,0),rhs.coeff(t,1),rhs.coeff(t,2)-(3*g*g-S.Rational(3,2)*z2)],[x0,x1,x2])
rows.append({'diagonal_solution':{str(k):str(S.factor(v)) for k,v in sol.items()},'pass':all(S.simplify(sol[k]-v)==0 for k,v in [(x0,S.Rational(1,3)),(x1,l),(x2,l*l-4*zpp0)])})
(p/'results'/'tornheim_peer_review.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(rows,indent=2))
