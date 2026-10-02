import json,sympy as s
from pathlib import Path
x,e=s.symbols('x e')
G14=(1-(e-9)*x)*(1-(e-5)*x)*(1-2*e*x+(e*e-32)*x*x)
H14=x*(e-4-s.Rational(1,2)*(7*e*e-50*e+24)*x+(4*e**3-42*e*e+26*e+448)*x*x-s.Rational(3,2)*(e-9)*(e-5)*(e*e-32)*x**3)
G15=(1-(e-1)*x)*(1-(e+11)*x)*(1-2*e*x+(e*e+4)*x*x)
H15=x*(e+2-s.Rational(1,2)*(7*e*e+34*e-8)*x+(4*e**3+30*e*e-14*e+40)*x*x-s.Rational(3,2)*(e-1)*(e+11)*(e*e+4)*x**3)
def get(G,H,r,K,order=6):
 g=s.Poly(s.expand(G),x);h=s.Poly(s.expand(H),x);gs=[K.from_sympy(g.nth(j)) for j in range(g.degree()+1)];hs=[K.from_sympy(h.nth(j)) for j in range(g.degree()+1)];r=K.from_sympy(r)
 D=sum(K(j)*gs[j]*r**j for j in range(1,len(gs)));bs=[K.one]
 def bc(a,j,d):return K.from_sympy(s.rf(a,d)*s.Integer(j)**d/s.factorial(d)) if d>=0 else K.zero
 for m in range(1,order+1):
  z=K.zero
  for k in range(m):
   d=m+1-k
   z+=bs[k]*sum(r**j*(gs[j]*(bc(s.Rational(1,2)+k,j,d)-K(j)/K(2)*bc(s.Rational(1,2)+k,j,d-1))-K(2)*hs[j]*(bc(s.Rational(3,2)+k,j,d-2)-K(j)/K(2)*bc(s.Rational(3,2)+k,j,d-3))) for j in range(len(gs)))
  bs.append(-z/(K(m)*D))
 return [K.to_sympy(y) for y in bs]
