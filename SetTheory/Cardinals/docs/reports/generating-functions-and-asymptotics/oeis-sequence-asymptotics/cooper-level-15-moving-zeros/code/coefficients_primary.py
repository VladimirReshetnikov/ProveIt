import sympy as s,json
from pathlib import Path
x=s.symbols('x');
CASES={
 '11':(11,1-20*x+56*x*x-44*x**3,4*x*(1-8*x+11*x*x),1-20*x+56*x*x-44*x**3),
 '14A':(14,(1+4*x)*(1-10*x-7*x*x),x*s.Rational(1,2)*(2+51*x+56*x*x),1-10*x-7*x*x),
 '14B':(14,(1-4*x)*(1-18*x+49*x*x),x*s.Rational(1,2)*(10-141*x+392*x*x),1-18*x+49*x*x),
 '15A':(15,(1-12*x)*(1-2*x+5*x*x),3*x*s.Rational(1,2)*(2-11*x+40*x*x),1-12*x),
 '24':(24,(1+4*x)*(1-4*x)*(1-8*x),2*x*(1+5*x-64*x*x),1-8*x)}
def coeffs(name,K=6):
 N,G,H,P=CASES[name];G=s.Poly(G,x);H=s.Poly(H,x);P=s.Poly(P,x)
 def red(y):
  a,b=s.cancel(y).as_numer_denom(); return s.rem(s.Poly(a,x)*s.invert(s.Poly(b,x),P),P).as_expr()
 gs=[G.nth(j) for j in range(G.degree()+1)];hs=[H.nth(j) for j in range(G.degree()+1)]
 D=red(x*s.diff(G.as_expr(),x));bs=[s.Integer(1)]
 def bincoef(alpha,j,d):return s.rf(alpha,d)*s.Integer(j)**d/s.factorial(d) if d>=0 else 0
 def ac(j,k,d):
  return gs[j]*(bincoef(s.Rational(1,2)+k,j,d)-s.Rational(j,2)*bincoef(s.Rational(1,2)+k,j,d-1))-2*hs[j]*(bincoef(s.Rational(3,2)+k,j,d-2)-s.Rational(j,2)*bincoef(s.Rational(3,2)+k,j,d-3))
 for m in range(1,K+1):
  z=sum(bs[k]*sum(x**j*ac(j,k,m+1-k) for j in range(len(gs))) for k in range(m))
  bs.append(red(-z/(m*D)))
 return bs
