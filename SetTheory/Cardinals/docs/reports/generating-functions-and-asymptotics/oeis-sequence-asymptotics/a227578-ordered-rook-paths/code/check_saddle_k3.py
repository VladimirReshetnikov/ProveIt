import sympy as s,json
u,v,t=s.symbols('u v t');I=s.I;q=s.Rational(1,4)
def trunc(e,m):return s.series(e,t,0,m+1).removeO().expand()
x=q*sum((I*t*u)**j/s.factorial(j) for j in range(5)); y=q*sum((I*t*v)**j/s.factorial(j) for j in range(5))
S=trunc(1-x/(1-x)-y/(1-y),4); z=trunc(S/(1+S),4)
f=trunc(I*t*(u+v)+s.log(z/q),4)
B=trunc((1-z)**2/z/((1-x)*(1-y)*(1-z))**2,2)
D=trunc(((x-y)*(x-z)*(y-z)/t**3)**2,2)
amp=trunc(B*D,2)
f3=s.expand(f).coeff(t,3);f4=s.expand(f).coeff(t,4)
poly0=amp.coeff(t,0)
poly1=s.expand(amp.coeff(t,2)-amp.coeff(t,1)*f3+amp.coeff(t,0)*(f3*f3/2-f4))
from functools import lru_cache
C=[[s.Rational(2,5),s.Rational(-1,5)],[s.Rational(-1,5),s.Rational(2,5)]]
@lru_cache(None)
def moment(a,b):
 if (a+b)%2:return s.Integer(0)
 if a+b==0:return s.Integer(1)
 if a:
  return (a-1)*C[0][0]*moment(a-2,b) if b==0 else ((a-1)*C[0][0]*moment(a-2,b) if a>1 else 0)+b*C[0][1]*moment(a-1,b-1)
 return (b-1)*C[1][1]*moment(0,b-2)
def ev(p):return s.expand(sum(c*moment(*powers) for powers,c in s.Poly(s.cancel(p),u,v).terms()))
e1=s.factor(ev(poly1)/ev(poly0));d1=e1-8
print('Hessian',f.coeff(t,2));print('N correction',e1,'n correction',d1)
assert d1==-s.Rational(326,75)
json.dump(dict(phase_quadratic=str(f.coeff(t,2)),N_correction=str(e1),n_correction=str(d1),method='Exact rational Gaussian evaluation from proved rational coefficient formula, not the OEIS recurrence'),open('saddle-k3-check.json','w'),indent=2)
