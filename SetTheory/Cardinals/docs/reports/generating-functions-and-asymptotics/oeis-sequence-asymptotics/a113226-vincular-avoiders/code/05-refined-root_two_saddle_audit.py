import sympy as s
import json
X,V,c1,c2,d1,f3,a1,a2=s.symbols('X V c1 c2 d1 f3 a1 a2')
P1=3*s.I*c1*X
P3=-s.I*f3*X**3/6+s.I*d1*X
P4=-3*c2*X**2/2
def E(p):
 out=0
 for (k,),v in s.Poly(s.expand(p),X).terms():
  if k%2==0:out+=v*(s.factorial2(k-1) if k else 1)/V**(k//2)
 return s.factor(out)
b1=E(a1+P1**2/2)
b2=E(a2+a1*P1**2/2+P4+P1*P3+P1**4/24)
assert s.simplify(b1-(a1-9*c1*c1/(2*V)))==0
assert s.simplify(b2-(a2-9*a1*c1*c1/(2*V)+81*c1**4/(8*V**2)-3*c2/(2*V)-3*c1*d1/V+3*c1*f3/(2*V**2)))==0
print(json.dumps({'b1':str(b1),'b2':str(b2),'both_verified':True},indent=2))
