import sympy as s
import json,hashlib
from pathlib import Path
c,r,u=s.symbols('c rho u',real=True)
q1=5*s.I*c*u**3/8
q2=35*c*u**4/64+c**2*(1-r)/2
q3=-63*s.I*c*u**5/128+s.I*c**2*(1-r/4)*u
q4=-231*c*u**6/512-c**2*(s.Rational(1,2)+r/16)*u**2+c*(1+r/2)
def ev(p):
 p=s.Poly(s.expand(p),u);out=0
 for (j,),v in p.terms():
  if j%2==0:out+=v*(s.factorial2(j-1) if j else 1)*(2/(3*c))**(j//2)
 return s.factor(out)
a1=ev(q2+q1*q1/2)
a2=ev(q4+q1*q3+q2*q2/2+q1*q1*q2/2+q1**4/24)
expected=(324*c**6*(r-1)**2+c**3*(1908*r-612)-35)/(2592*c**2)
assert s.simplify(a2-expected)==0
print(json.dumps({'a1':str(a1),'a2':str(a2),'a2_matches':True},indent=2))
