import json
from pathlib import Path
import sympy as s
x,z=s.symbols('x z');cumul=s.log(1+z)
answers={}
for r in range(1,5):
 cumul=s.diff(cumul,z)*z
 h=s.cancel((-x)**r*cumul.subs(z,x**2))
 num,den=s.fraction(h);pol,rem=s.div(num,den,x);partial=0;value=0
 for mon,c in s.Poly(pol,x).terms():value+=c*s.zeta(-mon[0])
 for root in (s.I,-s.I):
  analytic=s.cancel((x-root)**r*h)
  for j in range(1,r+1):
   coeff=s.simplify(s.diff(analytic,x,r-j).subs(x,root)/s.factorial(r-j))
   partial+=coeff/(x-root)**j
   f=s.log(-root)-s.digamma(1-root) if j==1 else s.zeta(j,1-root)-(-root)**(1-j)/s.Integer(j-1)
   value+=coeff*f
 if s.cancel(h-pol-partial)!=0:raise ValueError('Partial fractions failed')
 value=s.expand(value/s.factorial(r));answers[str(r)]=str(value)
 if r==1:
  expected=s.Rational(1,12)-(s.digamma(1+s.I)+s.digamma(1-s.I))/2
  if s.simplify(value-expected)!=0:raise ValueError('c1(2) mismatch')
# Gamma reflection yields the constant formula at p=2.
if s.simplify(s.gamma(1+s.I)*s.gamma(1-s.I)-s.pi/s.sinh(s.pi))!=0:raise ValueError('Gamma reflection mismatch')
result={'power':2,'orders':answers,'partial_fraction_reconstructions':4,'gamma_constant_check':True}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print('Four exact square-weight rational reconstructions and Gamma constant passed')
