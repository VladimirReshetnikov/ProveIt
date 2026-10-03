import sympy as s
from fractions import Fraction
from math import factorial
import json, hashlib
from pathlib import Path
import mpmath as mp
r,t,y,e=s.symbols('r t y e', positive=True)
a=1-t
P1=y-y**2/2
P2=y**2/2-y**3/3+P1**2/2
lap=lambda p:s.expand(p).as_poly(y)
def integ(p):
 return s.factor(sum(c*s.factorial(j[0])/a**(j[0]+1) for j,c in lap(p).terms()))
M0=1/a;M1=integ(P1);M2=integ(P2)
B1=s.factor(M1/M0);B2=s.factor(M2/M0-B1**2/2)
t0=1-r;d=s.factor(-s.diff(B1,t).subs(t,t0)*r**2)
# Stationary exponent e term, with m=1/e and k=r/e.
A=s.factor(r*(B2.subs(t,t0)+d*s.diff(B1,t).subs(t,t0)+d**2/(2*r**2)))
# Relative correction to |t|^-1 (K'')^-1/2.
v1=s.factor(2*d/r**3+s.diff(B1,t,2).subs(t,t0))
F=s.factor(-d/t0-v1*r**2/2)
# Limiting tilted exponential law: sigma=1/r, lambda3=2,lambda4=6.
Q=s.factor(s.Rational(6,8)-s.Rational(20,24)-r/t0-r**2/t0**2)
C=s.factor(A+F+Q/r)
claimed=-(r**4+10*r**3-17*r**2+24*r-6)/(12*r**3*(r-1)**2)
assert s.factor(B1-(1/a-1/a**2))==0
assert s.factor(B2-(s.Rational(3,2)/a**2-4/a**3+s.Rational(5,2)/a**4))==0
assert s.factor(d-(2/r-1))==0
assert s.factor(C-claimed)==0
symbolic={key:str(val) for key,val in dict(B1=B1,B2=B2,saddle_shift=d,exponent_correction=A,prefactor_correction=F,Q1_limit=Q,c1=C).items()}
print(json.dumps(symbolic,indent=2),flush=True)
# Independent coefficient recurrence from q A'=k q' A, not repeated convolution.
def exact_success(m,k):
 q=[(-1)**j*factorial(m-1)//factorial(m-1-j) for j in range(m)]
 D=k*(m-1);coeff=[1]
 for n in range(1,D+1):
  num=sum(((k+1)*j-n)*q[j]*coeff[n-j] for j in range(1,min(n,m-1)+1))
  assert num%n==0
  coeff.append(num//n)
 denom=factorial(k+D);weight=1;total=0
 for n in range(D,-1,-1):
  total+=coeff[n]*weight
  weight*=k+n
 return Fraction(m**k*total,denom)
mp.mp.dps=70
rows=[]
for m,k in [(10,5),(10,8),(10,15),(10,20),(20,10),(20,15),(20,30),(20,40),(40,20),(40,30),(40,60),(40,80),(60,30),(60,120)]:
 p=exact_success(m,k);tail=p if k>m else 1-p
 W=factorial(m*k)//factorial(m)**k
 assert (p*W).denominator==1
 rho=mp.mpf(k)/m;T=mp.mpf(tail.numerator)/tail.denominator
 leading=mp.exp(1-1/rho)*mp.sqrt(rho)/(abs(rho-1)*mp.sqrt(2*mp.pi*m))*mp.exp(-m*(1-rho+rho*mp.log(rho)))
 c=-(rho**4+10*rho**3-17*rho**2+24*rho-6)/(12*rho**3*(rho-1)**2)
 row=dict(m=m,k=k,tail=mp.nstr(T,30),exact_over_leading=mp.nstr(T/leading,30),c1=mp.nstr(c,30),exact_over_first=mp.nstr(T/(leading*(1+c/m)),30),scaled_second_residual=mp.nstr(m*m*(T/leading-1-c/m),30))
 rows.append(row);print(row,flush=True)
path=Path(__file__).resolve().parent.parent/'checks'
(path/'independent-rare-results.json').write_text(json.dumps(dict(symbolic=symbolic,exact_checks=rows),indent=2)+'\n')
