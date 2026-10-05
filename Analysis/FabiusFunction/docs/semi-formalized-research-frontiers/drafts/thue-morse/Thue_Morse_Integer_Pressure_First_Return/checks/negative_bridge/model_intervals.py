"""Exact rational side conditions for an eventual degree<6.6m theorem."""
from fractions import Fraction as F
from pathlib import Path
import sys,json,math
sys.path.insert(0,str(Path(__file__).resolve().parent))
from exact_intervals import I,iv,PI,S,sinp,cosp

def require(condition,message):
 if not condition:raise ArithmeticError(message)

def trig_rad(x,sine):
 x=iv(x);xx=x.square();term=x if sine else iv(1);v=term
 for k in range(1,40):
  term=-(term*xx)/((2*k)*(2*k+1)if sine else (2*k-1)*(2*k));v=v+term
 power=iv(1);ab=I(0,max(abs(x.lo),abs(x.hi)));order=81 if sine else 80
 for _ in range(order):power=power*ab
 rad=(power/math.factorial(order)).hi
 return I(v.lo-rad,v.hi+rad)

bs=[sinp(F(1,2**(j+1)))/cosp(F(1,2**(j+1)))for j in range(1,33)]
def values(t):
 a=trig_rad(t,True)/trig_rad(t,False);prod=iv(1);mean=iv(0)
 for b in bs:
  prod=prod*(1+a*b);mean=mean+(a*b)/(1+a*b)
 mean=I(mean.lo,mean.hi+(a*F(1,2**31)).hi)
 mu=iv(t)*(1+a.square())/a*(1+mean)
 g=iv(2)/PI*a*prod
 return mu,g

def lo(x):return F(x.lo,S)
def hi(x):return F(x.hi,S)