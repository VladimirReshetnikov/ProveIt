"""Directed integer intervals and exact Machin/Taylor bounds."""
from fractions import Fraction as F
from dataclasses import dataclass
from math import factorial
from pathlib import Path
import json,time
S=10**32
@dataclass(frozen=True)
class I:
 lo:int;hi:int
 def __add__(a,b):
  if not isinstance(b,I):b=iv(b)
  return I(a.lo+b.lo,a.hi+b.hi)
 __radd__=__add__
 def __neg__(a):return I(-a.hi,-a.lo)
 def __sub__(a,b):return a+-iv(b)
 def __rsub__(a,b):return iv(b)+-a
 def __mul__(a,b):
  b=iv(b);v=[a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi];return I(min(v)//S,-((-max(v))//S))
 __rmul__=__mul__
 def __truediv__(a,b):
  if not isinstance(b,I):
   b=F(b);assert b>0
   return I((a.lo*b.denominator)//b.numerator,-((-a.hi*b.denominator)//b.numerator))
  assert b.lo>0;return a*I(S*S//b.hi,-((-S*S)//b.lo))
 def square(a):
  lo=0 if a.lo<=0<=a.hi else min(a.lo*a.lo,a.hi*a.hi)
  hi=max(a.lo*a.lo,a.hi*a.hi);return I(lo//S,-((-hi)//S))
def iv(x):
 if isinstance(x,I):return x
 x=F(x);return I((x.numerator*S)//x.denominator,-((-x.numerator*S)//x.denominator))
def atan_bounds(q,N):
 v=sum((F((-1)**k,(2*k+1)*q**(2*k+1))for k in range(N)),F(0));w=v+F((-1)**N,(2*N+1)*q**(2*N+1));return min(v,w),max(v,w)
a,b=atan_bounds(5,32);c,d=atan_bounds(239,10);plo,phi=16*a-4*d,16*b-4*c
PI=I(iv(plo).lo,iv(phi).hi)
def sinp(x):
 x=PI*iv(x);xx=x.square();term=x;v=x
 for k in range(1,40):term=-(term*xx)/((2*k)*(2*k+1));v=v+term
 # Taylor's derivative remainder: |R_80(x)|<=|x|^81/81!; degree79 used, so use degree80 with zero coefficient.
 ab=I(0,max(abs(x.lo),abs(x.hi)));power=iv(1)
 for _ in range(81):power=power*ab
 rad=(power/ factorial(81)).hi;return I(v.lo-rad,v.hi+rad)
def cosp(x):
 x=PI*iv(x);xx=x.square();term=iv(1);v=term
 for k in range(1,40):term=-(term*xx)/((2*k-1)*(2*k));v=v+term
 # Degree78 polynomial equals degree79 Taylor polynomial.
 ab=I(0,max(abs(x.lo),abs(x.hi)));power=iv(1)
 for _ in range(80):power=power*ab
 rad=(power/factorial(80)).hi;return I(v.lo-rad,v.hi+rad)
def srng(l,h,mode):
 # Required intervals are contained in a monotonicity interval.
 a,b=sinp(l),sinp(h)
 return I(a.lo,b.hi) if mode=='up' else I(b.lo,a.hi)
def crng(l,h):return I(cosp(h).lo,cosp(l).hi)
