"""Exact fixed-grid real/complex enclosures for the contour certificates."""
from pathlib import Path
from fractions import Fraction as F
from dataclasses import dataclass
from math import isqrt
from functools import lru_cache
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
from exact_intervals import I,iv,PI,S,sinp,cosp

@dataclass(frozen=True)
class C:
 re:I;im:I
 def __add__(a,b):
  if not isinstance(b,C):b=C(iv(b),iv(0))
  return C(a.re+b.re,a.im+b.im)
 __radd__=__add__
 def __neg__(a):return C(-a.re,-a.im)
 def __sub__(a,b):return a+-b
 def __mul__(a,b):
  if not isinstance(b,C):b=C(iv(b),iv(0))
  return C(a.re*b.re-a.im*b.im,a.re*b.im+a.im*b.re)
 __rmul__=__mul__
 def square_mod(a):return a.re.square()+a.im.square()
 def conjugate(a):return C(a.re,-a.im)

def sqrt_interval(x):
 if x.lo<0:raise ArithmeticError('negative square-root lower endpoint')
 lo=isqrt(x.lo*S);hi=isqrt(x.hi*S)
 if hi*hi<x.hi*S:hi+=1
 return I(lo,hi)

def trig_rad(x,kind):
 x=iv(x);xx=x.square();odd=kind in ['sin','sinh'];hyper=kind in ['sinh','cosh']
 if max(abs(x.lo),abs(x.hi))>=S:raise ArithmeticError('Taylor argument must have modulus<1')
 term=x if odd else iv(1);v=term
 for j in range(1,21):
  term=term*xx/((2*j)*(2*j+1)if odd else (2*j-1)*(2*j))
  if not hyper:term=-term
  v=v+term
 # Degree41/40; |argument|<1. The trigonometric and hyperbolic tails are <3/42!<1/S.
 return I(v.lo-1,v.hi+1)

@lru_cache(None)
def angle_box(qlo,qhi):
 return I(cosp(qhi).lo,cosp(qlo).hi),I(sinp(qlo).lo,sinp(qhi).hi)

def tangent_circle(tlo,thi,qlo,qhi):
 co,si=angle_box(qlo,qhi);t=I(iv(tlo).lo,iv(thi).hi)
 u=2*t*co;v=2*t*si
 den=trig_rad(u,'cos')+trig_rad(v,'cosh')
 return C(trig_rad(u,'sin')/den,trig_rad(v,'sinh')/den)

@lru_cache(None)
def fixed_spatial_trig(x,j):return cosp(x/F(2**j)),sinp(x/F(2**j))

def spatial_product(a,x,J=20):
 z=C(iv(1),iv(0))
 for j in range(1,J+1):
  co,si=fixed_spatial_trig(x,j);z=z*(C(co,iv(0))+a*si)
 r=sqrt_interval(a.square_mod())
 # sum |factor-1| <= r*pi*x/2^J+(pi*x)^2/(6*4^J).
 px=PI*abs(x);tail=r*px/F(2**J)+px.square()/F(6*4**J)
 if tail.hi>=S:raise ArithmeticError('tail too large')
 tlo=1-tail;thi=iv(1)/(1-tail)
 p=z.square_mod()
 return I((p*tlo.square()).lo,(p*thi.square()).hi)
