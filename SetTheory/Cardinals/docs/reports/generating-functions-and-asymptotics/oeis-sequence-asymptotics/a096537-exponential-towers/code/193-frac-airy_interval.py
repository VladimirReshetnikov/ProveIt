"""Rigorous positive-real Airy interval evaluation from convergent series.
See README.md for the mathematical and arithmetic-library trust boundary.
"""
from interval_decimal import I,D,DN,UP,NEAR,PI,gamma_fraction,MISSING,exact_decimal,integer
from fractions import Fraction
from functools import lru_cache
SQRT3=I(3).sqrt();A=(I(2).ln()*I(Fraction(-1,3))).exp();ROOT3=(I(3).ln()/3).exp()
AI0=1/(ROOT3**2*gamma_fraction(Fraction(2,3)))
AP0=-1/(ROOT3*gamma_fraction(Fraction(1,3)))

def fundamental_point(x,offset,steps=64):
 x=exact_decimal(x);integer(offset,'Airy basis offset');integer(steps,'Airy series steps',1)
 if offset not in (0,1):raise ValueError('Airy basis offset must be zero or one')
 z=I(x)
 if z.lo<0 or z.hi>9:raise ValueError('Series domain0<=x<=9')
 if x==0:return (I(1),I(0)) if offset==0 else (I(0),I(1))
 term=z**offset;s=term;ds=I(0) if offset==0 else I(1)
 zz=z**3;n=offset
 for k in range(steps):
  term=term*zz/((n+3)*(n+2));n+=3;s+=term;ds+=term*n/z
 nxt=term*zz/((n+3)*(n+2));nn=n+3
 ratio=zz/((nn+3)*(nn+2))
 ratiod=ratio*I(Fraction(nn+3,nn))
 if not (ratio.hi<1 and ratiod.hi<1):raise ValueError("Airy geometric tail ratio is not below1")
 tail=nxt/(1-ratio);taild=nxt*nn/z/(1-ratiod)
 return s+I(0,tail.hi),ds+I(0,taild.hi)

@lru_cache(maxsize=100000,typed=True)
def airy_point(x):
 x=exact_decimal(x);f,fp=fundamental_point(x,0);g,gp=fundamental_point(x,1)
 ai=AI0*f+AP0*g;ap=AI0*fp+AP0*gp
 bi=SQRT3*(AI0*f-AP0*g);bp=SQRT3*(AI0*fp-AP0*gp)
 return ai,ap,bi,bp

def airy_range(z):
 z=I(z);l=airy_point(z.lo);h=airy_point(z.hi)
 # Ai decreases, Ai' increases, Bi and Bi' increase on the nonnegative axis.
 return I(h[0].lo,l[0].hi),I(l[1].lo,h[1].hi),I(l[2].lo,h[2].hi),I(l[3].lo,h[3].hi)

def atan_point(x):
 x=I(x)
 if x.lo<0:raise ValueError("atan_point accepts nonnegative arguments only")
 if x.hi==0:return I(0)
 times=0
 while x.hi>D('0.1'):
  x=x/(1+(1+x*x).sqrt());times+=1
 term=x;s=x
 for k in range(1,45):
  term=term*x*x;s+=((-1)**k)*term/(2*k+1)
 nxt=term*x*x/(2*45+1)
 # Last included index44 is positive; remainder lies between−next and0.
 s=s+I(nxt.hi.copy_negate(),0)
 return s*(2**times)

def atan_range(x):
 x=I(x)
 if x.lo<0:raise ValueError('Positive atan used here')
 return I(atan_point(x.lo).lo,atan_point(x.hi).hi)

class C:
 __slots__=('r','i')
 def __init__(self,r=0,i=MISSING):
  if isinstance(r,C):
   if i is not MISSING:raise TypeError('Complex copy constructor takes one argument')
   self.r,self.i=I(r.r),I(r.i)
  else:self.r,self.i=I(r),I(0 if i is MISSING else i)
 def __add__(self,b):b=C(b);return C(self.r+b.r,self.i+b.i)
 __radd__=__add__
 def __neg__(self):return C(-self.r,-self.i)
 def __sub__(self,b):return self+-C(b)
 def __rsub__(self,b):return C(b)+-self
 def __mul__(self,b):b=C(b);return C(self.r*b.r-self.i*b.i,self.r*b.i+self.i*b.r)
 __rmul__=__mul__
 def conj(self):return C(self.r,-self.i)
 def inv(self):
  d=self.r**2+self.i**2;return C(self.r/d,-self.i/d)
 def __truediv__(self,b):return self*C(b).inv()
 def __rtruediv__(self,b):return C(b)*self.inv()
 def __pow__(self,n):
  integer(n,'power')
  if n<0:return (self**(-n)).inv()
  q=C(1);v=self
  while n:
   if n&1:q=q*v
   v=v*v;n//=2
  return q
 def log_q1(self):
  if self.r.lo<=0 or self.i.lo<0:raise ValueError('QuadrantI log only')
  return C((self.r**2+self.i**2).ln()/2,atan_range(self.i/self.r))
 def __repr__(self):return f'C({self.r},{self.i})'

