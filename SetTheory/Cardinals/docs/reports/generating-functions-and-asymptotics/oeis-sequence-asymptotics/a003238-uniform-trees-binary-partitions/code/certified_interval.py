"""Directed fixed-point intervals using Python integers only.
Every endpoint is an integer multiple of 2**(-PREC). Exponentials use the
alternating rational Taylor series after range reduction. No float decisions.
"""
from fractions import Fraction as F
from math import factorial
PREC=256;S=1<<PREC

def ceildiv(a,b):return -((-a)//b)
class IV:
 def __init__(self,lo,hi=None):self.lo=int(lo);self.hi=int(lo if hi is None else hi)
 @staticmethod
 def of(x):
  q=F(x);return IV((q.numerator*S)//q.denominator,ceildiv(q.numerator*S,q.denominator))
 def __add__(self,x):
  if not isinstance(x,IV):x=IV.of(x)
  return IV(self.lo+x.lo,self.hi+x.hi)
 __radd__=__add__
 def __neg__(self):return IV(-self.hi,-self.lo)
 def __sub__(self,x):return self+-asiv(x)
 def __rsub__(self,x):return asiv(x)+-self
 def __mul__(self,x):
  x=asiv(x);a=[self.lo*x.lo,self.lo*x.hi,self.hi*x.lo,self.hi*x.hi]
  return IV(min(a)//S,ceildiv(max(a),S))
 __rmul__=__mul__
 def __truediv__(self,x):
  x=asiv(x)
  if x.lo<=0<=x.hi:raise ZeroDivisionError('interval contains zero')
  a=[F(self.lo*S,x.lo),F(self.lo*S,x.hi),F(self.hi*S,x.lo),F(self.hi*S,x.hi)]
  lo=min(a);hi=max(a)
  return IV(lo.numerator//lo.denominator,ceildiv(hi.numerator,hi.denominator))
 def __rtruediv__(self,x):return asiv(x)/self
 def __pow__(self,n):
  if type(n) is not int or n<0:raise ValueError('nonnegative integer power required')
  out=IV.of(1);x=self
  while n:
   if n&1:out=out*x
   x=x*x;n//=2
  return out
 def decimal(self,d=30):
  base=10**d;l=self.lo*base//S;h=ceildiv(self.hi*base,S)
  def fmt(x):
   sign='-' if x<0 else '';x=abs(x);return sign+str(x//base)+'.'+str(x%base).zfill(d)
  return [fmt(l),fmt(h)]
 def integer_bounds(self):return [str(self.lo),str(self.hi)]
def asiv(x):return x if isinstance(x,IV) else IV.of(x)

def expminus(x):
 x=F(x)
 if x<0:return 1/expminus(-x)
 shifts=0
 while x>F(1,16):x/=2;shifts+=1
 term=F(1);partial=F(1);j=0
 while True:
  j+=1;term*=x/j
  if j%2:partial-=term;lo=partial;hi=partial+term*x/(j+1)
  else:partial+=term;hi=partial;lo=partial-term*x/(j+1)
  if term< F(1,1<<(PREC+12)):break
 out=IV(lo.numerator*S//lo.denominator,ceildiv(hi.numerator*S,hi.denominator))
 for _ in range(shifts):out=out*out
 return out

def binary_product(t):
 q=expminus(t);out=IV.of(1);steps=0
 while q.hi>2:
  out=out/(1-q);q=q*q;steps+=1
  if steps>10000:raise RuntimeError('product loop')
 # Remaining q<=2/S: log tail <=q/(1-q)^2<4/S and exp bound <1+8/S.
 return out*IV(S,S+8)

def polynomial(coeff,q):
 if q.lo<0 or q.hi>S or any(a<0 for a in coeff):raise ValueError('nonnegative polynomial and q in [0,1] required')
 lo=hi=0
 for a in reversed(coeff):
  lo=(lo*q.lo)//S+a*S;hi=ceildiv(hi*q.hi,S)+a*S
 return IV(lo,hi)

from functools import lru_cache
@lru_cache(None)
def _log_unit(x):
 x=F(x)
 if not 1<=x<=2:raise ValueError('unit logarithm domain')
 z=IV.of((x-1)/(x+1));z2=z*z;term=z;acc=IV.of(0);M=PREC//3+12
 for j in range(M):acc+=term/(2*j+1);term*=z2
 tail=2*term/((2*M+1)*(1-z2))
 return 2*acc+IV(0,tail.hi)

@lru_cache(None)
def log_rational(x):
 x=F(x)
 if x<=0:raise ValueError('positive logarithm argument required')
 shift=0
 while x>2:x/=2;shift+=1
 while x<1:x*=2;shift-=1
 return _log_unit(x)+shift*_log_unit(F(2))

def exp_interval(v):
 v=asiv(v);lo=expminus(F(-v.lo,S));hi=expminus(F(-v.hi,S))
 return IV(lo.lo,hi.hi)

@lru_cache(None)
def rational_power(x,power):return exp_interval(log_rational(F(x))*F(power))
