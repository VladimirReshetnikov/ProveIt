"""Directed Decimal real intervals for the stated finite certificate domain.
The mathematical and Decimal-library trust boundary is documented in README.md.
"""
from decimal import Decimal, Context, ROUND_FLOOR, ROUND_CEILING, ROUND_HALF_EVEN
from fractions import Fraction
PREC=70
DN=Context(prec=PREC,rounding=ROUND_FLOOR)
UP=Context(prec=PREC,rounding=ROUND_CEILING)
NEAR=Context(prec=PREC,rounding=ROUND_HALF_EVEN)
D=Decimal
MISSING=object()
def exact_decimal(value):
 """Accept finite exact scalar inputs, never bools, floats, tuples or complex."""
 if type(value) not in (int,str,Decimal):raise TypeError('Exact integer, string, or Decimal required')
 value=D(value)
 if not value.is_finite():raise ValueError('Non-finite scalar')
 return value

def integer(value,name,minimum=None):
 if type(value) is not int:raise TypeError(name+' must be an integer')
 if minimum is not None and value<minimum:raise ValueError(name+' is outside its domain')
 return value

class I:
 __slots__=('lo','hi')
 def __init__(self,lo,hi=MISSING):
  if isinstance(lo,(I,Fraction)):
   if hi is not MISSING:raise TypeError('Interval and rational constructors take one argument')
   if isinstance(lo,I):
    self.lo,self.hi=exact_decimal(lo.lo),exact_decimal(lo.hi)
   else:
    self.lo=DN.divide(D(lo.numerator),D(lo.denominator));self.hi=UP.divide(D(lo.numerator),D(lo.denominator))
  else:
   self.lo=exact_decimal(lo);self.hi=self.lo if hi is MISSING else exact_decimal(hi)
  if not self.lo.is_finite() or not self.hi.is_finite():raise ValueError('Non-finite interval')
  if self.lo>self.hi:raise ValueError('Inverted interval')
 def __repr__(self):return f'I({self.lo},{self.hi})'
 def __add__(self,b):
  b=I(b);return I(DN.add(self.lo,b.lo),UP.add(self.hi,b.hi))
 __radd__=__add__
 def __neg__(self):return I(self.hi.copy_negate(),self.lo.copy_negate())
 def __sub__(self,b):return self+-I(b)
 def __rsub__(self,b):return I(b)+-self
 def __mul__(self,b):
  b=I(b);pairs=((x,y) for x in (self.lo,self.hi) for y in (b.lo,b.hi));p=list(pairs)
  return I(min(DN.multiply(x,y) for x,y in p),max(UP.multiply(x,y) for x,y in p))
 __rmul__=__mul__
 def inv(self):
  if self.lo<=0<=self.hi:raise ZeroDivisionError(self)
  return I(DN.divide(D(1),self.hi),UP.divide(D(1),self.lo))
 def __truediv__(self,b):return self*I(b).inv()
 def __rtruediv__(self,b):return I(b)*self.inv()
 def __pow__(self,n):
  integer(n,'power')
  if n<0:return (self**(-n)).inv()
  if n==0:return I(1)
  def scalar_bounds(x):
   ax=x.copy_abs();lo=hi=D(1)
   for _ in range(n):lo=DN.multiply(lo,ax);hi=UP.multiply(hi,ax)
   if x<0 and n%2:return hi.copy_negate(),lo.copy_negate()
   return lo,hi
  vals=[scalar_bounds(x) for x in (self.lo,self.hi)]
  if n%2==0 and self.lo<0<self.hi:return I(0,max(v[1] for v in vals))
  return I(min(v[0] for v in vals),max(v[1] for v in vals))
 def abs(self):
  if self.lo>=0:return self
  if self.hi<=0:return -self
  return I(0,max(self.lo.copy_negate(),self.hi))
 def sqrt(self):
  if self.lo<0:raise ValueError(self)
  # Decimal sqrt/ln/exp are correctly rounded to nearest; outward neighbors enclose.
  return I(max(D(0),NEAR.next_minus(NEAR.sqrt(self.lo))),NEAR.next_plus(NEAR.sqrt(self.hi)))
 def ln(self):
  if self.lo<=0:raise ValueError(self)
  return I(NEAR.next_minus(NEAR.ln(self.lo)),NEAR.next_plus(NEAR.ln(self.hi)))
 def exp(self):return I(NEAR.next_minus(NEAR.exp(self.lo)),NEAR.next_plus(NEAR.exp(self.hi)))
 def width(self):return UP.subtract(self.hi,self.lo)
 def mid(self):return NEAR.divide(NEAR.add(self.lo,self.hi),D(2))
 def hull(self,b):b=I(b);return I(min(self.lo,b.lo),max(self.hi,b.hi))
 def contains(self,x):
  q=I(x)
  return self.lo<=q.lo and q.hi<=self.hi

def atan_small(x,n=100):
 """Alternating rational series enclosure, for exact rational x in[0,1)."""
 if not isinstance(x,Fraction) or not (0<=x<1):raise ValueError('Rational arctangent argument outside [0,1)')
 integer(n,'terms',1)
 s=Fraction(0)
 for k in range(n):s+=(-1)**k*x**(2*k+1)/(2*k+1)
 nxt=(-1)**n*x**(2*n+1)/(2*n+1)
 return I(min(s,s+nxt)).hull(I(max(s,s+nxt)))
PI=16*atan_small(Fraction(1,5),110)-4*atan_small(Fraction(1,239),30)

def bernoulli(n):
 integer(n,'Bernoulli index',0)
 a=[Fraction(0)]*(n+1)
 for m in range(n+1):
  a[m]=Fraction(1,m+1)
  for j in range(m,0,-1):a[j-1]=j*(a[j-1]-a[j])
 return a[0]

def gamma_fraction(x,shift=100,terms=12):
 """Positive real gamma using the enveloping real Stirling expansion.
 Bound is the first omitted Bernoulli term, with its sign.
 """
 if not isinstance(x,Fraction) or x<=0:raise ValueError('Positive rational gamma input required')
 integer(shift,'gamma shift',0);integer(terms,'gamma terms',1)
 z=I(x+shift)
 logg=(z-I(Fraction(1,2)))*z.ln()-z+(2*PI).ln()/2
 for k in range(1,terms):logg+=I(bernoulli(2*k))/I(2*k*(2*k-1))/(z**(2*k-1))
 rem=I(bernoulli(2*terms))/I(2*terms*(2*terms-1))/(z**(2*terms-1))
 logg=logg+I(min(D(0),rem.lo),max(D(0),rem.hi))
 for j in range(shift):logg-=I(x+j).ln()
 return logg.exp()

