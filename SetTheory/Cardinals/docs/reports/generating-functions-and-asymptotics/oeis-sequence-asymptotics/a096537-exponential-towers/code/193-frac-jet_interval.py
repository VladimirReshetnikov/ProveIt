"""Second derivative interval jets, all arithmetic inherited from directed intervals."""
from interval_decimal import I,MISSING,integer
from airy_interval import atan_range
class J:
 __slots__=('v','d','dd')
 def __init__(self,v=0,d=MISSING,dd=MISSING):
  if isinstance(v,J):
   if d is not MISSING or dd is not MISSING:raise TypeError('Jet copy constructor takes one argument')
   self.v,self.d,self.dd=I(v.v),I(v.d),I(v.dd)
  else:self.v,self.d,self.dd=I(v),I(0 if d is MISSING else d),I(0 if dd is MISSING else dd)
 def __add__(self,b):b=J(b);return J(self.v+b.v,self.d+b.d,self.dd+b.dd)
 __radd__=__add__
 def __neg__(self):return J(-self.v,-self.d,-self.dd)
 def __sub__(self,b):return self+-J(b)
 def __rsub__(self,b):return J(b)+-self
 def __mul__(self,b):
  b=J(b);return J(self.v*b.v,self.d*b.v+self.v*b.d,self.dd*b.v+2*self.d*b.d+self.v*b.dd)
 __rmul__=__mul__
 def inv(self):return J(1/self.v,-self.d/self.v**2,2*self.d**2/self.v**3-self.dd/self.v**2)
 def __truediv__(self,b):return self*J(b).inv()
 def __rtruediv__(self,b):return J(b)*self.inv()
 def __pow__(self,n):
  integer(n,'power')
  if n<0:return (self**(-n)).inv()
  q=J(1);v=self
  while n:
   if n&1:q=q*v
   v=v*v;n//=2
  return q
 def ln(self):return J(self.v.ln(),self.d/self.v,self.dd/self.v-self.d**2/self.v**2)
 def atan(self):
  den=1+self.v**2
  return J(atan_range(self.v),self.d/den,self.dd/den-2*self.v*self.d**2/den**2)
 def __repr__(self):return f'J({self.v},{self.d},{self.dd})'
class CJ:
 __slots__=('r','i')
 def __init__(self,r=0,i=MISSING):
  if isinstance(r,CJ):
   if i is not MISSING:raise TypeError('Complex jet copy constructor takes one argument')
   self.r,self.i=J(r.r),J(r.i)
  else:self.r,self.i=J(r),J(0 if i is MISSING else i)
 def __add__(self,b):b=CJ(b);return CJ(self.r+b.r,self.i+b.i)
 __radd__=__add__
 def __neg__(self):return CJ(-self.r,-self.i)
 def __sub__(self,b):return self+-CJ(b)
 def __rsub__(self,b):return CJ(b)+-self
 def __mul__(self,b):b=CJ(b);return CJ(self.r*b.r-self.i*b.i,self.r*b.i+self.i*b.r)
 __rmul__=__mul__
 def conj(self):return CJ(self.r,-self.i)
 def inv(self):
  den=self.r**2+self.i**2;return CJ(self.r/den,-self.i/den)
 def __truediv__(self,b):return self*CJ(b).inv()
 def __rtruediv__(self,b):return CJ(b)*self.inv()
 def __pow__(self,n):
  integer(n,'power')
  if n<0:return (self**(-n)).inv()
  q=CJ(1);v=self
  while n:
   if n&1:q=q*v
   v=v*v;n//=2
  return q
 def log_q1(self):
  if self.r.v.lo<=0 or self.i.v.lo<0:raise ValueError('QuadrantI only')
  return CJ((self.r**2+self.i**2).ln()/2,(self.i/self.r).atan())
