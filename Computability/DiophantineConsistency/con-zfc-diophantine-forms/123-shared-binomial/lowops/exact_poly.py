"""Small exact sparse Z-polynomial arithmetic for the independent checker.

A monomial is a sorted tuple of variable names, with repetitions for powers.
No external package, floating point, interpolation, or expression evaluation
is used by this arithmetic module.
"""
class Poly:
 def __init__(self,terms):self.terms={m:c for m,c in terms.items() if c}
 @staticmethod
 def coerce(v):
  if isinstance(v,Poly):return v
  if type(v) is int:return Poly({():v})
  raise TypeError(type(v))
 def __add__(self,other):
  other=self.coerce(other);out=dict(self.terms)
  for m,c in other.terms.items():out[m]=out.get(m,0)+c
  return Poly(out)
 def __radd__(self,other):return self+other
 def __neg__(self):return Poly({m:-c for m,c in self.terms.items()})
 def __sub__(self,other):return self+-self.coerce(other)
 def __rsub__(self,other):return self.coerce(other)+-self
 def __mul__(self,other):
  other=self.coerce(other);out={}
  for m,c in self.terms.items():
   for n,d in other.terms.items():
    k=tuple(sorted(m+n));out[k]=out.get(k,0)+c*d
  return Poly(out)
 def __rmul__(self,other):return self*other
 def __pow__(self,n):
  if type(n) is not int or n<0:raise ValueError('nonnegative fixed exponent required')
  if n==0:return Integer(1)
  if n==1:return self
  h=self**(n//2);p=h*h;return p*self if n%2 else p
 def __eq__(self,other):
  try:return self.terms==self.coerce(other).terms
  except TypeError:return False
 def __bool__(self):return bool(self.terms)
 def subs(self,variable,value):
  variable=self.coerce(variable)
  if len(variable.terms)!=1:raise ValueError('single variable required')
  mon,co=next(iter(variable.terms.items()))
  if len(mon)!=1 or co!=1:raise ValueError('single variable required')
  name=mon[0];value=self.coerce(value);out=Integer(0)
  for m,c in self.terms.items():
   power=m.count(name);remaining=tuple(v for v in m if v!=name)
   out=out+Poly({remaining:c})*value**power
  return out

def Symbol(name):return Poly({(name,):1})
def Integer(value):return Poly.coerce(value)
def symbols(names):return tuple(Symbol(n) for n in names.split())
def expand(value):return Poly.coerce(value)
