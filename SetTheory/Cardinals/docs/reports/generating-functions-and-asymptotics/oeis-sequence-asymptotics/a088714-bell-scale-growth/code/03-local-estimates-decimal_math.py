"""Small Decimal interface used by diagnose.py; no third-party dependency."""
from decimal import Decimal,getcontext,localcontext
import math
class Context:
 @property
 def dps(self):return getcontext().prec
 @dps.setter
 def dps(self,n):getcontext().prec=n
mp=Context()
mpf=Decimal
nan=Decimal('NaN')
def log(x):return Decimal(x).ln()
def exp(x):return Decimal(x).exp()
def factorial(x):return Decimal(math.factorial(x))
def nstr(x,n):
 with localcontext() as c:
  c.prec=n
  return str(+Decimal(x))
def lambertw(n):
 x=Decimal(n); w=log(x+1)
 for _ in range(40):
  e=exp(w); dw=(w*e-x)/(e*(1+w)); nw=w-dw
  if nw==w:return w
  w=nw
 return w
