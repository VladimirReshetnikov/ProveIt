"""Rational interval certificate for root, amplitudes and pole polynomials.
Only standard library and original local finite combinatorial routines.
"""
from fractions import Fraction as F
from math import factorial,comb
from check_fixed_permanent import kernel_poly,expand_kernel,mul
import json
class I:
 def __init__(self,a,b=None):
  if isinstance(a,I):self.a,self.b=a.a,a.b
  else:self.a,self.b=F(a),F(a if b is None else b)
  if self.a>self.b:raise ValueError('interval reversed')
 def __add__(self,o):o=I(o);return I(self.a+o.a,self.b+o.b)
 __radd__=__add__
 def __neg__(self):return I(-self.b,-self.a)
 def __sub__(self,o):return self+-I(o)
 def __rsub__(self,o):return I(o)+-self
 def __mul__(self,o):
  o=I(o);v=[self.a*o.a,self.a*o.b,self.b*o.a,self.b*o.b];return I(min(v),max(v))
 __rmul__=__mul__
 def __truediv__(self,o):
  o=I(o)
  if o.a<=0<=o.b:raise ZeroDivisionError
  return self*I(1/o.b,1/o.a)
 def __rtruediv__(self,o):return I(o)/self
 def __pow__(self,n):
  if n<0:return I(1)/(self**(-n))
  v=I(1)
  for _ in range(n):v*=self
  return v
 def dump(self):return [str(self.a),str(self.b)]
 def outer_decimal(self,d=25):
  den=10**d;lo=self.a*den;hi=self.b*den
  a=lo.numerator//lo.denominator;b=-((-hi.numerator)//hi.denominator)
  def dec(n):
   sg='-' if n<0 else '';n=abs(n);return sg+str(n//den)+'.'+str(n%den).zfill(d)
  return [dec(a),dec(b)]
def require(p,msg):
 if not p:raise ArithmeticError(msg)
N=45;R=F(3,2)
ex=[F((-1)**n,factorial(n)) for n in range(N)]
ec=[x/2**comb(n,2) for n,x in enumerate(ex)]
kernels,_=kernel_poly(4)
S={2:[F(0),F(0)]+[F(1,n) for n in range(2,N)]}
S.update({k:expand_kernel(t,N) for k,t in kernels.items()})
hc={k:[x/2**comb(n,2) for n,x in enumerate(mul(ex,v,N))] for k,v in S.items()}
t=mul(ex,mul(S[2],S[2],N),N)
hc[4]=[x-y/2**(comb(n,2)+1) for n,(x,y) in enumerate(zip(hc[4],t))]
def evaluate(c,x,j=0,kind='h'):
 require(len(c)==N and isinstance(j,int) and 0<=j<=4 and kind in ('e','h'),'unsupported coefficient/tail parameters')
 x=I(x)
 require(max(abs(x.a),abs(x.b))<=R,'argument outside certified disk')
 v=I(0)
 for n in range(len(c)-1,j-1,-1):v=v*x+c[n]*F(factorial(n),factorial(n-j))
 if kind=='e':first=R**(N-j)/(factorial(N-j)*2**comb(N,2))
 else:first=64*2**N*F(factorial(N),factorial(N-j))*R**(N-j)/2**comb(N,2)
 # Consecutive term ratios are <1/2 for N>=45,j<=4.
 err=2*first
 return v+I(-err,err)
r=I('1.4880785455997102946562460315823576618935','1.4880785455997102946562460315823576618936')
lo=evaluate(ec,I(r.a),kind='e');hi=evaluate(ec,I(r.b),kind='e')
require(lo.a>0 and hi.b<0,'root sign bracket')
a=-r*evaluate(ec,r,1,'e');b=r*r*evaluate(ec,r,2,'e')/2;c=-r**3*evaluate(ec,r,3,'e')/6
h={k:evaluate(v,r) for k,v in hc.items()};hp={k:evaluate(v,r,1) for k,v in hc.items()};hpp={k:evaluate(v,r,2) for k,v in hc.items()}
require(a.a>0 and h[2].a>0 and h[3].a>0,'positive amplitudes')
P={1:{1:1/a}}
for k in (2,3):P[k]={2:h[k]/a**2,1:-r*hp[k]/a**2-2*b*h[k]/a**3}
P[4]={3:h[2]**2/a**3,2:h[4]/a**2-2*r*h[2]*hp[2]/a**3-3*b*h[2]**2/a**4,1:-r*hp[4]/a**2-2*b*h[4]/a**3+r**2*(hp[2]**2+h[2]*hpp[2])/a**3+6*b*r*h[2]*hp[2]/a**4+h[2]**2*(6*b**2/a**5-3*c/a**4)}
values={'rho':r,'a':a,**{'h'+str(k):v for k,v in h.items()},**{f'P{k}_binomial{j}':v for k,p in P.items() for j,v in p.items()}}
data={key:{'outward_decimal_25':v.outer_decimal()} for key,v in values.items()}
print(json.dumps({k:v['outward_decimal_25'] for k,v in data.items()},indent=2))
open('constant_certificate.json','w').write(json.dumps(data,indent=2)+'\n')
