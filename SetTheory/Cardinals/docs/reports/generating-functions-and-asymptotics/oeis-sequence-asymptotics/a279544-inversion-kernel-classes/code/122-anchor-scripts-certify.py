"""Exact rational finite orbit certificate for A279558. See report122.pdf for the mathematical proof.
No floating-point operations enter the proof certificate.
"""
if not __debug__:
 raise RuntimeError("Auxiliary producer scripts require ordinary Python; run the active-guard companion with python3 checks/verify.py")
from fractions import Fraction as Q
from math import isqrt
DIGITS=120
S=10**DIGITS

def ceildiv(a,b):return -((-a)//b)
class I:
 def __init__(self,a,b=None,raw=False):
  if raw:self.a,self.b=a,b
  else:
   a=Q(a);b=Q(a if b is None else b)
   self.a=(a.numerator*S)//a.denominator;self.b=ceildiv(b.numerator*S,b.denominator)
 def __add__(x,y):y=cv(y);return I(x.a+y.a,x.b+y.b,raw=True)
 __radd__=__add__
 def __neg__(x):return I(-x.b,-x.a,raw=True)
 def __sub__(x,y):return x+-cv(y)
 def __rsub__(x,y):return cv(y)+-x
 def __mul__(x,y):
  y=cv(y);v=[x.a*y.a,x.a*y.b,x.b*y.a,x.b*y.b];return I(min(v)//S,ceildiv(max(v),S),raw=True)
 __rmul__=__mul__
 def inv(x):
  assert not x.a<=0<=x.b
  return I((S*S)//x.b,ceildiv(S*S,x.a),raw=True)
 def __truediv__(x,y):return x*cv(y).inv()
 def __rtruediv__(x,y):return cv(y)*x.inv()
 def sqrt(x):
  assert x.a>=0
  return I(isqrt(x.a*S),isqrt(x.b*S)+1,raw=True)
 def widen(x,e):return x+I(-e,e)
 def inside(x,a,b):return Q(x.a,S)>Q(a) and Q(x.b,S)<Q(b)
 def out(x):
  def f(a):return ('-' if a<0 else '')+str(abs(a)//S)+'.'+str(abs(a)%S).zfill(DIGITS)
  return '['+f(x.a)+', '+f(x.b)+']'
def cv(x):return x if isinstance(x,I) else I(x)
class D:
 def __init__(self,v,d=0):self.v,self.d=cv(v),cv(d)
 def __add__(x,y):y=dc(y);return D(x.v+y.v,x.d+y.d)
 __radd__=__add__
 def __neg__(x):return D(-x.v,-x.d)
 def __sub__(x,y):return x+-dc(y)
 def __rsub__(x,y):return dc(y)+-x
 def __mul__(x,y):y=dc(y);return D(x.v*y.v,x.d*y.v+x.v*y.d)
 __rmul__=__mul__
 def inv(x):return D(1/x.v,-x.d/(x.v*x.v))
 def __truediv__(x,y):return x*dc(y).inv()
 def __rtruediv__(x,y):return dc(y)*x.inv()
def dc(x):return x if isinstance(x,D) else D(x)

def atan_inv(q,m):
 a=sum((Q((-1)**j,(2*j+1)*q**(2*j+1)) for j in range(m)),Q(0))
 b=a+Q((-1)**m,(2*m+1)*q**(2*m+1))
 return I(min(a,b),max(a,b))
pi=16*atan_inv(5,120)-4*atan_inv(239,40)

rho=Q(4,27);h=Q(1,100000);r=Q(1,1000)
zlo=rho*(1-h*h);zhi=rho*(1+h*h);Z=Q(149,1000);M=Q(176,100);q=Q(1,2)
# Uniform complex region |z-rho|<=rho*h^2, |R-3/2|<=r.
assert zhi<Z and 1/zlo<7
assert Z*(1+Z*M)/(1-Z*M)**3<q
Xmax=(Q(3,2)+r)**2
assert Xmax<Q(226,100)
assert Z*(1+Z*Xmax)/(1-Z*Xmax)**3<Q(11,10)
assert Xmax*(1+Z*Xmax)/(1-Z*Xmax)**3<11
assert M*(1+Z*M)/(1-Z*M)**3<6
assert Q(11,10)*(3+r)*r+11*rho*h*h<Q(1,250)
assert Q(1,250)+12*rho*h*h<Q(1,200)
assert Q(7,4)+Q(1,200)<M and 1-Q(1,200)>Q(99,100)
# Reference upper x0=7/4, x1=589/400, and lower x0=1.
assert Q(7,4)-Q(589,400)<Q(28,100)
assert rho/(1-rho)**2<Q(21,100)
assert Q(28,100)+Q(3,2)*Q(1,250)+6*rho*h*h<Q(3,10)
assert 7*Q(3,10)/Q(99,100)<Q(11,5)
assert (1+Z*M)*Q(11,5)<3
# Products bounded by e^6 < 3^6 < 2^10.
P=2**10
assert 3**6<P
assert 2+Q(22,5)<7
assert 2*(3*7*P+Q(11,5))<2**16
N=512;E=Q(2**16)*q**N

def phi(z,x):return 1+z*x/((1-z*x)*(1-z*x))
def orbit(z,x,v,p=None):
 for j in range(N):
  nx=phi(z,x);d=(x-nx)/(z*x);c=1-(1-z*x)*d
  v=c*v+d
  if p is not None:p=c*p
  x=nx
 return (v,p) if p is not None else v

z=D(rho);R=D(Q(3,2),1)
V=orbit(z,phi(z,R*R),R)
Q0,P0=orbit(z,D(1),D(0),D(1))
V=D(V.v.widen(E),V.d.widen(1000*E))
Q0=D(Q0.v.widen(E),Q0.d);P0=D(P0.v.widen(E),P0.d)
F=(V-Q0)/P0
C=I(3).sqrt()*F.d/(4*pi.sqrt())
assert F.v.inside(Q(1226243,10**6),Q(1226244,10**6))
assert F.d.inside(Q(740740,10**9),Q(740741,10**9))
assert C.inside(Q(1809637754651179072704308064957871691430,10**43),Q(1809637754651179072704308064957871691431,10**43))
print('PASS: exact interval and uniform infinite-tail certificate')
print('F(rho):',F.v.out());print('F_R:',F.d.out());print('C:',C.out())
print('P0:',P0.v.out());print('Tail E=2^16 (1/2)^512, derivative tail=1000 E')
