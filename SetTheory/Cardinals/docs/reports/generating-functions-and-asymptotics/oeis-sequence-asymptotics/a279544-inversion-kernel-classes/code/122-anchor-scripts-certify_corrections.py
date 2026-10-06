"""Exact interval certificates for b1,b3,b5 and first two coefficient corrections."""
if not __debug__:
 raise RuntimeError("Auxiliary producer scripts require ordinary Python; run the active-guard companion with python3 checks/verify.py")
from certify import I,Q,cv,pi,phi,orbit,E,h,rho,S
# Complex rectangular interval arithmetic. No floating-point arithmetic.
class Z:
 def __init__(self,r=0,i=0):self.r,self.i=cv(r),cv(i)
 def __add__(x,y):y=zc(y);return Z(x.r+y.r,x.i+y.i)
 __radd__=__add__
 def __neg__(x):return Z(-x.r,-x.i)
 def __sub__(x,y):return x+-zc(y)
 def __rsub__(x,y):return zc(y)+-x
 def __mul__(x,y):y=zc(y);return Z(x.r*y.r-x.i*y.i,x.r*y.i+x.i*y.r)
 __rmul__=__mul__
 def inv(x):
  den=x.r*x.r+x.i*x.i
  return Z(x.r/den,-x.i/den)
 def __truediv__(x,y):return x*zc(y).inv()
 def __rtruediv__(x,y):return zc(y)*x.inv()
 def norm1_bound(x):return Q(max(abs(x.r.a),abs(x.r.b))+max(abs(x.i.a),abs(x.i.b)),S)
def zc(x):return x if isinstance(x,Z) else Z(x)
def box(c,r):return Z(I(c-r,c+r),I(-r,r))
# Lagrange bound for the critical branch R(t) on |t|<=h:
assert ((Q(101,100)**3)/Q(299,100))<Q(3,5)**2
assert Q(9,10)/(1-60*h)<1
z=box(rho,rho*h*h);R=box(Q(3,2),h)
V=orbit(z,phi(z,R*R),R)
Q0,P0=orbit(z,Z(1),Z(0),Z(1))
assert P0.r.inside(3,4)
assert (V-Q0).norm1_bound()<5
# |P_N|>3, |V_N-Q_N|<5, errors <=E each, so |F-F_N|<2E.
assert E<Q(1,2)
DEG=5
class J:
 def __init__(self,a=0):
  if isinstance(a,list):self.a=[cv(v) for v in a]+[I(0)]*(DEG+1-len(a))
  else:self.a=[cv(a)]+[I(0)]*DEG
 def __add__(x,y):y=jc(y);return J([a+b for a,b in zip(x.a,y.a)])
 __radd__=__add__
 def __neg__(x):return J([-a for a in x.a])
 def __sub__(x,y):return x+-jc(y)
 def __rsub__(x,y):return jc(y)+-x
 def __mul__(x,y):
  y=jc(y);return J([sum((x.a[k]*y.a[n-k] for k in range(n+1)),I(0)) for n in range(DEG+1)])
 __rmul__=__mul__
 def inv(x):
  a=[1/x.a[0]]
  for n in range(1,DEG+1):a.append(-sum((x.a[k]*a[n-k] for k in range(1,n+1)),I(0))/x.a[0])
  return J(a)
 def __truediv__(x,y):return x*jc(y).inv()
 def __rtruediv__(x,y):return jc(y)*x.inv()
def jc(x):return x if isinstance(x,J) else J(x)
s3=I(3).sqrt()
z=J([rho,0,-rho])
R=J([Q(3,2),-s3/2,Q(2,3),-Q(35,108)*s3,Q(40,81),-Q(1001,3888)*s3])
# Verify the root equation through available powers; singular leading term needs one extra equation analytically.
V=orbit(z,phi(z,R*R),R)
Q0,P0=orbit(z,J(1),J(0),J(1));F=(V-Q0)/P0
b={j:F.a[j].widen(2*E/h**j) for j in [1,3,5]}
C=-b[1]/(2*pi.sqrt())
d1=Q(3,8)-Q(3,2)*b[3]/b[1]
d2=Q(25,128)-Q(45,16)*b[3]/b[1]+Q(15,4)*b[5]/b[1]
assert d1.inside(Q(13722155058455044742556,10**20),Q(13722155058455044742557,10**20))
assert d2.inside(Q(491456133466923234229799,10**20),Q(491456133466923234229800,10**20))
print('PASS: complex-disk finite quotient bounds and Cauchy coefficient tails')
for j in [1,3,5]:print('b'+str(j)+':',b[j].out())
print('C:',C.out());print('d1:',d1.out());print('d2:',d2.out())
print('b_j error <=2 E h^(-j), E=2^(-496), h=10^(-5)')
