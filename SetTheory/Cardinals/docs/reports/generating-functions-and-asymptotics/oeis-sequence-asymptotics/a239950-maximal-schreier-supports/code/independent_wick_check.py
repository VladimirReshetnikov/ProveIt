"""Independent two/three-dimensional Wick derivation of first corrections.
No numerical inference from exact counts and no sequential-saddle formulas.
"""
import sympy as s
from functools import lru_cache
q,u,a,S=s.symbols('q u a S',positive=True)
X,U,Z=s.symbols('X U Z')
variables=(X,U,Z)
dx=lambda f:-q*s.diff(f,q)
ds=lambda f:u*s.diff(f,u)
def at(f):
 return s.simplify(s.expand_log(f.subs({q:s.Rational(2,3),u:s.Rational(1,2)}),force=True).subs(s.log(3),a+s.log(2)))
h=s.log(1-(1-u)*q)-s.log(1-q)
b=-u/(1-u)*s.log(1-(1-u)*q)
L=s.log(u)+s.log(q)-s.log(1-q)/2-s.log(1-(1-u)*q)/2
Id={(0,0):S-a*s.log(2)}
Ld={}
for i in range(5):
 for j in range(5-i):
  if i+j:
   f=-h if i else b
   for _ in range(i-1 if i else 0):f=dx(f)
   for _ in range(j if i else j-1):f=ds(f)
   Id[i,j]=at(f)
  if i+j<=2:
   f=L
   for _ in range(i):f=dx(f)
   for _ in range(j):f=ds(f)
   Ld[i,j]=at(f)

def trunc(p,n,vs=variables):
 return s.Add(*(c*s.prod(v**k for v,k in zip(vs,ex)) for ex,c in s.Poly(s.expand(p),*vs).terms() if sum(ex)<=n))
def homogeneous(p,n,vs):
 return s.Add(*(c*s.prod(v**k for v,k in zip(vs,ex)) for ex,c in s.Poly(s.expand(p),*vs).terms() if sum(ex)==n))

def solve(dim):
 vs=variables[:dim] if dim==2 else variables
 shift=X if dim==2 else X+a*Z+X*Z
 Ipoly=trunc(sum(v*shift**i*U**j/s.factorial(i)/s.factorial(j) for (i,j),v in Id.items()),4,vs)
 if dim==2:
  P=Ipoly-(a+X)*(-s.log(2)+U)
 else:
  P=trunc(Ipoly*(1-Z+Z**2-Z**3+Z**4)-(a+X)*(-s.log(2)+U)+S*(1+Z),4,vs)
 origin={v:0 for v in vs}
 H=s.Matrix([[s.diff(P,v,w).subs(origin) for w in vs] for v in vs])
 C=s.simplify(-H.inv())
 @lru_cache(None)
 def wick(ex):
  if sum(ex)==0:return s.Integer(1)
  if sum(ex)%2:return s.Integer(0)
  i=next(k for k,x in enumerate(ex) if x)
  remain=list(ex);remain[i]-=1
  val=0
  for j in range(dim):
   if remain[j]:
    count=remain[j];nxt=remain.copy();nxt[j]-=1
    val+=count*C[i,j]*wick(tuple(nxt))
  return s.factor(val)
 def expect(poly):
  return s.factor(sum(c*wick(ex) for ex,c in s.Poly(s.expand(poly),*vs).terms()))
 Lpoly=trunc(sum(v*shift**i*U**j/s.factorial(i)/s.factorial(j) for (i,j),v in Ld.items() if i+j),2,vs)
 l1=homogeneous(Lpoly,1,vs);l2=homogeneous(Lpoly,2,vs)
 p3=homogeneous(P,3,vs);p4=homogeneous(P,4,vs)
 f1=-at(dx(h))/12
 pieces=[f1,expect(l2+l1*l1/2),expect(l1*p3),expect(p4),expect(p3*p3)/2]
 total=s.factor(sum(pieces))
 print('dimension',dim)
 print('Hessian =',H)
 print('Gaussian covariance =',C)
 print('correction pieces =',pieces)
 print('correction =',total)
 return total
radial=solve(2)
coefficient=solve(3)
if s.factor(radial+(26*a*a-82*a+29)/(144*(a-1)**2)) != 0:
 raise ValueError('radial correction identity failed')
if s.factor(coefficient-radial+3/(16*S)) != 0:
 raise ValueError('coefficient correction identity failed')
print('coefficient - radial + 3/(16S) =',s.factor(coefficient-radial+3/(16*S)))
print('exact symbolic identity checks: PASS')
