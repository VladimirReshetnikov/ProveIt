"""Direct 3D derivative/Wick evaluation of the second correction. No fits.
Uses a linear covariance-diagonalizing coordinate D=X+a Z only for speed.
The original moving endpoint is v=(a+X)*(1+Z), so v-a=D+D*Z-a*Z**2.
The original phase is I(v,s0+U)/(1+Z)-(a+X)*(s0+U)+S*(1+Z),
with s0=-log(2). Covariance -H**(-1) represents the audited complex
Gaussian contour, not a real probability covariance. Phase degree 6,
log-amplitude degree 4, and first Euler--Maclaurin degree 2 determine d2.
This is a finite first/second coefficient calculation, not an all-orders engine.
The analytic remainder and contour hypotheses are proved in Report195.tex.
"""
import sympy as s
from functools import lru_cache
a,S=s.symbols('a S',positive=True)
q,u=s.symbols('q u',positive=True)
D,U,Z=s.symbols('D U Z'); vs=(D,U,Z)
dx=lambda f:-q*s.diff(f,q)
ds=lambda f:u*s.diff(f,u)
def at(f):
 return s.factor(s.expand_log(f.subs({q:s.Rational(2,3),u:s.Rational(1,2)}),force=True).subs(s.log(3),a+s.log(2)))
h=s.log(1-(1-u)*q)-s.log(1-q)
b=-u/(1-u)*s.log(1-(1-u)*q)
L=s.log(u)+s.log(q)-s.log(1-q)/2-s.log(1-(1-u)*q)/2
Id={(0,0):S-a*s.log(2)}; Ld={}; Ed={}
for i in range(7):
 for j in range(7-i):
  if i+j:
   f=-h if i else b
   for _ in range(i-1 if i else 0):f=dx(f)
   for _ in range(j if i else j-1):f=ds(f)
   Id[i,j]=at(f)
  if 0<i+j<=4:
   f=L
   for _ in range(i):f=dx(f)
   for _ in range(j):f=ds(f)
   Ld[i,j]=at(f)
  if i+j<=2:
   f=-dx(h)/12
   for _ in range(i):f=dx(f)
   for _ in range(j):f=ds(f)
   Ed[i,j]=at(f)
def cut(p,n):
 return s.Add(*(c*s.prod(v**k for v,k in zip(vs,ex)) for ex,c in s.Poly(s.expand(p),*vs).terms() if sum(ex)<=n))
def hom(p,n):
 return s.Add(*(c*s.prod(v**k for v,k in zip(vs,ex)) for ex,c in s.Poly(s.expand(p),*vs).terms() if sum(ex)==n))
# X=D-aZ, so v-a=X+aZ+XZ=D+DZ-aZ².
shift=D+D*Z-a*Z**2
Ipoly=cut(sum(val*shift**i*U**j/s.factorial(i)/s.factorial(j) for (i,j),val in Id.items()),6)
P=cut(Ipoly*sum((-Z)**k for k in range(7))-(a+D-a*Z)*(-s.log(2)+U)+S*(1+Z),6)
Lpoly=cut(sum(val*shift**i*U**j/s.factorial(i)/s.factorial(j) for (i,j),val in Ld.items()),4)
Epoly=cut((1+Z)*sum(val*shift**i*U**j/s.factorial(i)/s.factorial(j) for (i,j),val in Ed.items()),2)
origin=dict.fromkeys(vs,0)
H=s.hessian(P,vs).subs(origin)
C=s.Matrix([[(1-4*a)/(6*(a-1)),-1/(2*(a-1)),0],[-1/(2*(a-1)),-1/(2*(a-1)),0],[0,0,-1/(2*S)]])
if (C+H.inv()).applyfunc(s.factor)!=s.zeros(3):
 raise ValueError('diagonalizing-coordinate covariance identity failed')
if s.factor(P.subs(origin)-2*S)!=0:
 raise ValueError('phase constant identity failed')
if not all(s.diff(P,v).subs(origin)==0 for v in vs):
 raise ValueError('phase gradient does not vanish')
@lru_cache(None)
def wick2(i,j):
 if i+j==0:return s.Integer(1)
 if (i+j)%2:return s.Integer(0)
 if i:
  value=(i-1)*C[0,0]*wick2(i-2,j) if i>=2 else 0
  if j:value+=j*C[0,1]*wick2(i-1,j-1)
 else:value=(j-1)*C[1,1]*wick2(0,j-2)
 return s.factor(value)
def wick(ex):
 i,j,k=ex
 if k%2:return s.Integer(0)
 zm=s.factorial2(k-1)*(-1/(2*S))**(k//2) if k else 1
 return wick2(i,j)*zm
def mean(p):
 return s.factor(sum(c*wick(ex) for ex,c in s.Poly(s.expand(p),*vs).terms()))
r1=hom(P,3)+hom(Lpoly,1)
r2=hom(P,4)+hom(Lpoly,2)+hom(Epoly,0)
r3=hom(P,5)+hom(Lpoly,3)+hom(Epoly,1)
r4=hom(P,6)+hom(Lpoly,4)+hom(Epoly,2)
d1=mean(r2+r1**2/2)
B=-(26*a*a-82*a+29)/(144*(a-1)**2)
if s.factor(d1-B+3/(16*S))!=0:
 raise ValueError('first coefficient identity failed')
print('d1 =',d1,flush=True)
pieces=[]
for name,expr in [('r4',r4),('r1*r3',r1*r3),('r2^2/2',r2**2/2),('r1^2*r2/2',r1**2*r2/2),('r1^4/24',r1**4/24)]:
 v=mean(expr); pieces.append(v)
 print(name,'=',v,flush=True)
d2=s.factor(sum(pieces))
print('d2 =',d2,flush=True)
print('c2 =',s.factor(S*d2),flush=True)
print('d2 expanded in 1/S =',s.collect(s.apart(d2,S),S),flush=True)
radial=s.factor(s.limit(d2,S,s.oo))
print('B2 =',radial,flush=True)
if s.factor(d2-radial+15*B/(16*S)+s.Rational(15,512)/S**2)!=0:
 raise ValueError('second coefficient decomposition failed')
print('d2 = B2 - 15B/(16S) - 15/(512S²): PASS',flush=True)
print('B2 rational =',s.cancel(radial),flush=True)
# Verify the displayed polynomial itself, not merely a limit decomposition.
B2=(676*a**4+3416*a**3-10200*a**2+22172*a-7559)/(41472*(a-1)**4)
expected_d2=B2-15*B/(16*S)-s.Rational(15,512)/S**2
if s.factor(radial-B2)!=0:
 raise ValueError('explicit B2 polynomial identity failed')
if s.factor(d2-expected_d2)!=0:
 raise ValueError('full explicit second coefficient identity failed')
if s.factor(S*d2-(S*B2-s.Rational(15,16)*B-s.Rational(15,512)/S))!=0:
 raise ValueError('conversion c2=S*d2 failed')
print('explicit B2 polynomial identity: PASS')
print('full d2 and c2 identities: PASS')
print('exact second symbolic identity checks: PASS')
