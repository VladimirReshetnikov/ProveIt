from fractions import Fraction as F
from math import factorial,comb,sqrt,pi
from functools import lru_cache
import json, sympy as s
from pathlib import Path
OUT=Path(__file__).resolve().parent.parent/'checks'
# Independent construction: expand log of the raw moment series itself,
# rather than using the producer's cumulant recurrence.
def add(a,b):
 c=a.copy()
 for k,v in b.items():
  c[k]=c.get(k,F(0))+v
  if not c[k]: del c[k]
 return c
def scale(a,v): return {k:w*v for k,w in a.items() if w*v}
def mul(a,b,N):
 c={}
 for (h,u,x),v in a.items():
  for (i,j,k),w in b.items():
   if h+i<=N:
    t=(h+i,u+j,x+k); c[t]=c.get(t,F(0))+v*w
 return {k:v for k,v in c.items() if v}
N=9
M={}
for r in range(1,N+1):
 p={0:F(1)}
 for a in range(1,r+1):
  q={}
  for i,v in p.items():
   for j in range((N-r-i)//2+1): q[i+2*j]=q.get(i+2*j,F(0))+v*(-a)**j
  p=q
 for h,v in p.items(): M[(r+h,r,0)]=v
log={}; power={(0,0,0):F(1)}
for j in range(1,N+1):
 power=mul(power,M,N)
 log=add(log,scale(power,F((-1)**(j+1),j)))
log=add(log,{(1,1,0):F(-1)})
E={}
for (h,u,x),v in log.items():
 if h-2<=7: E=add(E,{(h-2,u,0):v})
 if h-1<=7: E=add(E,{(h-1,u,1):v})
E=add(E,{(0,2,0):F(-1,2)})
assert all(h>=1 for h,u,x in E)
A={(0,0,0):F(1)}; power=A.copy()
for j in range(1,8):
 power=mul(power,E,7); A=add(A,scale(power,F(1,factorial(j))))
x=s.symbols('x'); polys={}
for j in range(1,8):
 expr=0
 for (h,u,d),v in A.items():
  if h==j: expr-=s.Rational(v.numerator,v.denominator)*x**d*s.hermite_prob(u-1,-x)
 polys[j]=s.factor(expr)
print('CENTRAL P1..P4:')
for j in range(1,5): print(j,polys[j])
print('DIAGONAL THROUGH 7:',{j:str(polys[j].subs(x,0)) for j in polys})
# Count actual words by a direct combinatorial dynamic program.
def count(m,k):
 @lru_cache(None)
 def dp(rem,q):
  if not any(rem): return int(q==k)
  ans=0
  for a in range(k):
   if rem[a]:
    r=list(rem);r[a]-=1
    ans+=dp(tuple(r),q+int(a==q))
  return ans
 return dp((m,)*k,0)
counts={n:count(n,n) for n in range(1,6)}
print('DIRECT WORD COUNTS:',counts)
# Independent exact simplex integral: coefficient convolution and single factorial denominator.
def prob(m,k):
 a=[(-1)**j*factorial(m-1)//factorial(m-1-j) for j in range(m)]
 b=[1]
 for _ in range(k):
  c=[0]*(len(b)+m-1)
  for i,v in enumerate(b):
   for j,w in enumerate(a): c[i+j]+=v*w
  b=c
 D=factorial(m*k)
 return F(m**k*sum(v*(D//factorial(k+j)) for j,v in enumerate(b)),D)
p40=prob(40,40)
print('EXACT n40 scaled:',sqrt(40)*(float(p40)-.5),'limit',4/(3*sqrt(2*pi)))
results={'central':{str(j):str(polys[j]) for j in range(1,5)},'diagonal':{str(j):str(polys[j].subs(x,0)) for j in polys},'word_counts':counts,'n40_scaled':sqrt(40)*(float(p40)-.5)}
(OUT/'independent-central-results.json').write_text(json.dumps(results,indent=2)+'\n')
# Solve first two inverse corrections with formal Taylor coefficients.
z,a,b=s.symbols('z a b'); P1=polys[1];P2=polys[2]
# At x=-z+a h+b h^2: CDF correction is -a h+(-b-z*a*a/2)h^2;
# phi correction is z*a*h; polynomial derivative is a*P1'.
aa=s.factor(P1.subs(x,-z))
bb=s.factor((-z*aa*aa/2+aa*(s.diff(P1,x)+z*P1).subs(x,-z)+P2.subs(x,-z)))
assert s.factor(aa-(z*z+8)/6)==0
assert s.factor(bb-z*(z*z+38)/72)==0
print('INVERSE k coefficients:',aa,bb)
for m in range(1,5):
 for k in range(1,6):
  W=factorial(m*k)//factorial(m)**k
  assert prob(m,k)*W==count(m,k),(m,k)
print('RECTANGULAR DP/SIMPLEX CHECK: all 20 pairs, m=1..4, k=1..5, agree')
import mpmath as mp
mp.mp.dps=70
print('CENTRAL R=4 ERROR / h^5 (bounded-window diagnostic):')
for m in [8,16,32]:
 for shift in [-round(sqrt(m)),0,round(sqrt(m))]:
  k=m+shift; xx=mp.mpf(shift)/mp.sqrt(m); h=1/mp.sqrt(m)
  exact=prob(m,k); exact=mp.mpf(exact.numerator)/exact.denominator
  approx=mp.erfc(xx/mp.sqrt(2))/2
  phi=mp.exp(-xx**2/2)/mp.sqrt(2*mp.pi)
  for j in range(1,5): approx+=phi*s.lambdify(x,polys[j],'mpmath')(xx)*h**j
  print(m,k,mp.nstr((exact-approx)/h**5,18))
