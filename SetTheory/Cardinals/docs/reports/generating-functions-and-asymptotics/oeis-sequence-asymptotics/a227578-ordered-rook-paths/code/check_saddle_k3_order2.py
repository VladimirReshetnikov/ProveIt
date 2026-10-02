"""Independent second correction: nonsymmetric 2D residue, no guessed recurrence or trace-GUE formulas."""
import sympy as s,json,math
from functools import lru_cache
u,v=s.symbols('u v');I=s.I;N=6;q=s.Rational(1,4)
def const(c):return [s.sympify(c)]+[s.Integer(0)]*N
def add(*ps):return [s.expand(sum(p[j] for p in ps)) for j in range(N+1)]
def scale(p,c):return [s.expand(c*x) for x in p]
def mul(a,b):return [s.expand(sum(a[j]*b[n-j] for j in range(n+1))) for n in range(N+1)]
def inv(a):
 b=[1/a[0]]
 for n in range(1,N+1):b.append(s.expand(-sum(a[j]*b[n-j] for j in range(1,n+1))/a[0]))
 return b
def power(a,m):
 b=const(1)
 for _ in range(m):b=mul(a,b)
 return b
def log(a):
 der=[(j+1)*a[j+1] for j in range(N)]+[s.Integer(0)];p=mul(der,inv(a))
 return [s.log(a[0])]+[s.expand(p[j-1]/j) for j in range(1,N+1)]
x=[q*(I*u)**j/s.factorial(j) for j in range(N+1)];y=[q*(I*v)**j/s.factorial(j) for j in range(N+1)]
ox=add(const(1),scale(x,-1));oy=add(const(1),scale(y,-1))
S=add(const(1),scale(mul(x,inv(ox)),-1),scale(mul(y,inv(oy)),-1));z=mul(S,inv(add(const(1),S)));oz=add(const(1),scale(z,-1))
f=log(scale(z,1/q));f[1]=s.expand(f[1]+I*(u+v));assert f[0]==f[1]==0
# residue amplitude: (1-z)^2/z * prod(1-xj)^-2
B=mul(mul(power(oz,2),inv(z)),inv(power(mul(mul(ox,oy),oz),2)))
def diff_over_t(a,b):return [s.expand(a[j+1]-b[j+1]) for j in range(N)]+[s.Integer(0)]
D=power(mul(mul(diff_over_t(x,y),diff_over_t(x,z)),diff_over_t(y,z)),2)
amp=mul(B,D)
# exp(-Nf) after t=N^-1/2; remove Gaussian quadratic
h=[s.Integer(0)]+[-f[j+2] if j+2<=N else s.Integer(0) for j in range(1,N+1)]
E=const(1)
for j in range(1,5):E=add(E,scale(power(h,j),s.Rational(1,s.factorial(j))))
pol=mul(amp,E)
C=[[s.Rational(2,5),s.Rational(-1,5)],[s.Rational(-1,5),s.Rational(2,5)]]
@lru_cache(None)
def moment(a,b):
 if a<0 or b<0 or (a+b)%2:return s.Integer(0)
 if not a+b:return s.Integer(1)
 if a:return (a-1)*C[0][0]*moment(a-2,b)+b*C[0][1]*moment(a-1,b-1)
 return (b-1)*C[1][1]*moment(0,b-2)
def ev(p):return s.factor(sum(c*moment(*powers) for powers,c in s.Poly(p,u,v).terms()))
m0=ev(pol[0]);e1=s.factor(ev(pol[2])/m0);e2=s.factor(ev(pol[4])/m0)
# (n+2)^-4/n^-4 and coefficient conversions
n1=e1-8;n2=e2-10*e1+40
print('N coefficients',e1,e2,'n coefficients',n1,n2)
assert n1==-s.Rational(326,75)
assert n2==s.Rational(1044311,84375)
json.dump(dict(method='Independent nonsymmetric 2D residue, exact polynomial-series arithmetic and correlated Gaussian moments; no recurrence',N_coefficients=[str(e1),str(e2)],n_coefficients=[str(n1),str(n2)]),open('saddle-k3-order2-check.json','w'),indent=2)
