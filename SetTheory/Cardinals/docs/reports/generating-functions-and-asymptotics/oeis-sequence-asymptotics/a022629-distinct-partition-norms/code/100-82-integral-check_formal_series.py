"""Exact all-order logarithmic reversion, with polynomial coefficients in P=pi^2."""
from pathlib import Path
import json, sympy as s
P=s.Symbol('P');N=12
zero=lambda:[s.S(0)]*(N+1)
def normal(a):return [s.expand(x) for x in a]
def add(a,b):return normal([x+y for x,y in zip(a,b)])
def scale(a,c):return normal([x*c for x in a])
def shift(a,k=1):return ([s.S(0)]*k+a)[:N+1]
def mul(a,b):
 return normal([sum(a[j]*b[n-j] for j in range(n+1)) for n in range(N+1)])
one=zero();one[0]=1
z=shift(one)
def inv(a):
 if a[0]!=1:raise ArithmeticError('Unit inverse required')
 q=zero();q[0]=1
 for n in range(1,N+1):q[n]=s.expand(-sum(a[j]*q[n-j] for j in range(1,n+1)))
 return q
def exp(a):
 if a[0]!=0:raise ArithmeticError('Zero constant required')
 q=zero();q[0]=1
 for n in range(1,N+1):q[n]=s.expand(sum(j*a[j]*q[n-j] for j in range(1,n+1))/n)
 return q
def log(a):
 if a[0]!=1:raise ArithmeticError('Unit logarithm required')
 der=[(j+1)*a[j+1] for j in range(N)]+[s.S(0)]
 v=mul(der,inv(a));return [s.S(0)]+[s.expand(v[j-1]/j) for j in range(1,N+1)]
def compose(a,b):
 if b[0]!=0:raise ArithmeticError('Zero composition constant required')
 out=zero()
 for c in a[::-1]:out=mul(out,b);out[0]+=c
 return normal(out)
def D(a):
 der=[(j+1)*a[j+1] for j in range(N)]+[s.S(0)]
 return scale(mul(shift(der,2),inv(add(one,scale(z,-1)))),-1)
rho=inv(add(one,scale(z,-1)));E=zero();constants=[]
for j in range(1,N//2+1):
 c=2*(1-s.Rational(1,2)**(2*j-1))*abs(s.bernoulli(2*j))*2**(2*j)*P**j/(2*s.factorial(2*j))
 constants.append(c);E=add(E,scale(shift(rho),c));rho=D(D(rho))
# T=2(A+A')/(b-1), A=1/(2z)-1+E.
Eprime=scale(shift([(j+1)*E[j+1] for j in range(N)]+[s.S(0)],2),-1)
T=mul(add(add(one,scale(z,-1)),scale(shift(add(E,Eprime)),2)),inv(add(one,scale(z,-1))))
delta=zero()
for _ in range(N):
 zz=mul(z,inv(add(one,shift(delta))));delta=scale(log(compose(T,zz)),-s.Rational(1,2))
zz=mul(z,inv(add(one,shift(delta))))
res=add(mul(exp(scale(delta,2)),compose(T,zz)),scale(one,-1))
if any(s.expand(x)!=0 for x in res):raise ArithmeticError('Saddle residual')
plus=exp(delta);minus=exp(scale(delta,-1));cosh=scale(add(plus,minus),s.Rational(1,2))
# S=cosh(delta)/z + delta*cosh(delta)-exp(delta)+E(zz)*exp(delta)
S=add(add(mul(delta,cosh),scale(plus,-1)),mul(compose(E,zz),plus))
for j in range(N):S[j]+=cosh[j+1]
# Only coefficients through N-1 are complete because division by z loses one order.
forward=[s.expand(S[j]) for j in range(1,N-1)]
corr=zero()
for j,c in enumerate(forward,1):corr[j]=c
eps=zero()
for _ in range(N):
 zz=mul(z,inv(add(one,shift(eps))))
 den=add(add(one,scale(z,-1)),shift(add(eps,compose(corr,zz))))
 eps=add(log(add(one,scale(z,-1))),scale(log(den),-1))
zz=mul(z,inv(add(one,shift(eps))))
res=add(mul(exp(eps),add(add(one,scale(z,-1)),shift(add(eps,compose(corr,zz))))),scale(add(one,scale(z,-1)),-1))
if any(s.expand(x)!=0 for x in res):raise ArithmeticError('Inverse residual')
inverse=exp(scale(eps,2))
expected=[P/6,P/6,P/6-P**2/72,P/6+P**2/40]
if forward[:4]!=expected:raise ArithmeticError('Low-order forward formulas differ')
expectedinv={2:-P/3,3:-P/3,4: P**2/9-P/3}
for j,v in expectedinv.items():
 if s.expand(inverse[j]-v)!=0:raise ArithmeticError('Low-order inverse formulas differ')
if any(s.sympify(x).has(s.Float) for x in forward+inverse):raise ArithmeticError('Inexact symbolic coefficient')
out={'status':'Exact symbolic arithmetic; P denotes pi^2. Every displayed coefficient uses a completed truncation order.','forward_s_j':{str(j):str(c) for j,c in enumerate(forward,1)},'inverse_v_j':{str(j):str(s.expand(inverse[j])) for j in range(2,N-1)},'saddle_residual_orders':N,'inverse_residual_orders':N,'all_checks_passed':True}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
