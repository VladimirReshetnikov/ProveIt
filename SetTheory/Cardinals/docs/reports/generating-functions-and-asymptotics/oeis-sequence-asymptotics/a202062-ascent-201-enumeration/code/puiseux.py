#!/usr/bin/env python3
"""Exact Puiseux and all-orders coefficient generator for A202062.

Run with --relative-order M (at least the first three coefficients are checked).
All calculations use Q(rho)[delta] / (delta**2 - epsilon), without float fitting.
"""
import sympy as sp
from functools import reduce
from pathlib import Path
HERE=Path(__file__).resolve().parent
import argparse
parser=argparse.ArgumentParser()
parser.add_argument("--relative-order",type=int,default=3)
args=parser.parse_args()
M=max(args.relative_order,3)
r=sp.symbols('r'); d=r**3+5*r*r-8*r+1;rho=sp.CRootOf(d,1);K=sp.QQ.algebraic_field(rho)
k=lambda e:K.from_sympy(e)
z=K.zero;o=K.one;R=K.unit
# actual generator may use unit chosen root
assert K.to_sympy(R)==rho
class E:
 def __init__(self,a=0,b=0):self.a=a if hasattr(a,'rep') else k(sp.sympify(a));self.b=b if hasattr(b,'rep') else k(sp.sympify(b))
 def __add__(self,other):
  if not isinstance(other,E):other=E(other)
  return E(self.a+other.a,self.b+other.b)
 __radd__=__add__
 def __neg__(self):return E(-self.a,-self.b)
 def __sub__(self,o):return self+-asE(o)
 def __rsub__(self,o):return asE(o)+-self
 def __mul__(self,other):
  other=asE(other);return E(self.a*other.a+self.b*other.b*eps,self.a*other.b+self.b*other.a)
 __rmul__=__mul__
 def inv(self):
  den=self.a*self.a-self.b*self.b*eps;return E(self.a/den,-self.b/den)
 def __truediv__(self,o):return self*asE(o).inv()
 def __rtruediv__(self,o):return asE(o)*self.inv()
 def __eq__(self,o):o=asE(o);return self.a==o.a and self.b==o.b
 def show(self):return str(ks(self.a))+' + sqrt(eps)*('+str(ks(self.b))+')'
 def num(self):return float(K.to_sympy(self.a).evalf(20))+float(K.to_sympy(self.b).evalf(20))*float(K.to_sympy(eps).evalf(20))**.5

def asE(a):return a if isinstance(a,E) else E(a)
def ks(a):
 # convert generator RootOf to formal symbol
 return sp.expand(K.to_sympy(a).xreplace({rho:r}))
# derivatives at critical pair
T=(-3*R*R-17*R+8)/7
Axx=6*(1-R)**2*T+2*(R*R-1)
Ax=-2*(1-R)*T**3+2*R*T*T+T+1
eps=2*R*Ax/Axx
print('rho=',rho.evalf(30),'tau=',ks(T),'eps=',ks(eps),float(K.to_sympy(eps).evalf()),flush=True)
N=max(20,2*M+10)
Zero=E(0)
def add(*arrs):return [sum((arr[i] if i<len(arr) else Zero for arr in arrs),Zero) for i in range(N+1)]
def scale(arr,a):return [t*a for t in arr]
def mul(a,b):
 c=[Zero for i in range(N+1)]
 for i,ai in enumerate(a):
  for j,bj in enumerate(b[:N+1-i]):c[i+j]=c[i+j]+ai*bj
 return c
X=[E(R),Zero,E(-R)]+[Zero]*(N-2);one=[E(1)]+[Zero]*N
XX=mul(X,X);AX=mul(add(one,scale(X,-1)),add(one,scale(X,-1)))
def cubic(P):return add(mul(AX,mul(mul(P,P),P)),mul(add(XX,scale(one,-1)),mul(P,P)),mul(X,P),X)
P=[E(T),E(0,1)]+[Zero]*(N-1)
for m in range(2,N):
 C=cubic(P)[m+1]
 P[m]=-C/E(Axx,0)/E(0,1)
assert all(e==0 for e in cubic(P)[:N+1])
print('P exact through order',N-1,flush=True)
# G numerator 7(x^3-2x²+2x-1)P²+(8x³-16x²+6x+8)P+x³+18x²-20x-1
XXX=mul(XX,X)
GN=add(scale(mul(add(XXX,scale(XX,-2),scale(X,2),scale(one,-1)),mul(P,P)),7),mul(add(scale(XXX,8),scale(XX,-16),scale(X,6),scale(one,8)),P),XXX,scale(XX,18),scale(X,-20),scale(one,-1))
# 1/(8 x^3)=1/(8rho^3) (1-t²)^−3
invX3=[E(sp.binomial(i//2+2,2))/(8*E(R**3)) if i%2==0 else Zero for i in range(N+1)]
G=mul(GN,invX3)
for m in [1,3,5]:assert G[m]==0
print('PASS singular odd coefficients 1,3,5 vanish exactly',flush=True)
for m in [7,9,11,13]:print('beta'+str(m),G[m].show(),'num',G[m].num(),flush=True)
a0=sp.Rational(7,2)
g1=lambda a:a*(a+1)/2
g2=lambda a:a*(a+1)*(a+2)*(3*a+1)/24
g3=lambda a:a*a*(a+1)**2*(a+2)*(a+3)/48
R1=G[9]/G[7];R2=G[11]/G[7];R3=G[13]/G[7]
c1=E(g1(a0))-sp.Rational(9,2)*R1
c2=E(g2(a0))-sp.Rational(9,2)*R1*g1(a0+1)+sp.Rational(99,4)*R2
c3=E(g3(a0))-sp.Rational(9,2)*R1*g2(a0+1)+sp.Rational(99,4)*R2*g1(a0+2)-sp.Rational(1287,8)*R3
for j,cj in enumerate([c1,c2,c3],1):print('relative c'+str(j),cj.show(),'num',cj.num(),flush=True)
C=G[7].num()/float(sp.gamma(-sp.Rational(7,2)))
print('C=',C,flush=True)
open(HERE/'puiseux-results.txt','w').write('\n'.join(['eps='+str(ks(eps)),'beta7='+G[7].show(),'beta9='+G[9].show(),'beta11='+G[11].show(),'beta13='+G[13].show(),'c1='+c1.show(),'c2='+c2.show(),'c3='+c3.show(),'C numerical='+str(C)]))

# General all-orders transfer generator.
def gammas(alpha,m):
 qs=[None]+[sp.Rational((-1)**(j+1),j*(j+1))*(sp.bernoulli(j+1,-alpha)-sp.bernoulli(j+1,1)) for j in range(1,m+1)]
 gs=[sp.Integer(1)]
 for mm in range(1,m+1):gs.append(sp.expand(sum(j*qs[j]*gs[mm-j] for j in range(1,mm+1))/mm))
 return gs
gamma_cache={j:gammas(sp.Rational(7,2)+j,M-j) for j in range(M+1)}
coeffs=[]
for m in range(M+1):
 cm=sum((G[7+2*j]/G[7])*((-1)**j*sp.rf(sp.Rational(9,2),j))*gamma_cache[j][m-j] for j in range(m+1))
 assert cm.b==z
 coeffs.append(cm)
 print('allorder_c'+str(m)+' = '+str(ks(cm.a)),flush=True)
assert coeffs[1]==c1 and coeffs[2]==c2 and coeffs[3]==c3
open(HERE/'relative-coefficients.txt','w').write('\n'.join('c'+str(m)+'='+str(ks(cm.a)) for m,cm in enumerate(coeffs)))
