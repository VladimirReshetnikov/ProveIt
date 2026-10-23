#!/usr/bin/env python3
"""Independent exact ring and weighted-degree checks for the 2048 majorant.

This imports no construction or other verifier.  Rational inequalities are
proved in upstream/HIGHER_MAJORANT.md, rather than inferred from numeric fixtures.
"""
from collections import defaultdict
import json
from pathlib import Path

NV = 8
NAMES = ('A', 'C', 'D', 'e', 'i', 'H', 'P', 'R')

def require(value, message):
    if not value:
        raise RuntimeError(message)

class Poly:
    def __init__(self, value=0):
        self.d = {k:v for k,v in value.items() if v} if isinstance(value, dict) else ({(0,)*NV:value} if value else {})
    def __add__(self, other):
        other = other if isinstance(other, Poly) else Poly(other)
        out = defaultdict(int, self.d)
        for m,c in other.d.items(): out[m] += c
        return Poly(out)
    __radd__ = __add__
    def __neg__(self): return Poly({m:-c for m,c in self.d.items()})
    def __sub__(self, other): return self + -aspoly(other)
    def __rsub__(self, other): return aspoly(other) + -self
    def __mul__(self, other):
        other=aspoly(other); out=defaultdict(int)
        for m,c in self.d.items():
            for n,b in other.d.items(): out[tuple(x+y for x,y in zip(m,n))] += c*b
        return Poly(out)
    __rmul__=__mul__
    def __pow__(self,n):
        require(isinstance(n,int) and n>=0,'exponent domain')
        result=Poly(1); a=self
        while n:
            if n&1: result=result*a
            a=a*a; n>>=1
        return result
    def __eq__(self, other): return self.d==aspoly(other).d

def aspoly(x): return x if isinstance(x,Poly) else Poly(x)
def variable(k): return Poly({tuple(int(i==k) for i in range(NV)):1})
A,C,D,e,i,H,P,R=[variable(k) for k in range(NV)]
L=C*D+1-A
F=(D-1)*D**2*e**2+1
G=A+F*L
I=(G**2-1)*H**2+1
X=e**2*D**3*(D-1)
N=2*G+L
Ns=[2*e**2*D*(D-1)*L+3*C,
    2*e**2*(D-1)*L,
    2*e**2*(L-C), 2*e**2*C]
rs=[3-A,3*C*D+3-A]
rs.extend([2*e**2*(A-1)*D**2+rs[1],
           2*e**2*(1-A-C)*D**3+2*e**2*(A-1)*D**2+rs[1]])
for k in range(4): require(N==D**(k+1)*Ns[k]+rs[k],f'remainder {k+1}')
tn=1024*D**6-512*D**5-128*D**4-64*D**3-40*D**2-28*D-21
dn=33792*D**5+10560*D**4+4928*D**3+2464*D**2+1176*D+441
require(tn**2-1024**2*D**11*(D-1)==dn,'square approximation identity')
cor=256*i*(e**2+2)+2048
T=e*((1024*D**2-512*D-128)*N-64*Ns[0]-40*Ns[1]-28*Ns[2]-21*Ns[3])+cor
rn=e*(64*rs[0]*D**3+40*rs[1]*D**2+28*rs[2]*D+21*rs[3])+cor*D**4
require(D**4*T==e*tn*N+rn,'T identity')
require(D*F==X+D,'DF identity')
require(G==e**2*D**2*(D-1)*L+C*D+1,'G identity')
defect=T**2-2048**2*D*F*G**2
rhs=e**2*dn*N**2+1024**2*D**8*(X*L**2-4*D*G*(C*D+1))+2*e*tn*N*rn+rn**2
require(D**8*defect==rhs,'division-free defect identity')
Bgap=0
V=T*H+Bgap
dv=V**2-2048**2*D*F*I
require(dv==H**2*defect+2048**2*D*F*(H**2-1)+2*T*H*Bgap+Bgap**2,'V defect identity')


# New two-defect norm identity, checked in eight algebraically independent variables.
a,b,x,y,o,t,d0,d1=[variable(k) for k in range(NV)]
a=x*x-d0;b=y*y-d1
theta=t-o*(x+y)
inner=theta*theta-o*o*(a+b)
final=inner*inner-4*o**4*a*b
small=t*t-2*t*o*(x+y)+o*o*(d0+d1)
expanded=small*small+4*o*o*x*y*small+4*o**4*(d0*y*y+a*d1)
require(final==expanded,'two-defect norm expansion')
print(json.dumps({'status':'PASS','scope':'Exact ring identities only; inequalities reviewed separately','scale':2048,'identities':['four polynomial quotient remainders','rational square-root approximant','D4*T identity','DF identity','G identity','D8*defect identity','V1 squared defect','two-defect norm expansion']},indent=2))
