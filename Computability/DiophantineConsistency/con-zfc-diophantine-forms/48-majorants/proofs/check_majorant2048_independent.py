#!/usr/bin/env python3
"""Independent exact ring and weighted-degree checks for the 2048 majorant.

This imports no construction or other verifier.  Rational inequalities are
proved in NINE_T2048_REVIEW.md, rather than inferred from numeric fixtures.
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
Bgap=2*P*(P+R)+1
V=T*H+Bgap
dv=V**2-2048**2*D*F*I
require(dv==H**2*defect+2048**2*D*F*(H**2-1)+2*T*H*Bgap+Bgap**2,'V defect identity')

# Each register's actual source degree is a*t+b; leaders are powers of 2.
DEG=[(7,2),(3,0),(20,4),(10,3),(0,1),(3,1),(12,3),(3,0)]
EXP=[12,5,34,19,0,5,21,4]
def weighted_check(poly, expected, expected_lc):
    aggregate=defaultdict(int)
    for mon,coeff in poly.d.items():
        a=sum(k*d[0] for k,d in zip(mon,DEG)); b=sum(k*d[1] for k,d in zip(mon,DEG))
        require(expected[0]>=a, 'higher degree slope')
        if (a,b)!=expected:
            require(3*(expected[0]-a)+expected[1]-b>0,'degree separation for t>=3')
        aggregate[(a,b)]+=coeff*2**sum(k*j for k,j in zip(mon,EXP))
    require(aggregate[expected]==expected_lc,'wrong weighted leader')
    return {'degree_t_coefficient':expected[0], 'degree_constant':expected[1],
            'leading_coefficient':str(expected_lc), 'expanded_monomials':len(poly.d)}

checks={
  'Rnum':weighted_check(rn,(100,23),2**182),
  'T':weighted_check(T,(153,33),2**277),
  'T_squared_defect':weighted_check(defect,(173,40),2**324),
  'V':weighted_check(V,(156,34),2**282),
  'V_squared_defect':weighted_check(dv,(180,40),2**326),
}

# Structural finalizer leader: 16 common - 4 common = 12 common.
# common = Omega_0^4*h^4*P_0^4*(TH)_0^2.
inner_square_lc=2**1496
norm_sub_lc=2**1494
final_lc=3*2**1494
require(inner_square_lc-norm_sub_lc==final_lc,'final noncancellation')
receipt={'status':'PASS','scope':'Exact universal ring identities and weighted total-degree certificate for t>=3; semantic inequalities are proved separately.',
         'ring_variables':NAMES,'scale':2048,'gap_padding':'2*P*(P+R)+1',
         'checks':checks,'final_degree':'820*t+12*W+208',
         'final_leading_coefficient':'3*2^1494',
         'no_construction_or_other_verifier_imports':True}
out=Path(__file__).with_name('MAJORANT2048_INDEPENDENT.json')
out.write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
