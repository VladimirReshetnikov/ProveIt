#!/usr/bin/env python3
"""Exact ring and positivity checks for the new 4096 majorant.

This imports no construction or other verifier. Rational inequalities are
proved in PROOF.md using the retained upstream majorant argument, rather
than inferred from numeric fixtures.
"""
from collections import defaultdict
import json
from pathlib import Path

NV = 3

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
            n>>=1
            if n: a=a*a
        return result
    def __eq__(self, other): return self.d==aspoly(other).d

def aspoly(x): return x if isinstance(x,Poly) else Poly(x)
def variable(k): return Poly({tuple(int(i==k) for i in range(NV)):1})

ROOT=Path(__file__).resolve().parent
A,C,i=[variable(k) for k in range(NV)]
D=(A*A-1)*C*C+1;e=i*(4*A-5)*C;Lm=C*D+1-A
F=e*e*D*D*(D-1)+1;G=A+F*Lm;Ns=2*G+Lm
N1=2*e*e*D*(D-1)*Lm+3*C;N2=2*e*e*(D-1)*Lm
N3=2*e*e*(Lm-C);N4=2*e*e*C
T=e*((2048*D*D-1024*D-256)*Ns-128*N1-80*N2-56*N3-42*N4+i*i*(1568-448*A+288*C))+640*i+4096
tn=2048*D**7-1024*D**6-256*D**5-128*D**4-80*D**3-56*D**2-42*D-33
dn=109824*D**6+36608*D**5+18304*D**4+9984*D**3+5460*D**2+2772*D+1089
require(tn**2-2048**2*D**13*(D-1)==dn,'approximant square identity')
Rn=D**5*T-e*tn*Ns
rem=Rn-4096*D**5
from math import comb
shift=defaultdict(int)
for (a,c,j),val in rem.d.items():
 for aa in range(a+1):
  for cc in range(c+1): shift[(aa,cc,j)]+=val*comb(a,aa)*3**(a-aa)*comb(c,cc)
shift={m:v for m,v in shift.items() if v}
file=json.loads((ROOT/'data/order7_majorant_positive_certificate.json').read_text())
claimed={tuple(r['powers']):r['coefficient'] for r in file['terms']}
require(len(claimed)==len(file['terms'])==264,'264 distinct positivity terms')
require(shift==claimed,'exact shifted positivity certificate')
require(all(v>0 for v in shift.values()),'all coefficients positive')
require(any(m[0]==0 and m[1]==0 and v>0 for m,v in shift.items()),'strict positivity at boundary')
require({m:v for m,v in Rn.d.items() if sum(x*w for x,w in zip(m,(18729,1,1)))==187305}=={(10,12,3):2880},'exact weighted remainder head')
require(max(sum(x*w for x,w in zip(m,(18729,1,1))) for m in Rn.d)==187305,'remainder weighted degree')
X=e*e*D**3*(D-1)
left=D**10*(T*T-4096**2*D*F*G*G)
right=e*e*dn*Ns*Ns+2048**2*D**10*(X*Lm*Lm-4*D*G*(C*D+1))+2*e*tn*Ns*Rn+Rn*Rn
require(left==right,'D10 majorant defect identity')
# Universal two-defect norm identity in three arbitrary polynomials is algebraically
# the expansion (X+2Omega²V0V1)²-4Omega⁴a0a1; the report states it explicitly.
print(json.dumps({'status':'PASS','positive_terms':len(shift),'boundary_terms':[{'i_power':m[2],'coefficient':v} for m,v in sorted(shift.items()) if m[:2]==(0,0)],'majorant_scale':4096,'remainder_degree':187305,'remainder_leading_term':'2880 A^10 C^12 i^3','identities':['tn7 square identity','exact T7 remainder','positive shifted coefficient certificate','D10 majorant defect identity']},indent=2))
