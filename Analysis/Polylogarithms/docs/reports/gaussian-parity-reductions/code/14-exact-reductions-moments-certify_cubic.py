#!/usr/bin/env python3
"""Rational outward interval certificate for integral_0^1 log(Gamma(x))^3 dx.

The finite calculation uses only integer arithmetic and exact Bernoulli numbers
from SymPy.  Decimal digits printed are outward bounds, not floating point
approximations.  The analytic remainder is derived in article/sections/05_gamma.tex.
"""
import argparse
import json
import math
from pathlib import Path
from sympy import bernoulli

parser = argparse.ArgumentParser()
parser.add_argument('--order', type=int, default=360)
parser.add_argument('--digits', type=int, default=130)
parser.add_argument('--output', default=None)
args = parser.parse_args()
P = args.digits
assert P >= 20, "Use at least 20 fixed-point digits."
S = 10 ** P

class I:
    __slots__ = ('lo','hi')
    def __init__(self, lo, hi=None):
        self.lo = int(lo)
        self.hi = int(lo if hi is None else hi)
        assert self.lo <= self.hi
    @staticmethod
    def rat(n,d=1):
        assert d > 0
        return I(n*S//d, -((-n*S)//d))
    def __add__(a,b):
        if isinstance(b,int): b=I.rat(b)
        return I(a.lo+b.lo,a.hi+b.hi)
    __radd__=__add__
    def __neg__(a): return I(-a.hi,-a.lo)
    def __sub__(a,b): return a+(-b if isinstance(b,I) else -I.rat(b))
    def __mul__(a,b):
        if isinstance(b,int):
            return I(a.lo*b,a.hi*b) if b>=0 else I(a.hi*b,a.lo*b)
        pp=[a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi]
        return I(min(pp)//S,-((-max(pp))//S))
    __rmul__=__mul__
    def div(a,d):
        assert isinstance(d,int) and d>0
        return I(a.lo//d,-((-a.hi)//d))
    def enlarge(a,r):
        assert r>=0
        return I(a.lo-r,a.hi+r)

def decimal(q):
    sign='-' if q<0 else ''
    q=abs(q)
    return sign+str(q//S)+'.'+str(q%S).zfill(P)

def log2_interval():
    # ln 2 = 2 atanh(1/3), with a positive geometric upper bound.
    m=P+30
    v=I(0)
    for j in range(m): v += I.rat(2,(2*j+1)*3**(2*j+1))
    tail=I.rat(9,4*(2*m+1)*3**(2*m+1))
    return I(v.lo,v.hi+tail.hi)

B={j: (int(bernoulli(2*j).p),int(bernoulli(2*j).q)) for j in range(1,97)}
LN2=log2_interval()

def euler_interval():
    N=128; m=96
    v=sum((I.rat(1,k) for k in range(1,N+1)),I(0))
    v=v-7*LN2-I.rat(1,2*N)
    for j in range(1,m):
        num,den=B[j]
        v += I.rat(num,den*2*j*N**(2*j))
    num,den=B[m]
    err=I.rat(abs(num),den*2*m*N**(2*m)).hi
    return v.enlarge(err)

def zeta_interval(s):
    N=128
    v=sum((I.rat(1,k**s) for k in range(1,N)),I(0))
    if s>=64:
        # sum through N-1, with integral tail bounds for a decreasing kernel.
        lo=I.rat(1,(s-1)*N**(s-1))
        hi=I.rat(1,(s-1)*(N-1)**(s-1))
        return I(v.lo+lo.lo,v.hi+hi.hi)
    m=96
    v+=I.rat(1,(s-1)*N**(s-1))+I.rat(1,2*N**s)
    for j in range(1,m):
        num,den=B[j]
        v+=I.rat(num*math.comb(s+2*j-2,2*j-1),den*2*j*N**(s+2*j-1))
    num,den=B[m]
    err=I.rat(abs(num)*math.comb(s+2*m-2,2*m-1),den*2*m*N**(s+2*m-1)).hi
    return v.enlarge(err)

def convolution(a,b):
    out=[I(0) for _ in range(len(a)+len(b)-1)]
    # Inputs are nonnegative.  Rounding is performed after each product.
    for j,x in enumerate(a):
        if x.lo==x.hi==0: continue
        for k,y in enumerate(b):
            if y.lo==y.hi==0: continue
            assert x.lo >= 0 and y.lo >= 0, "Positive-convolution precondition failed"
            z=I(x.lo*y.lo//S,-((-x.hi*y.hi)//S))
            out[j+k]=out[j+k]+z
    return out

def J(j,p):
    # Integral_0^(1/2) x^j (-log x)^p dx.
    r=j+1
    val=I.rat(math.factorial(p),r**(p+1))
    power=I.rat(1)
    total=I.rat(1)
    for ell in range(1,p+1):
        power=power*LN2
        total += power*I.rat(r**ell,math.factorial(ell))
    return (val*total).div(2**r)

M=args.order
assert M>=2
G=euler_interval()
Z2=zeta_interval(2)
b=[I(0),G]+[zeta_interval(j).div(j) for j in range(2,M+1)]
b2=convolution(b,b)
b3=convolution(b2,b)
v=J(0,3)
for j in range(1,len(b)): v += ((-1)**j)*3*b[j]*J(j,2)
for j in range(2,len(b2)): v += ((-1)**j)*3*b2[j]*J(j,1)
for j in range(4,len(b3),2): v += 2*b3[j]*J(j,0)
D=(2*Z2).div(M+1)
D2=D*D; D3=D2*D
E=3*D*(J(M+1,2)+J(M+1,0))+3*D2*(J(2*M+2,1)+J(2*M+2,0))+2*D3*J(3*M+3,0)
answer=v.enlarge(E.hi)
lo=decimal(answer.lo); hi=decimal(answer.hi)
common=0
for a,b in zip(lo,hi):
    if a!=b: break
    common+=1
result={
 'definition':'integral_0^1 log(Gamma(x))^3 dx',
 'arithmetic':'integer fixed-point outward intervals; exact Bernoulli inputs',
 'order':M,'fixed_point_decimal_digits':P,
 'lower':lo,'upper':hi,
 'width_upper':decimal(answer.hi-answer.lo),
 'analytic_remainder_upper':decimal(E.hi),
 'common_decimal_digits': max(0,common-lo.index('.')-1),
 'euler_gamma_lower':decimal(G.lo),'euler_gamma_upper':decimal(G.hi),
 'zeta2_lower':decimal(Z2.lo),'zeta2_upper':decimal(Z2.hi),
 'log2_lower':decimal(LN2.lo),'log2_upper':decimal(LN2.hi),
}
destination=Path(args.output) if args.output else Path(__file__).with_name('cubic_certificate.json')
destination.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
