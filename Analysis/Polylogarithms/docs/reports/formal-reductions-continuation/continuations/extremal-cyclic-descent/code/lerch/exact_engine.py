#!/usr/bin/env python3
"""Exact rational certificates for the Lerch-boundary continuation.

Python >=3.10, standard library only. No floating-point arithmetic enters
any proof certificate. Run from any directory; output is written to results/lerch.

Arithmetic engine copied from the incoming ProveIt Lerch boundary report:
proveit_lerch_boundary_research/polylog_lerch_boundary/verification/certify.py
as inspected at repository commit a0a90ef31877f98be437191c48b46f02d5456867.
Only the output directory and this attribution were adapted for this package.
The theorem supplying the Euler--Maclaurin remainder is proved in article.tex.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial
from pathlib import Path
import json

@dataclass(frozen=True)
class I:
    lo: Q
    hi: Q
    def __post_init__(self):
        if self.lo > self.hi:
            raise ValueError('Reversed interval')
    @staticmethod
    def point(x):
        return I(Q(x), Q(x))
    def __add__(self, other):
        b = other if isinstance(other, I) else I.point(other)
        return I(self.lo+b.lo, self.hi+b.hi)
    __radd__=__add__
    def __neg__(self): return I(-self.hi,-self.lo)
    def __sub__(self,other): return self + (-other if isinstance(other,I) else -Q(other))
    def __rsub__(self,other): return -self+other
    def __mul__(self, other):
        b=other if isinstance(other,I) else I.point(other)
        z=[self.lo*b.lo,self.lo*b.hi,self.hi*b.lo,self.hi*b.hi]
        return I(min(z),max(z))
    __rmul__=__mul__
    def __truediv__(self,other):
        b=other if isinstance(other,I) else I.point(other)
        if b.lo <= 0 <= b.hi: raise ZeroDivisionError('Interval contains zero')
        return self*I(1/b.hi,1/b.lo)
    def __pow__(self,n):
        if not isinstance(n,int) or n<0: raise ValueError('Nonnegative integer exponent required')
        if n==0:return I.point(1)
        if n%2:
            return I(self.lo**n,self.hi**n)
        z=[self.lo**n,self.hi**n]
        return I(Q(0) if self.lo<=0<=self.hi else min(z),max(z))
    @property
    def sign(self):return 1 if self.lo>0 else -1 if self.hi<0 else 0

DIGITS=70
SCALE=10**DIGITS

def outward(z:I)->I:
    """Round outward to a rational fixed-point grid."""
    return I(Q((z.lo*SCALE).__floor__(),SCALE),Q((z.hi*SCALE).__ceil__(),SCALE))

@lru_cache(None)
def log_unit(y:Q)->I:
    if not 1<=y<=2:raise ValueError('Range reduction failed')
    u=(y-1)/(y+1)
    M=90
    u2=u*u;term=u;s=Q(0)
    for j in range(M):
        s+=term/(2*j+1);term*=u2
    rem=2*term/((2*M+1)*(1-u2))
    return outward(I(2*s,2*s+rem))

@lru_cache(None)
def logq(x:Q)->I:
    x=Q(x)
    if x<=0:raise ValueError('Real logarithm requires a positive argument')
    y=x;j=0
    while y<1:y*=2;j-=1
    while y>=2:y/=2;j+=1
    return outward(log_unit(y)+j*log_unit(Q(2)))

@lru_cache(None)
def elementary(k:int)->tuple[Q,...]:
    if k<0:raise ValueError('Negative k')
    c=[Q(1)]
    for j in range(1,k+1):
        c.append(Q(0))
        for i in range(j,0,-1):c[i]+=c[i-1]/j
    return tuple(c)

@lru_cache(None)
def polynomial(n:int,k:int)->tuple[Q,...]:
    """Ascending coefficients of B_{n,k}(x)."""
    if n<0 or k<0:raise ValueError('Indices must be nonnegative')
    c=[Q(0)]*(n+1)
    for i,e in enumerate(elementary(k)[:n+1]):
        c[n-i]=Q(factorial(n),factorial(n-i))*e
    return tuple(c)

def horner(c, x:I)->I:
    v=I.point(0)
    for b in reversed(c):v=outward(v*x+b)
    return v

def f(n:int,k:int,x:Q)->I:
    return outward(factorial(k)*horner(polynomial(n,k),-logq(x))/x**(k+1))

@lru_cache(None)
def bernoulli(n:int)->Q:
    # Convention B_1=-1/2; all even values are independent of this convention.
    b=[Q(1)]
    from math import comb
    for m in range(1,n+1):
        b.append(-sum(Q(comb(m+1,j))*b[j] for j in range(m))/(m+1))
    return b[n]

def power_log_integral_upper(q:int,s:int,b:Q)->Q:
    """Upper bound for integral_b^infty x^(-s-1) log(x)^q dx, b>=1."""
    if b<1 or s<=0:raise ValueError('Invalid tail parameters')
    L=logq(b).hi
    return b**(-s)*sum(Q(factorial(q),factorial(q-j))*L**(q-j)/s**(j+1) for j in range(q+1))

def em_remainder(n:int,k:int,b:Q,p:int)->Q:
    s=k+2*p
    coeffs=polynomial(n,s)
    # Coefficients of B_{n,s} are nonnegative.
    assert all(c>=0 for c in coeffs)
    integ=factorial(s)*sum(c*power_log_integral_upper(q,s,b) for q,c in enumerate(coeffs))
    return abs(bernoulli(2*p))*integ/factorial(2*p)

def endpoint(n:int,k:int,a:Q,N:int=32,p:int=8)->tuple[I,Q]:
    """Enclose F_{n,k}^1(a), k>=1, using exact Euler--Maclaurin."""
    if n<0 or k<1 or a<=0 or N<1 or p<1:raise ValueError('Invalid inputs')
    b=a+N
    v=I.point(0)
    for m in range(N):v=outward(v+f(n,k,a+m))
    v=outward(v+f(n,k-1,b)+f(n,k,b)/2)
    for r in range(1,p+1):
        v=outward(v+Q(bernoulli(2*r),factorial(2*r))*f(n,k+2*r-1,b))
    R=em_remainder(n,k,b,p)
    return outward(v+I(-R,R)),R

def fracstr(x:Q)->str:return f'{x.numerator}/{x.denominator}'

def dec(x:Q,places:int=18,up:bool=False)->str:
    scale=10**places
    z=(x*scale).__ceil__() if up else (x*scale).__floor__()
    sign='-' if z<0 else '';z=abs(z)
    return f'{sign}{z//scale}.{z%scale:0{places}d}'

def pack(v:I)->dict:
    return {'lower_rational':fracstr(v.lo),'upper_rational':fracstr(v.hi),
            'lower_decimal':dec(v.lo,20),'upper_decimal':dec(v.hi,20,True),'sign':v.sign}

def main():
    out=Path(__file__).resolve().parents[2]/'results'/'lerch';out.mkdir(parents=True,exist_ok=True)
    groups={1:[('1',1),('1.5',-1)],2:[('1',1),('1.3',-1),('2',1)],
            3:[('0.8',1),('1.1',-1),('1.5',1),('2.1',-1)],
            4:[('0.8',1),('0.94',-1),('1.2',1),('1.7',-1),('2.2',1)]}
    rows=[]
    for n,items in groups.items():
        for atext,sign in items:
            a=Q(atext);v,R=endpoint(n,1,a);V=outward(v*a*a)
            assert v.sign==sign, (n,a,v)
            rows.append({'n':n,'k':1,'a':fracstr(a),'N':32,'p':8,
                         'F':pack(v),'normalized_V':pack(V),'remainder_bound':fracstr(R)})
            print(f'n={n}, a={atext}: V in [{dec(V.lo,12)}, {dec(V.hi,12,True)}], sign {sign:+d}')
    (out/'endpoint_sign_certificates.json').write_text(json.dumps({'arithmetic':'exact rational, outward rounding','certificates':rows},indent=2)+'\n')
    counts=[]
    for n in range(2,17):
        for k in range(1,n):
            r=n-k
            C=outward(Q((-1)**r*factorial(r)*factorial(k),2**(k+1)*factorial(n))*horner(polynomial(n,k),-logq(Q(2))))
            assert C.sign!=0,(n,k)
            count=k+(1 if r%2 else (2 if C.sign<0 else 0))
            if k==1:assert C.sign==1 and count==(1 if n%2 else 2)
            counts.append({'n':n,'k':k,'r':r,'C':pack(C),'eventual_small_rho_real_zero_count':count})
    (out/'weak_deformation_certificates.json').write_text(json.dumps({'certificates':counts},indent=2)+'\n')
    print(f'PASS: {len(rows)} endpoint signs; {len(counts)} weak-deformation coefficients.')

if __name__=='__main__':main()
