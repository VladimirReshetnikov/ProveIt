#!/usr/bin/env python3
"""Exact sign certificates for Stieltjes parameter derivatives.

Only Python's standard library is used. All endpoints are integers scaled by
10**90. Every arithmetic operation rounds outward. Logarithms are enclosed by
an atanh series with an explicit positive tail. Euler--Maclaurin's periodic
Bernoulli remainder is bounded analytically; no floating-point special function
is used by this verifier. See the accompanying article, Section 8.
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass
from fractions import Fraction as F
from functools import lru_cache
import json
from math import comb, factorial
from pathlib import Path
import time

DIGITS = 90
SCALE = 10**DIGITS

def ceildiv(a: int, b: int) -> int:
    if b <= 0:
        raise ValueError('positive denominator required')
    return -((-a)//b)

@dataclass(frozen=True)
class I:
    lo: int
    hi: int
    def __post_init__(self) -> None:
        if self.lo > self.hi:
            raise ValueError('reversed interval')
    @staticmethod
    def q(value: F | int | str) -> 'I':
        v = F(value)
        return I(v.numerator*SCALE//v.denominator,
                 ceildiv(v.numerator*SCALE, v.denominator))
    def __add__(self, other: 'I | int') -> 'I':
        o = other if isinstance(other,I) else I.q(other)
        return I(self.lo+o.lo, self.hi+o.hi)
    __radd__ = __add__
    def __neg__(self) -> 'I':
        return I(-self.hi,-self.lo)
    def __sub__(self, other: 'I | int') -> 'I':
        return self + (-(other if isinstance(other,I) else I.q(other)))
    def __rsub__(self, other: 'I | int') -> 'I':
        return (-self) + other
    def __mul__(self, other: 'I | int') -> 'I':
        o = other if isinstance(other,I) else I.q(other)
        p = (self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi)
        return I(min(p)//SCALE,ceildiv(max(p),SCALE))
    __rmul__ = __mul__
    def __truediv__(self, other: 'I | int') -> 'I':
        o = other if isinstance(other,I) else I.q(other)
        if o.lo <= 0 <= o.hi:
            raise ZeroDivisionError('interval contains zero')
        vals = [F(a*SCALE,b) for a in (self.lo,self.hi)
                for b in (o.lo,o.hi)]
        low,high=min(vals),max(vals)
        return I(low.numerator//low.denominator,
                 ceildiv(high.numerator,high.denominator))
    def __pow__(self, n: int) -> 'I':
        if not isinstance(n,int):
            raise TypeError('integer exponent required')
        if n<0:
            return I.q(1)/(self**(-n))
        ans=I.q(1); base=self
        while n:
            if n&1: ans=ans*base
            base=base*base; n//=2
        return ans
    def sign(self) -> int:
        if self.lo>0: return 1
        if self.hi<0: return -1
        return 0
    def decimal(self, places: int=35) -> list[str]:
        if not 0<=places<=DIGITS: raise ValueError('invalid places')
        div=10**(DIGITS-places)
        def fmt(x:int)->str:
            s='-' if x<0 else '';x=abs(x)
            return f'{s}{x//10**places}.{x%10**places:0{places}d}'
        return [fmt(self.lo//div),fmt(ceildiv(self.hi,div))]

@lru_cache(maxsize=4096)
def _atanh_log(y: F, terms: int=120) -> I:
    """Enclose log(y) for 1 <= y <= 2, by positive rational summands."""
    if not F(1)<=y<=F(2): raise ValueError('range reduction failed')
    u=(y-1)/(y+1)
    if u==0: return I.q(0)
    p,q=u.numerator,u.denominator
    pn,qn=p,q; lower=0
    for j in range(terms):
        lower += (2*SCALE*pn)//((2*j+1)*qn)
        pn *= p*p; qn *= q*q
    # pn/qn = u**(2*terms+1); integral-series remainder bound.
    tail=F(2*pn, (2*terms+1)*qn)/(1-u*u)
    upper=lower+terms+ceildiv(SCALE*tail.numerator,tail.denominator)
    return I(lower,upper)

@lru_cache(maxsize=4096)
def logq(x: F) -> I:
    if x<=0: raise ValueError('logarithm requires a positive rational')
    e=x.numerator.bit_length()-x.denominator.bit_length()
    y=x/(F(2)**e)
    if y<1: e-=1; y*=2
    if y>=2: e+=1; y/=2
    return _atanh_log(y)+e*_atanh_log(F(2))

@lru_cache(maxsize=None)
def bernoulli(n:int)->F:
    if n<0: raise ValueError('negative index')
    if n==0:return F(1)
    return -sum(F(comb(n+1,j))*bernoulli(j) for j in range(n))/F(n+1)

@lru_cache(maxsize=2048)
def elementary(ell:int,n:int)->tuple[F,...]:
    if ell<0 or n<0:raise ValueError('negative index')
    e=[F(1)]+[F(0)]*n
    for j in range(1,ell+1):
        for i in range(min(j,n),0,-1):e[i]+=e[i-1]/j
    return tuple(e)

def poly_q(n:int,ell:int,logx:I)->I:
    e=elementary(ell,n);v=I.q(0)
    # Q_{n,ell}(x) = sum_{j=0}^n n! e_{n-j}(ell) (-x)^j/j!.
    for j in range(n,-1,-1):
        v=v*(-logx)+I.q(F(factorial(n),factorial(j))*e[n-j])
    return v

def enclosure(n:int,k:int,a:F,M:int=40,R:int=16)->I:
    """Enclose a**(k+1) (-1)**(n+k) gamma_n^(k)(a) / k!."""
    if n<0 or k<1 or a<=0 or M<1 or R<1:
        raise ValueError('n>=0, k>=1, a>0, M>=1, R>=1 required')
    A=a+M;p=k+1;L=k+2*R
    la=logq(A); ratio=I.q(a/A)**p
    v=I.q(0)
    for m in range(M):
        x=a+m
        v += (I.q(a/x)**p)*poly_q(n,k,logq(x))
    v += ratio*I.q(A/k)*poly_q(n,k-1,la)
    v += ratio*I.q(F(1,2))*poly_q(n,k,la)
    prod=I.q(1)
    for j in range(1,2*R):
        prod *= I.q(F(k+j)/A)
        if j%2==1:
            r=(j+1)//2
            v += ratio*I.q(bernoulli(2*r)/factorial(2*r))*prod*poly_q(n,k+2*r-1,la)
    # Absolute remainder bound, valid since A>1. All factors below are positive.
    e=elementary(L,n);boundpoly=I.q(0)
    for i in range(min(n,L)+1):
        for j in range(n-i+1):
            d=n-i-j
            boundpoly += I.q(F(factorial(n),factorial(d))*e[i]/(L**j))*(la**d)
    b=ratio*I.q(abs(bernoulli(2*R))/factorial(2*R))*prod*boundpoly
    return I(v.lo-b.hi,v.hi+b.hi)

def self_test()->None:
    assert bernoulli(2)==F(1,6) and bernoulli(4)==-F(1,30)
    assert bernoulli(12)==-F(691,2730)
    assert logq(F(1))==I.q(0)
    assert (logq(F(2))-I.q(F('0.693147180559945309417232121458176568075500134360255254120680009493393621969694715605863326996418687'))).sign()==0
    assert I.q(F(1,3)).lo*SCALE <= I.q(F(1,3)).hi*SCALE
    assert (I.q(-3)*I.q(-2))==I.q(6)
    assert (I.q(-3)/I.q(-2))==I.q(F(3,2))
    assert elementary(2,2)==(F(1),F(3,2),F(1,2))

def main()->None:
    ap=argparse.ArgumentParser(description=__doc__)
    root=Path(__file__).resolve().parents[1]
    ap.add_argument('--input',type=Path,default=root/'data/certificates.json')
    ap.add_argument('--output',type=Path,default=root/'data/exact_results.json')
    args=ap.parse_args();self_test();doc=json.loads(args.input.read_text())
    results=[];start=time.monotonic()
    for item in doc['evaluations']:
        v=enclosure(item['n'],item['k'],F(item['a']),item.get('M',40),item.get('R',16))
        if v.sign()!=item['expected_sign']:
            raise AssertionError(f'Certificate failed: {item}; interval {v.decimal()}')
        results.append(dict(item,enclosure=v.decimal(),verified_sign=v.sign()))
        print(f"PASS n={item['n']} k={item['k']} a={item['a']} sign={v.sign()}",flush=True)
    out={'status':'PASS','arithmetic':'exact integer outward intervals',
         'decimal_scale_digits':DIGITS,'evaluations':len(results),
         'elapsed_seconds':round(time.monotonic()-start,3),'results':results}
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(f"Verified {len(results)} sign enclosures; wrote {args.output}")

if __name__=='__main__':main()
