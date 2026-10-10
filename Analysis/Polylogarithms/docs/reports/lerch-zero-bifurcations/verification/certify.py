#!/usr/bin/env python3
"""Exact fixed-point interval certificates for Stieltjes derivative signs.

Only Python's standard library is used. All rounding is outward. No floating
point values are used in any mathematical certification decision.
See the article's Euler--Maclaurin remainder theorem for the error formula.
"""
from __future__ import annotations

if not __debug__:
    raise RuntimeError("Certification requires assertions; do not use Python -O.")
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from math import comb, factorial
from pathlib import Path
import argparse
import json

DIGITS = 55
SCALE = 10**DIGITS
LOG_TERMS = 72


def ceildiv(a: int, b: int) -> int:
    return -((-a)//b)

@dataclass(frozen=True)
class I:
    lo: int
    hi: int
    def __post_init__(self):
        if self.lo > self.hi: raise ValueError('Reversed interval')
    @staticmethod
    def exact(x=0) -> I:
        q=Fraction(x)
        return I(q.numerator*SCALE//q.denominator,
                 ceildiv(q.numerator*SCALE,q.denominator))
    @staticmethod
    def bounds(a,b) -> I:
        return I(I.exact(a).lo,I.exact(b).hi)
    def __add__(self,other) -> I:
        other=as_i(other)
        return I(self.lo+other.lo,self.hi+other.hi)
    __radd__=__add__
    def __neg__(self) -> I:return I(-self.hi,-self.lo)
    def __sub__(self,other) -> I:return self+-as_i(other)
    def __rsub__(self,other) -> I:return as_i(other)+-self
    def __mul__(self,other) -> I:
        other=as_i(other)
        products=[self.lo*other.lo,self.lo*other.hi,self.hi*other.lo,self.hi*other.hi]
        return I(min(products)//SCALE,ceildiv(max(products),SCALE))
    __rmul__=__mul__
    def reciprocal(self) -> I:
        if self.lo<=0<=self.hi:raise ZeroDivisionError('Interval contains zero')
        return I((SCALE*SCALE)//self.hi,ceildiv(SCALE*SCALE,self.lo))
    def __truediv__(self,other) -> I:return self*as_i(other).reciprocal()
    def __rtruediv__(self,other) -> I:return as_i(other)*self.reciprocal()
    def __pow__(self,n:int) -> I:
        if not isinstance(n,int):raise TypeError('Integer powers only')
        if n<0:return self.reciprocal()**(-n)
        ans=I.exact(1);base=self
        while n:
            if n&1:ans=ans*base
            base=base*base;n//=2
        return ans
    def sign(self) -> int:
        return 1 if self.lo>0 else -1 if self.hi<0 else 0
    def contains(self,other) -> bool:
        other=as_i(other);return self.lo<=other.lo and self.hi>=other.hi
    def json(self) -> dict:
        return {'lo_numerator':str(self.lo),'hi_numerator':str(self.hi),
                'denominator':str(SCALE),'decimal_enclosure':decimal_bounds(self)}

def as_i(x) -> I:return x if isinstance(x,I) else I.exact(x)

def decimal_bounds(x:I, places:int=16) -> list[str]:
    t=10**places
    lo=x.lo*t//SCALE;hi=ceildiv(x.hi*t,SCALE)
    def fmt(v):
        sg='-' if v<0 else '';v=abs(v)
        return f'{sg}{v//t}.{v%t:0{places}d}'
    return [fmt(lo),fmt(hi)]

@lru_cache(maxsize=None)
def _log_core(q:Fraction) -> tuple[Fraction,Fraction]:
    """Atanh series, for 1 <= q <= 2; returns exact rational bounds."""
    if not 1<=q<=2:raise ValueError('log core out of range')
    u=(q-1)/(q+1);u2=u*u;power=u;sm=Fraction(0)
    for j in range(LOG_TERMS):
        sm+=power/(2*j+1);power*=u2
    lo=2*sm
    return lo,lo+2*power/((2*LOG_TERMS+1)*(1-u2))

@lru_cache(maxsize=None)
def log_rational(q:Fraction) -> I:
    if q<=0:raise ValueError('Positive logarithm argument required')
    e=0
    while q<1:q*=2;e-=1
    while q>=2:q/=2;e+=1
    lo,hi=_log_core(q);L=I.bounds(lo,hi)
    lo2,hi2=_log_core(Fraction(2))
    return L+e*I.bounds(lo2,hi2)

def log_interval(x:I) -> I:
    return I(log_rational(Fraction(x.lo,SCALE)).lo,
             log_rational(Fraction(x.hi,SCALE)).hi)

@lru_cache(maxsize=None)
def bernoulli(n:int) -> Fraction:
    if n==0:return Fraction(1)
    return -sum(Fraction(comb(n+1,j))*bernoulli(j) for j in range(n))/Fraction(n+1)

@lru_cache(maxsize=None)
def rising_coeff(length:int,n:int) -> tuple[int,...]:
    p=[1]+[0]*n
    for j in range(1,length+1):
        p=[j*p[i]+(p[i-1] if i else 0) for i in range(n+1)]
    return tuple(p)

def mul(p,q,n):
    out=[I.exact(0) for _ in range(n+1)]
    for i,x in enumerate(p[:n+1]):
        for j,y in enumerate(q[:n+1-i]):out[i+j]=out[i+j]+x*y
    return out

def exp_poly(L:I,n:int):
    p=[I.exact(1)]
    for j in range(1,n+1):p.append(p[-1]*(-L)/j)
    return p

def em_remainder(n:int,k:int,A:I,M:int) -> I:
    """Upper enclosure of |R_{n,k}|, using the even Bernoulli bound."""
    if A.lo<SCALE:raise ValueError('Require A>=1 for this remainder bound')
    h=k+2*M;L=log_interval(A);Lupper=I(L.hi,L.hi)
    co=rising_coeff(h,n);ans=I.exact(0)
    for j in range(n+1):
        d=n-j;integ=I.exact(0)
        for v in range(d+1):
            integ+=Fraction(factorial(d),factorial(d-v)*h**(v+1))*Lupper**(d-v)
        integ*=I(A.lo,A.lo)**(-h)
        ans+=Fraction(co[j],factorial(d))*integ
    ans*=Fraction(factorial(n),factorial(2*M))*abs(bernoulli(2*M))
    return ans

def certify_F(n:int,k:int,a:I|str|Fraction,N:int=32,M:int=16) -> tuple[I,I]:
    if n<0 or k<1 or N<1 or M<1:raise ValueError('Invalid index/cutoff')
    a=as_i(a)
    if a.lo<=0:raise ValueError('a must be positive')
    p=rising_coeff(k,n);z=[I.exact(0) for _ in range(n+1)]
    for m in range(N):
        x=a+m;ep=exp_poly(log_interval(x),n);fac=x**(-k-1)
        for j in range(n+1):z[j]+=fac*ep[j]
    ans=mul(p,z,n)
    A=a+N;ep=exp_poly(log_interval(A),n)
    terms=[(rising_coeff(k-1,n),A**(-k)),
           (p,A**(-k-1)/2)]
    for r in range(1,M+1):
        terms.append((rising_coeff(k+2*r-1,n),
                      Fraction(bernoulli(2*r),factorial(2*r))*A**(-k-2*r)))
    for coeff,fac in terms:
        tail=mul(coeff,ep,n)
        for j in range(n+1):ans[j]+=fac*tail[j]
    rem=em_remainder(n,k,A,M)
    val=factorial(n)*ans[n]
    return I(val.lo-rem.hi,val.hi+rem.hi),rem


def main(out:Path) -> None:
    out.mkdir(parents=True,exist_ok=True)
    records=[]
    def record(tag,n,k,a,expected):
        A=I.bounds(*a) if isinstance(a,tuple) else I.exact(a)
        val,rem=certify_F(n,k,A)
        assert val.sign()==expected,(tag,decimal_bounds(val))
        records.append({'id':tag,'n':n,'k':k,'a':A.json(),
                        'value':val.json(),'absolute_remainder_bound':rem.json(),
                        'expected_sign':expected})
        print(tag,decimal_bounds(val),flush=True)
    # Fixed anchors give uniform-in-rho low-index theorems.
    record('n2_anchor',2,1,'1.3',-1)
    record('n2_at_one',2,1,'1',1)
    record('n2_at_two',2,1,'2',1)
    record('n3_negative_anchor',3,1,'1',-1)
    record('n3_positive_anchor',3,1,'1.5',1)
    # Five brackets at derivative order 3; predecessor enclosures on whole brackets.
    c3=[('0.94095','0.94096'),('1.12928','1.12930'),
        ('1.63577','1.63579'),('6.1361','6.1362'),('319.61','319.63')]
    prev_signs=[1,1,-1,1,-1]
    for j,b in enumerate(c3,1):
        record(f'n5_k3_root{j}_left',5,3,b[0],(-1)**(j-1))
        record(f'n5_k3_root{j}_right',5,3,b[1],(-1)**j)
        record(f'n5_k2_on_k3_root{j}',5,2,b,prev_signs[j-1])
    # Three brackets at order 2, with order-1 values on whole brackets.
    c2=[('1.37132','1.37134'),('1.91135','1.91138'),('148.91','148.92')]
    for j,b in enumerate(c2,1):
        record(f'n5_k2_root{j}_left',5,2,b[0],(-1)**(j-1))
        record(f'n5_k2_root{j}_right',5,2,b[1],(-1)**j)
        record(f'n5_k1_on_k2_root{j}',5,1,b,(-1)**j)
    # First derivative zeros, for usable isolating intervals.
    c1=[('1.13788','1.13790'),('1.63892','1.63895'),('2.12489','2.12492')]
    for j,b in enumerate(c1,1):
        record(f'n5_k1_root{j}_left',5,1,b[0],(-1)**(j-1))
        record(f'n5_k1_root{j}_right',5,1,b[1],(-1)**j)
    payload={'status':'all exact sign assertions passed','arithmetic':'integer fixed-point, outward rounding',
             'digits':DIGITS,'log_terms':LOG_TERMS,'N':32,'M':16,
             'assertion_count':len(records),'records':records}
    (out/'sign_certificates.json').write_text(json.dumps(payload,indent=2)+'\n')
    (out/'certificate_summary.md').write_text('# Exact sign certificate summary\n\n'
        +f'{len(records)} exact sign assertions passed. All intervals use rational endpoints.\n\n'
        +'| ID | enclosure | sign |\n|---|---|---|\n'
        +'\n'.join(f"| `{r['id']}` | {r['value']['decimal_enclosure']} | {r['expected_sign']:+d} |" for r in records)+'\n')

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out',type=Path,default=Path(__file__).resolve().parents[1]/'certificates')
    args=parser.parse_args();main(args.out)
