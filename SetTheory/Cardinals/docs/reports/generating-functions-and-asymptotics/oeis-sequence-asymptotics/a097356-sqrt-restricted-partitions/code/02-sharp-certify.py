#!/usr/bin/env python3
"""Exact rational interval certificate for the signs used in the article.

All interval endpoints are fractions. Every arithmetic operation rounds
outward to a fixed rational grid. No floating-point evaluation is trusted.
The only dependency, SymPy, supplies exact Bernoulli numbers.
"""
from __future__ import annotations
from fractions import Fraction as Q
from dataclasses import dataclass
import math
from sympy import bernoulli

SCALE=10**45


def down(x: Q) -> Q:
    return Q((x*SCALE).numerator//(x*SCALE).denominator,SCALE)


def up(x: Q) -> Q:
    z=x*SCALE
    return Q(-((-z.numerator)//z.denominator),SCALE)


@dataclass(frozen=True)
class I:
    lo: Q
    hi: Q
    def __init__(self,lo,hi=None):
        lo=Q(lo); hi=lo if hi is None else Q(hi)
        if lo>hi: raise ValueError('reversed interval')
        object.__setattr__(self,'lo',down(lo))
        object.__setattr__(self,'hi',up(hi))
    def __add__(self,b):
        b=as_i(b); return I(self.lo+b.lo,self.hi+b.hi)
    __radd__=__add__
    def __neg__(self): return I(-self.hi,-self.lo)
    def __sub__(self,b): return self+-as_i(b)
    def __rsub__(self,b): return as_i(b)+-self
    def __mul__(self,b):
        b=as_i(b); p=[self.lo*b.lo,self.lo*b.hi,self.hi*b.lo,self.hi*b.hi]
        return I(min(p),max(p))
    __rmul__=__mul__
    def __truediv__(self,b):
        b=as_i(b)
        if b.lo<=0<=b.hi: raise ZeroDivisionError('interval crosses zero')
        return self*I(1/b.hi,1/b.lo)
    def __rtruediv__(self,b):return as_i(b)/self
    def __pow__(self,k:int):
        if k<0:return 1/(self**(-k))
        r=I(1)
        while k:
            if k&1:r=r*self
            self=self*self;k//=2
        return r


def as_i(x): return x if isinstance(x,I) else I(x)


def fd(v:I,d:int,N:int=20)->I:
    """Enclose F^(d)(v), 1<=d<=4, for 0<v<1."""
    assert 1<=d<=4 and 0<v.lo<=v.hi<1
    ans=(-1)**d*math.factorial(d-1)/v**d
    if d==1:ans+=Q(1,4)
    for k in range(1,N+1):
        if 2*k<d:continue
        bk=Q(int(bernoulli(2*k).p),int(bernoulli(2*k).q))
        fall=math.factorial(2*k)//math.factorial(2*k-d)
        a=-bk*Q(fall,2*k*math.factorial(2*k)*(2*k+1))
        ans+=a*v**(2*k-d)
    # |B_2k|/(2k)! < 4/36^k, since pi>3 and zeta(2k)<2.
    # For k>=21, consecutive 4(2k)^4/36^k terms have ratio<1/16.
    tail=Q(4*(2*N+2)**4,36**(N+1))*Q(16,15)
    return ans+I(-tail,tail)


def exp_pos(v:I,N:int=40)->I:
    assert 0<v.lo<=v.hi<1
    ans=I(0)
    for k in range(N+1):ans+=v**k/math.factorial(k)
    tail=Q(1,math.factorial(N+1))*Q(N+2,N+1)
    return ans+I(0,tail)


def log_pos(x:I,N:int=45)->I:
    assert x.lo>1
    t=(x-1)/(x+1)
    assert 0<t.lo<=t.hi<Q(1,3)
    ans=I(0)
    for k in range(N+1):ans+=2*t**(2*k+1)/(2*k+1)
    tail=2*t.hi**(2*N+3)/((2*N+3)*(1-t.hi*t.hi))
    return ans+I(0,tail)


def show(name:str,x:I,places:int=12):
    scale=10**places
    l=(x.lo*scale).numerator//(x.lo*scale).denominator
    h=-(((-x.hi*scale).numerator)//(-x.hi*scale).denominator)
    def fmt(n):
        return ('-' if n<0 else '')+str(abs(n)//scale)+'.'+str(abs(n)%scale).zfill(places)
    print(f'{name}: [{fmt(l)}, {fmt(h)}]')


def run():
    vlo=Q('0.814651136747611');vhi=Q('0.814651136747612')
    assert (-fd(I(vlo),1)-1).lo>0
    assert (-fd(I(vhi),1)-1).hi<0
    v=I(vlo,vhi)
    B,F3,F4=fd(v,2),fd(v,3),fd(v,4)
    assert B.lo>0
    E=exp_pos(v)
    h1=1/(2*v)-1/(2*(E-1))
    h2=-1/(2*v*v)+E/(2*(E-1)**2)
    u1=-v*(E+1)/(24*(E-1))
    d0=u1-(h2+h1*h1)/(2*B)+h1*F3/(2*B**2)+F4/(8*B**2)-5*F3**2/(24*B**3)
    eta=-h1/B+F3/(2*B**2)
    linear=2+2*eta;quadratic=v-2/B
    beta=log_pos(E/(E-1))
    tail=d0+linear+quadratic+beta/2
    boxes={'d0':(d0,'-.374525','-.374524'),
           'linear':(linear,'.018208','.018209'),
           'quadratic':(quadratic,'-.537095','-.537094'),
           'beta':(beta,'.584819','.584821'),
           'tail':(tail,'-.601002','-.600999')}
    for name,(x,l,h) in boxes.items():
        assert Q(l)<x.lo<=x.hi<Q(h),name
    assert d0.hi+linear.hi<0 and quadratic.hi<0
    assert tail.hi<0
    assert tail.hi+beta.hi<0
    assert tail.lo+Q(3,2)*beta.lo>0
    for name,x in [('v',v),('B',B),('F3',F3),('F4',F4)]+[(a,b[0]) for a,b in boxes.items()]:
        show(name,x)
    print('PASS: unique saddle bracket; Q1(delta)<0 on [0,1]; pre-square correction<0; boundary signs at r=3 and r=4.')
    print('Arithmetic: exact rational intervals; outward grid denominator 10^45.')


if __name__=='__main__':run()
