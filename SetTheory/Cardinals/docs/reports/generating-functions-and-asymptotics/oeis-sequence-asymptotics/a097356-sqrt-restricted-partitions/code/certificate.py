"""Exact rational certificates for the signs in the article (standard library).

The analytic tail bound used here is proved in the article. This checks finite
rational inequalities; it is not a Lean/Coq formalization of the analytic proof.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from math import comb, factorial
import json

@dataclass(frozen=True)
class Interval:
    lo: Q
    hi: Q

    def __post_init__(self):
        if self.lo > self.hi:
            raise ValueError('reversed interval')

    @staticmethod
    def make(x):
        return x if isinstance(x,Interval) else Interval(Q(x),Q(x))

    def __add__(self,other):
        t=self.make(other)
        return Interval(self.lo+t.lo,self.hi+t.hi)
    __radd__=__add__

    def __neg__(self):
        return Interval(-self.hi,-self.lo)

    def __sub__(self,other):
        return self+-self.make(other)

    def __rsub__(self,other):
        return self.make(other)+-self

    def __mul__(self,other):
        t=self.make(other)
        a=[self.lo*t.lo,self.lo*t.hi,self.hi*t.lo,self.hi*t.hi]
        return Interval(min(a),max(a))
    __rmul__=__mul__

    def reciprocal(self):
        if self.lo <= 0 <= self.hi:
            raise ZeroDivisionError('interval contains zero')
        return Interval(1/self.hi,1/self.lo)

    def __truediv__(self,other):
        return self*self.make(other).reciprocal()

    def __rtruediv__(self,other):
        return self.make(other)*self.reciprocal()

    def __pow__(self,n):
        if not isinstance(n,int):
            raise TypeError('integer exponent required')
        if n<0:
            return self.reciprocal()**(-n)
        if n==0:
            return self.make(1)
        # Multiplication enclosure suffices (all powers used here are positive-base).
        x=self; y=self.make(1)
        while n:
            if n&1: y=y*x
            x=x*x; n//=2
        return y

    def widen(self,e):
        return Interval(self.lo-e,self.hi+e)

    def within(self,lo,hi):
        return Q(lo) <= self.lo and self.hi <= Q(hi)

    def decimal_enclosure(self,digits=12):
        scale=10**digits
        lower=(self.lo.numerator*scale)//self.lo.denominator
        upper=-((-self.hi.numerator*scale)//self.hi.denominator)
        def fmt(n):
            sign='-' if n<0 else ''
            n=abs(n)
            return f'{sign}{n//scale}.{n%scale:0{digits}d}'
        return [fmt(lower),fmt(upper)]


def bernoulli(n):
    B=[Q(1)]
    for j in range(1,n+1):
        B.append(-sum(Q(comb(j+1,k))*B[k] for k in range(j))/Q(j+1))
    return B

R=16
B=bernoulli(2*R)
# All tails of the power series and their <=4 derivatives are bounded by eps
# on 0.8 <= u <= 1. See the article's rational-certificate appendix.
eps=Q(8*(2*R+2)**4,6**(2*R+2))


def log_interval(u):
    w=(1-u)/(1+u)
    s=Interval.make(0)
    T=24
    for j in range(T):
        s+=w**(2*j+1)/Q(2*j+1)
    err=2*w.hi**(2*T+1)/(Q(2*T+1)*(1-w.hi*w.hi))
    return (-2*s).widen(err)


def F(u,d=0):
    if d==0:
        v=1-log_interval(u)+u/4
    else:
        v=Q((-1)**d*factorial(d-1))*u**(-d)
        if d==1:
            v+=Q(1,4)
    for r in range(1,R+1):
        p=2*r
        if p<d:
            continue
        c=-B[p]/Q(p*factorial(p)*(p+1))
        v+=c*Q(factorial(p),factorial(p-d))*u**(p-d)
    return v.widen(eps)


def ell(u,d):
    v=u/4 if d==0 else Interval.make(Q(1,4) if d==1 else 0)
    for r in range(1,R+1):
        p=2*r
        if p>=d:
            v-=B[p]/Q(2*p*factorial(p))*Q(factorial(p),factorial(p-d))*u**(p-d)
    return v.widen(eps)


def E1(u):
    v=Interval.make(Q(-1,12))
    for r in range(1,R+1):
        v-=B[2*r]/Q(12*factorial(2*r))*u**(2*r)
    return v.widen(eps)


def certify():
    lo=Q(814651136747,10**12)
    hi=Q(814651136748,10**12)
    jl=-F(Interval.make(lo),1)
    jh=-F(Interval.make(hi),1)
    assert jl.lo>1 and jh.hi<1, 'failed saddle bracket'
    u=Interval(lo,hi)
    V,F3,F4=F(u,2),F(u,3),F(u,4)
    l1,l2=ell(u,1),ell(u,2)
    H=u+F(u)
    def d1(s):
        w=l1+s
        return E1(u)-(l2+w*w)/(2*V)+F3*w/(2*V**2)+F4/(8*V**2)-5*F3**2/(24*V**3)
    a=d1(0)
    b=2-2*l1/V+F3/V**2
    c=u-2/V
    kappa=d1(2)+2+H/2
    checks={
        'u':u,'H':H,'V':V,'P1_constant':a,
        'P1_linear':b,'P1_quadratic':c,'endpoint_kappa':kappa,
        'J(lower)-1':jl-1,'J(upper)-1':jh-1,
        'kappa_3':a+b+c+3*(H-2*u)/2,
        'kappa_4':a+b+c+4*(H-2*u)/2,
    }
    assert a.within('-.374525','-.374524')
    assert b.within('.018208','.018209')
    assert c.within('-.537095','-.537094')
    assert kappa.within('-.601001','-.601000')
    # For theta in [0,1]: P1(theta) <= a_hi+max(b_hi,0)<0,
    # because c_hi<0. This proves an eventual upper envelope.
    assert a.hi+max(b.hi,0)<0 and c.hi<0
    assert kappa.hi<0
    assert checks['kappa_3'].within('-.016181','-.016180')
    assert checks['kappa_4'].within('.276229','.276230')
    return {key:val.decimal_enclosure(14) for key,val in checks.items()}

if __name__=='__main__':
    print(json.dumps(certify(),indent=2))
