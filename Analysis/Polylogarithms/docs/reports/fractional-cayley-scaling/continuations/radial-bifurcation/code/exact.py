"""Outward dyadic intervals and second-order two-variable jets.

All decision arithmetic uses Python integers, not binary floating point.
Endpoints represent integer multiples of 2**(-BITS).  Elementary functions
are enclosed by positive Taylor series with written geometric tail bounds.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from typing import Union

BITS = 256
SCALE = 1 << BITS
Number = Union[int, str, Fraction]

def ceildiv(a: int, b: int) -> int:
    if b <= 0:
        raise ValueError('positive divisor required')
    return -((-a) // b)

@dataclass(frozen=True, slots=True)
class I:
    lo: int
    hi: int

    def __post_init__(self):
        if self.lo > self.hi:
            raise ValueError('reversed interval')

    @staticmethod
    def point(x: Number) -> I:
        f = Fraction(x)
        n, d = f.numerator * SCALE, f.denominator
        return I(n // d, ceildiv(n, d))

    @staticmethod
    def bounds(lo: Number, hi: Number) -> I:
        a, b = I.point(lo), I.point(hi)
        if Fraction(lo) > Fraction(hi):
            raise ValueError('reversed bounds')
        return I(a.lo, b.hi)

    def __add__(self, other):
        o = as_i(other)
        return I(self.lo + o.lo, self.hi + o.hi)
    __radd__ = __add__

    def __neg__(self): return I(-self.hi, -self.lo)
    def __sub__(self, other): return self + (-as_i(other))
    def __rsub__(self, other): return as_i(other) + (-self)

    def __mul__(self, other):
        o = as_i(other)
        p = (self.lo*o.lo, self.lo*o.hi, self.hi*o.lo, self.hi*o.hi)
        return I(min(p)//SCALE, ceildiv(max(p), SCALE))
    __rmul__ = __mul__

    def reciprocal(self):
        if self.lo <= 0 <= self.hi:
            raise ZeroDivisionError('interval contains zero')
        if self.hi < 0:
            return -((-self).reciprocal())
        return I((SCALE*SCALE)//self.hi,
                 ceildiv(SCALE*SCALE, self.lo))

    def __truediv__(self, other): return self * as_i(other).reciprocal()
    def __rtruediv__(self, other): return as_i(other) * self.reciprocal()

    def __pow__(self, n: int):
        if not isinstance(n, int): raise TypeError('integer exponent required')
        if n < 0: return self.reciprocal() ** (-n)
        if n == 0: return I.point(1)
        if n == 1: return self
        if n == 2:
            p = (self.lo*self.lo, self.hi*self.hi)
            return I(0 if self.lo <= 0 <= self.hi else min(p)//SCALE,
                     ceildiv(max(p), SCALE))
        r, v = I.point(1), self
        while n:
            if n & 1: r = r * v
            n >>= 1
            if n: v = v ** 2
        return r

    def dump(self): return {'lo':str(self.lo), 'hi':str(self.hi), 'bits':BITS}
    def fractions(self): return Fraction(self.lo,SCALE), Fraction(self.hi,SCALE)
    def diagnostic(self):
        # Display only. Never used for a sign decision.
        return (float(Fraction(self.lo,SCALE)),float(Fraction(self.hi,SCALE)))

def as_i(x): return x if isinstance(x,I) else I.point(x)

@lru_cache(None)
def log_integer(n: int) -> I:
    if not isinstance(n,int) or n < 1:
        raise ValueError('positive integer required')
    if n > 9:
        k=n.bit_length()-1; power=1<<k
        z=I.point(Fraction(n-power,n+power));z2=z*z
        term=z;total=I.point(0);N=128
        for j in range(N):
            total+=2*term/(2*j+1);term*=z2
        tail=2*term/((2*N+1)*(1-z2))
        return k*log_integer(2)+I(total.lo,total.hi+tail.hi)
    if n == 1: return I.point(0)
    z = I.point(Fraction(n-1,n+1))
    z2, term, total = z*z, z, I.point(0)
    N=512
    for j in range(N):
        total += 2*term/(2*j+1)
        term *= z2
    tail = 2*term/((2*N+1)*(1-z2))
    return I(total.lo, total.hi+tail.hi)

def exp_nonnegative(x: I) -> I:
    if x.lo < 0 or x.hi > 8*SCALE:
        raise ValueError('exp input must lie in [0,8]')
    y=x/16
    term=I.point(1); total=term
    N=64
    for k in range(1,N+1):
        term=term*y/k
        total+=term
    tail=term*y/(N+1)/(1-y/(N+2))
    total=I(total.lo,total.hi+tail.hi)
    for _ in range(4): total=total**2
    return total

def neg_power(n: int, exponent: I) -> I:
    return exp_nonnegative(exponent*log_integer(n)).reciprocal()

@dataclass(frozen=True, slots=True)
class J:
    """Value, a derivative, b derivative, aa, ab, bb derivatives."""
    v: I
    a: I
    b: I
    aa: I
    ab: I
    bb: I

    @staticmethod
    def const(v):
        z=I.point(0)
        return J(as_i(v),z,z,z,z,z)

    def __add__(self, other):
        o=as_j(other)
        return J(*(x+y for x,y in zip(self.tuple(),o.tuple())))
    __radd__=__add__
    def __neg__(self): return J(*(-x for x in self.tuple()))
    def __sub__(self,other): return self+(-as_j(other))
    def __rsub__(self,other): return as_j(other)+(-self)

    def __mul__(self,other):
        o=as_j(other); x=self
        return J(x.v*o.v, x.a*o.v+x.v*o.a, x.b*o.v+x.v*o.b,
                 x.aa*o.v+2*x.a*o.a+x.v*o.aa,
                 x.ab*o.v+x.a*o.b+x.b*o.a+x.v*o.ab,
                 x.bb*o.v+2*x.b*o.b+x.v*o.bb)
    __rmul__=__mul__

    def reciprocal(self):
        v=self.v.reciprocal(); v2=v*v; v3=v2*v
        return J(v,-v2*self.a,-v2*self.b,
                 2*v3*self.a**2-v2*self.aa,
                 2*v3*self.a*self.b-v2*self.ab,
                 2*v3*self.b**2-v2*self.bb)
    def __truediv__(self,other): return self*as_j(other).reciprocal()
    def __rtruediv__(self,other): return as_j(other)*self.reciprocal()
    def __pow__(self,n):
        if not isinstance(n,int) or n<0: raise ValueError('nonnegative integer required')
        r=J.const(1); v=self
        while n:
            if n&1:r=r*v
            n>>=1
            if n:v=v*v
        return r
    def tuple(self): return (self.v,self.a,self.b,self.aa,self.ab,self.bb)

def as_j(x): return x if isinstance(x,J) else J.const(x)

def coefficients(A: I, B: I, *, jets=True):
    """Enclose mu,K,Q,R. R is a value interval; other outputs are jets.

    When jets=False, return value intervals, using the same formulas.
    """
    p={}; H=I.point(0); Hb=I.point(0); Hbb=I.point(0)
    for n in range(2,10):
        j=n-1; L=log_integer(j); v=neg_power(j,B)
        H+=v; Hb-=L*v; Hbb+=L**2*v
        L=log_integer(n); v=neg_power(n,A)
        p[n]=J(v*H,-L*v*H,v*Hb,L**2*v*H,-L*v*Hb,v*Hbb) if jets else v*H
    mu=p[3]/(2*p[2])
    A0=4*p[3]*mu**2-4*p[4]*mu+p[5]
    A1=8*p[3]*mu-4*p[4]
    B0=8*p[4]*mu**3-12*p[5]*mu**2+6*p[6]*mu-p[7]
    B1=24*p[4]*mu**2-24*p[5]*mu+6*p[6]
    C0=16*p[5]*mu**4-32*p[6]*mu**3+24*p[7]*mu**2-8*p[8]*mu+p[9]
    K=-A0/(2*p[2]); Q=-(A1*K+B0)/(2*p[2])
    if jets:
        R=-(A1.v*Q.v+4*p[3].v*K.v**2+B1.v*K.v+C0.v)/(2*p[2].v)
    else:
        R=-(A1*Q+4*p[3]*K**2+B1*K+C0)/(2*p[2])
    return mu,K,Q,R

def threshold_derivatives(K:J,Q:J):
    ap=-K.b/K.a
    app=-(K.bb+2*K.ab*ap+K.aa*ap**2)/K.a
    qp=Q.b+Q.a*ap
    qpp=Q.bb+2*Q.ab*ap+Q.aa*ap**2+Q.a*app
    return ap,app,qp,qpp

def normalized_coefficients(A:I,B:I,*,jets=True):
    """Equivalent ratio formulas, avoiding differentiation of p_2^{-1}."""
    r={}; H=I.point(0); Hb=I.point(0); Hbb=I.point(0)
    L2=log_integer(2)
    for n in range(2,10):
        j=n-1; L=log_integer(j); v=neg_power(j,B)
        H+=v; Hb-=L*v; Hbb+=L**2*v
        L=log_integer(n)-L2
        if n==2:L=I.point(0)
        v=exp_nonnegative(A*L).reciprocal()
        r[n]=J(v*H,-L*v*H,v*Hb,L**2*v*H,-L*v*Hb,v*Hbb) if jets else v*H
    s=r[3];mu=s/2
    K=(2*s*r[4]-s**3-r[5])/2
    Q=-2*(s**2-r[4])*K-(r[4]*s**3-3*r[5]*s**2+3*r[6]*s-r[7])/2
    if jets:r={n:x.v for n,x in r.items()};s=s.v;k=K.v;q=Q.v
    else:k=K;q=Q
    R=-2*(s**2-r[4])*q-2*s*k**2-3*(r[4]*s**2-2*r[5]*s+r[6])*k-(r[5]*s**4-4*r[6]*s**3+6*r[7]*s**2-4*r[8]*s+r[9])/2
    return mu,K,Q,R

def threshold_value(A:I,B:I) -> I:
    """Fast value-only evaluation of K, equivalent to both jet formulas."""
    x=neg_power(2,B); y=neg_power(3,B); z=neg_power(4,B)
    U=1+x;V=U+y;W=V+z
    e25=exp_nonnegative(A*(log_integer(5)-log_integer(2))).reciprocal()
    e827=exp_nonnegative(3*A*(log_integer(3)-log_integer(2))).reciprocal()
    return U*V*neg_power(3,A)-W*e25/2-U**3*e827/2
