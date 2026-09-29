#!/usr/bin/env python3
"""Independent certificate using ONLY Python integer/rational arithmetic.

No floating-point, mpmath, NumPy, or SymPy is used in any mathematical bound.
Elementary functions are enclosed by explicit Taylor-series remainder bounds.
Run: python certify_integer.py --output integer_certificate.json
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from math import isqrt
from pathlib import Path
import json
import time

BITS = 100
S = 1 << BITS
R, K, N, J, C = 4, 128, 512, 28, 3_200_000

def ceil_div(a: int, b: int) -> int:
    assert b > 0
    return -((-a)//b)

@dataclass(frozen=True, slots=True)
class Interval:
    lo: int
    hi: int

    def __post_init__(self):
        assert self.lo <= self.hi

    @staticmethod
    def rational(n: int, d: int = 1) -> 'Interval':
        if d < 0:
            n, d = -n, -d
        if d == 0:
            raise ZeroDivisionError
        return Interval(n*S//d, ceil_div(n*S,d))

    @staticmethod
    def coerce(x) -> 'Interval':
        if isinstance(x, Interval):
            return x
        q = Fraction(x)
        return Interval.rational(q.numerator, q.denominator)

    def __add__(self, other):
        y = self.coerce(other)
        return Interval(self.lo+y.lo, self.hi+y.hi)
    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-self.coerce(other))

    def __rsub__(self, other):
        return self.coerce(other) + (-self)

    def __mul__(self, other):
        y = self.coerce(other)
        p = [self.lo*y.lo, self.lo*y.hi, self.hi*y.lo, self.hi*y.hi]
        return Interval(min(p)//S, ceil_div(max(p),S))
    __rmul__ = __mul__

    def __truediv__(self, other):
        y = self.coerce(other)
        if y.hi < 0:
            return (-self)/(-y)
        if y.lo <= 0:
            raise ZeroDivisionError('Interval denominator contains zero')
        lows, highs = [], []
        for a in (self.lo,self.hi):
            for b in (y.lo,y.hi):
                lows.append(a*S//b)
                highs.append(ceil_div(a*S,b))
        return Interval(min(lows),max(highs))

    def square(self):
        if self.lo <= 0 <= self.hi:
            lower = 0
        else:
            lower = min(self.lo*self.lo,self.hi*self.hi)//S
        upper = ceil_div(max(self.lo*self.lo,self.hi*self.hi),S)
        return Interval(lower,upper)

    def abs_upper(self):
        return max(abs(self.lo), abs(self.hi))

    def sqrt(self):
        assert self.lo >= 0
        lower = isqrt(self.lo*S)
        upper = isqrt(self.hi*S)
        if upper*upper < self.hi*S:
            upper += 1
        return Interval(lower, upper)

    def rationals(self):
        return Fraction(self.lo,S), Fraction(self.hi,S)

I = Interval.coerce

def pi_interval() -> Interval:
    def atan_reciprocal(d: int) -> Interval:
        total = I(0)
        terms = 40
        for k in range(terms):
            term = Interval.rational(1, (2*k+1)*d**(2*k+1))
            total += term if k % 2 == 0 else -term
        rem = Interval.rational(1,(2*terms+1)*d**(2*terms+1)).hi
        return total + Interval(-rem,rem)
    return 16*atan_reciprocal(5)-4*atan_reciprocal(239)

def sinc(t: Interval) -> Interval:
    """sin(t)/t for |t|<=4; alternating-series remainder after 20 terms."""
    assert t.abs_upper() <= 4*S
    t2 = t.square()
    term, total = I(1), I(1)
    terms = 20
    for k in range(1,terms):
        term = term*t2/((2*k)*(2*k+1))
        total += term if k % 2 == 0 else -term
    nxt = term*t2/((2*terms)*(2*terms+1))
    error = nxt.abs_upper()
    return total + Interval(-error,error)

def log_positive(y: Interval, terms: int = 36) -> Interval:
    """log(y), y>=1, via 2*atanh((y-1)/(y+1))."""
    assert y.lo >= S
    q = (y-1)/(y+1)
    q2 = q.square()
    assert q2.hi < S
    power, total = q, I(0)
    for k in range(terms):
        total += power/(2*k+1)
        power = power*q2
    # power encloses q**(2*terms+1); all exact terms are nonnegative.
    rem = 2*power/((2*terms+1)*(1-q2))
    return 2*total + Interval(0,max(0,rem.hi))

def exp_nonnegative(x: Interval) -> Interval:
    """exp(x), 0<=x<=4, with a geometric bound on the positive Taylor tail."""
    assert 0 <= x.lo <= x.hi <= 4*S
    term, total = I(1), I(1)
    terms = 60
    for k in range(1,terms+1):
        term = term*x/k
        total += term
    nxt = term*x/(terms+1)
    rem = nxt/(1-x/(terms+2))
    return total + Interval(0,max(0,rem.hi))

@lru_cache(maxsize=None)
def alpha(k: int) -> int:
    if k == 0: return 0
    if k == 1: return 1
    return -2*alpha(k//2) if k%2 == 0 else alpha(k//2)+alpha(k//2+1)

@lru_cache(maxsize=None)
def eta(k: int) -> Fraction:
    if k == 0: return Fraction(1)
    if k == 1: return Fraction(-1,3)
    return eta(k//2) if k%2 == 0 else -(eta(k//2)+eta(k//2+1))/2

def bounds_record(lo: Fraction, hi: Fraction) -> dict:
    # Diagnostic decimals are obtained by integer division, not floating point.
    d=10**21
    l=lo.numerator*d//lo.denominator
    h=ceil_div(hi.numerator*d,hi.denominator)
    def fixed(v):
        sign='-' if v<0 else ''
        v=abs(v)
        return f'{sign}{v//d}.{v%d:021d}'
    return {'lower_rational':str(lo),'upper_rational':str(hi),
            'lower_decimal_outward':fixed(l),'upper_decimal_outward':fixed(h)}

def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path('integer_certificate.json'))
    args=parser.parse_args()
    start=time.monotonic()
    pi=pi_interval()
    assert I(Fraction(31415,10000)).hi < pi.lo < pi.hi < I(Fraction(22,7)).lo
    log2=log_positive(I(2))
    kappa=log_positive(2*pi,terms=128)/log2
    M=N*2**R
    tail=Fraction(20,9*4**J)
    tail_factor=Interval(I(1-tail).lo,S)
    h, sin2 = [], []
    print(f'Pure-integer interval certificate: {M} samples, {BITS} bits.',flush=True)
    for q in range(M):
        x=Interval.rational(q,M)
        z=(1+x)/2
        t=pi*z
        product=I(1)
        for _ in range(J):
            product=product*sinc(t)
            t=t/2
        phi=product*tail_factor
        L=log_positive(1+x)
        exponent=L.square()/log2+(2*kappa-2)*L
        # The exact exponent is nonnegative; intersect with [0,infinity).
        exponent=Interval(max(0,exponent.lo),exponent.hi)
        h.append((phi/pi).square()*exp_nonnegative(exponent))
        angle=pi*x
        sin2.append((angle*sinc(angle)).square())
    g=[]
    for j in range(N):
        value=I(0)
        for ell in range(2**R):
            q=j+ell*N
            weight=I(1)
            for p in range(R):
                weight=weight*sin2[(2**p*q)%M]
            value+=weight*h[q]
        g.append(value)
    cosine=[1-2*sin2[j*2**R] for j in range(N)]
    est_a, est_mu=I(0),I(0)
    for j in range(N):
        ka,km=I(0),I(1)
        for k in range(1,K+1):
            co=cosine[(j*k)%N]
            ka+=2*alpha(k)*co
            km+=2*I(eta(k))*co
        est_a+=g[j]*ka
        est_mu+=g[j]*km
    est_a=est_a*((-2)**R)/N
    est_mu=est_mu/N
    ea=Fraction(16*C,3*K**6)+Fraction(64*C*K*(K+1),(N-K)**8)
    em=Fraction(2*C,7*K**7)+Fraction(4*C*(2*K+1),(N-K)**8)
    alo,ahi=est_a.rationals();mlo,mhi=est_mu.rationals()
    alo,ahi,mlo,mhi=alo-ea,ahi+ea,mlo-em,mhi+em
    rms=(Interval(I(mlo).lo,I(mhi).hi)/2).sqrt().rationals()
    bounds={'alpha_H':(alo,ahi),'mu_H':(mlo,mhi),'RMS_limit':rms}
    targets={'alpha_H':('-0.002907','-0.002898'),
             'mu_H':('0.021221672','0.021221677'),
             'RMS_limit':('0.10300890','0.10300894')}
    for key,(lo,hi) in bounds.items():
        a,b=map(Fraction,targets[key])
        assert a<lo<=hi<b,(key,lo,hi)
        print(key,bounds_record(lo,hi),flush=True)
    assert ahi<0<mlo
    # The relative error shrinks by 2**(-6) at each subsequent shell.
    assert Fraction(32*C,63*2**42) < Fraction(2898,10**6*6*2**10)
    result={'status':'PASS','arithmetic':'Exact Python integers and Fractions only',
            'proof_assistant_checked':False,'alternation_certified_from_shell':10,
            'parameters':{'r':R,'K':K,'N':N,'J':J,'C':C,'bits':BITS},
            'elementary_series_terms':{'atan':40,'sinc':20,'log_samples':36,
                'log_2pi':128,'exp':60},
            'analytic_errors':{'alpha_H':str(ea),'mu_H':str(em)},
            'enclosures':{key:bounds_record(*val) for key,val in bounds.items()},
            'certified_coarse_open_intervals':targets,
            'elapsed_seconds_diagnostic_only':round(time.monotonic()-start,2)}
    args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(f'PASS: wrote {args.output}',flush=True)

if __name__=='__main__':
    main()
