#!/usr/bin/env python3
"""Narrow exact enclosures for the axis maximizer and universal constant.

Dependencies are analytic, and are stated rather than tested:
  (1) the manuscript proves C has a unique strictly unimodal maximum;
  (2) the scalar-domination theorem gives the axis budget M=5/4;
  (3) log(Gamma(b) C(b)) is convex and (log Gamma)''<5/3 on [1,2].

All finite computations below use integer or Fraction arithmetic. No
floating-point arithmetic contributes to a mathematical comparison.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from math import comb
from pathlib import Path
import json

P = 2**384
LOG_TERMS = 128
EXP_TERMS = 200
EULER_TERMS = 224


def ceildiv(a,b):
    return -((-a)//b)


@dataclass(frozen=True)
class Interval:
    lo: int
    hi: int

    @classmethod
    def rational(cls,q):
        q=Q(q)
        return cls(q.numerator*P//q.denominator,
                   ceildiv(q.numerator*P,q.denominator))

    def add(self,other):
        return Interval(self.lo+other.lo,self.hi+other.hi)

    def mul(self,other):
        assert self.lo>=0 and other.lo>=0
        return Interval(self.lo*other.lo//P,
                        ceildiv(self.hi*other.hi,P))

    def scale(self,q):
        q=Q(q)
        assert q>=0
        return Interval(self.lo*q.numerator//q.denominator,
                        ceildiv(self.hi*q.numerator,q.denominator))

    def reciprocal(self):
        assert self.lo>0
        return Interval(P*P//self.hi,ceildiv(P*P,self.lo))


def log_ratio(z):
    """2 atanh(z), 0<=z<=1/3, with an exact positive tail bound."""
    z=Q(z)
    assert 0<=z<=Q(1,3)
    zi=Interval.rational(z)
    zz=zi.mul(zi)
    power=zi
    total=Interval(0,0)
    for j in range(LOG_TERMS):
        total=total.add(power.scale(Q(2,2*j+1)))
        power=power.mul(zz)
    tail=2*z**(2*LOG_TERMS+1)/((2*LOG_TERMS+1)*(1-z*z))
    return Interval(total.lo,total.hi+ceildiv(tail.numerator*P,tail.denominator))


LOG2=log_ratio(Q(1,3))
LOG_CACHE={1:Interval(0,0)}


def log_integer(n):
    if n not in LOG_CACHE:
        k=n.bit_length()-1
        power=2**k
        LOG_CACHE[n]=LOG2.scale(k).add(log_ratio(Q(n-power,n+power)))
    return LOG_CACHE[n]


def positive_exp(x):
    assert 0<=x.lo<=x.hi<8*P
    term=Interval(P,P)
    total=term
    for k in range(1,EXP_TERMS+1):
        term=term.mul(x).scale(Q(1,k))
        total=total.add(term)
    next_term=term.mul(x).scale(Q(1,EXP_TERMS+1))
    denom=P*(EXP_TERMS+2)-x.hi
    # Sum of the geometric majorant for all omitted positive terms.
    tail_hi=ceildiv(next_term.hi*P*(EXP_TERMS+2),denom)
    return Interval(total.lo,total.hi+tail_hi)


def power(n,b):
    if n==1:
        return Interval(P,P)
    return positive_exp(log_integer(n).scale(b)).reciprocal()


def C_interval(b):
    b=Q(b)
    m=EULER_TERMS
    lo=hi=0
    coeff=[(0,0)]
    for k in range(1,2*m-1):
        p=power(k,b)
        lo+=p.lo
        hi+=p.hi
        if k%2==0:
            coeff.append((lo,hi))
    e_lo=e_hi=Q(0)
    for j,(lo,hi) in enumerate(coeff):
        w=Q((-1)**j*sum(comb(m,k) for k in range(j+1,m+1)),2**m*P)
        if w>=0:
            e_lo+=w*lo
            e_hi+=w*hi
        else:
            e_lo+=w*hi
            e_hi+=w*lo
    return -2*e_hi,-2*e_lo+Q(5,2**(m+1))


def decimal_floor(q,digits):
    scaled=q.numerator*10**digits//q.denominator
    integer,fraction=divmod(scaled,10**digits)
    return f"{integer}.{fraction:0{digits}d}"


def decimal_ceil(q,digits):
    scaled=ceildiv(q.numerator*10**digits,q.denominator)
    integer,fraction=divmod(scaled,10**digits)
    return f"{integer}.{fraction:0{digits}d}"


def main():
    left=Q('1.3022165871012412095923717014')
    center=Q('1.30221658710124120959237170155')
    right=Q('1.3022165871012412095923717017')
    vals={b:C_interval(b) for b in (left,center,right)}
    assert vals[center][0]>vals[left][1]
    assert vals[center][0]>vals[right][1]
    # Unimodality implies left < b_* < right.
    delta=Q(5,24)*(right-left)**2
    c_lo=vals[center][0]
    c_hi=max(vals[left][1],vals[right][1])/(1-delta)
    assert c_lo<c_hi
    c_lo_text=decimal_floor(c_lo,54)
    c_hi_text=decimal_ceil(c_hi,54)
    assert Q(c_lo_text)<=c_lo<c_hi<=Q(c_hi_text)
    record={
        "arithmetic":"outward dyadic intervals and exact Fraction",
        "dyadic_bits":384, "log_terms":LOG_TERMS,
        "exp_terms":EXP_TERMS, "Euler_terms":EULER_TERMS,
        "b_star_interval":[str(left),str(right)],
        "C_star_interval":[str(c_lo),str(c_hi)],
        "C_star_decimal_enclosure":[c_lo_text,c_hi_text],
        "axis_values":{str(b):[str(lo),str(hi)] for b,(lo,hi) in vals.items()},
        "proved_comparisons":["C(center) > C(left)","C(center) > C(right)"]}
    out=Path(__file__).with_name('axis_maximum_certificate.json')
    out.write_text(json.dumps(record,indent=2)+'\n')
    print('Proved: 1.3022165871012412095923717014 < b_* < 1.3022165871012412095923717017')
    print(c_lo_text+' < C_* < '+c_hi_text)
    print('Wrote '+out.name)


if __name__=='__main__':
    main()
