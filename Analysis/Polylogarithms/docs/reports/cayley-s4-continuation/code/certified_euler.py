#!/usr/bin/env python3
"""Rational Euler acceleration with proved signed-moment error bounds.

All certificate arithmetic uses Fraction; Decimal is only for display.
See the accompanying article for the measure-theoretic proof of the bounds.
No external dependencies.
"""
from __future__ import annotations
from dataclasses import dataclass
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from typing import Iterable
import argparse
import json
from pathlib import Path
import time

@dataclass(frozen=True)
class Interval:
    lo: Q
    hi: Q
    def __post_init__(self) -> None:
        if self.lo > self.hi:
            raise ValueError('Reversed interval')
    @staticmethod
    def point(x: int | Q) -> 'Interval':
        return Interval(Q(x), Q(x))
    def __add__(self, other: 'Interval | int | Q') -> 'Interval':
        if not isinstance(other, Interval): other = Interval.point(other)
        return Interval(self.lo+other.lo, self.hi+other.hi)
    __radd__ = __add__
    def __neg__(self) -> 'Interval':
        return Interval(-self.hi, -self.lo)
    def __sub__(self, other: 'Interval | int | Q') -> 'Interval':
        return self + (-other if isinstance(other, Interval) else -Q(other))
    def __mul__(self, other: 'Interval | int | Q') -> 'Interval':
        if not isinstance(other, Interval): other = Interval.point(other)
        p = [self.lo*other.lo, self.lo*other.hi,
             self.hi*other.lo, self.hi*other.hi]
        return Interval(min(p),max(p))
    __rmul__ = __mul__
    def __pow__(self, n: int) -> 'Interval':
        if not isinstance(n,int) or n < 0:
            raise ValueError('Nonnegative integer power required')
        ans = Interval.point(1)
        base = self
        while n:
            if n & 1: ans = ans*base
            base = base*base
            n //= 2
        return ans
    def contains_zero(self) -> bool:
        return self.lo <= 0 <= self.hi
    def serial(self) -> dict[str, str]:
        # Exact outward rounding keeps portable endpoints compact.
        scale = 10**350
        lo = Q((self.lo*scale).__floor__(), scale)
        hi = Q((self.hi*scale).__ceil__(), scale)
        return {'lower':str(lo), 'upper':str(hi),
                'outward_rounding_decimal_places':350,
                'lower_decimal':decimal_string(lo),
                'upper_decimal':decimal_string(hi),
                'width_decimal':decimal_string(hi-lo)}

def decimal_string(x: Q, digits: int=32) -> str:
    with localcontext() as ctx:
        ctx.prec = digits
        return str(Decimal(x.numerator)/Decimal(x.denominator))

def euler(values: Iterable[Q], N: int, variation_bound: Q) -> Interval:
    """N-term Euler transform, with |error| <= C/2**N.

    Uses binomial-tail weights; no difference table or cancellation-prone
    floating-point subtraction is used. Input must supply exactly N terms.
    """
    if N < 1 or variation_bound < 0:
        raise ValueError('N must be positive and C nonnegative')
    power=1 << N
    tail=power
    bc=1
    acc=Q(0)
    count=0
    for k,ak in enumerate(values):
        if k >= N: raise ValueError('Too many terms')
        tail -= bc
        acc += ((-1)**k)*tail*ak
        bc = bc*(N-k)//(k+1)
        count += 1
    if count != N: raise ValueError('Too few terms')
    center=acc/power
    radius=variation_bound/power
    return Interval(center-radius,center+radius)

def harmonic_values(N: int, a: int, b: int, r: int, d: int) -> Iterable[Q]:
    """H_(r*k)^(b)/(d*k+1)^a, k=0,...,N-1."""
    if min(a,b,r,d) < 1: raise ValueError('Positive parameters required')
    H=Q(0)
    for k in range(N):
        if k:
            for j in range(r*(k-1)+1,r*k+1): H += Q(1,j**b)
        yield H/(d*k+1)**a

def harmonic_interval(N: int,a: int,b: int=1,r: int=2,d: int=2) -> Interval:
    # zeta(2)<5/3 and zeta(b)<=zeta(2) for b>=2.
    C=Q(10*r,3*d) if b==1 else Q(10,3)
    return euler(harmonic_values(N,a,b,r,d),N,C)

def beta(N: int,s: int) -> Interval:
    return euler((Q(1,(2*k+1)**s) for k in range(N)),N,Q(1))

def eta(N: int,s: int) -> Interval:
    return euler((Q(1,(k+1)**s) for k in range(N)),N,Q(1))

def zeta(N: int,s: int) -> Interval:
    if s < 2: raise ValueError('zeta requires s>=2')
    return eta(N,s)*Q(2**(s-1),2**(s-1)-1)

def evaluate(N: int, p: int) -> dict:
    """Enclose S4 identity, S6 conjecture, or rejected S8 candidate."""
    start=time.monotonic()
    vals={'S':harmonic_interval(N,p,r=1), 'pi':4*beta(N,1), 'L':eta(N,1)}
    for b in range(1,p//2+1):
        a=p+1-b
        vals[f'g{a}{b}']=harmonic_interval(N,a,b)
    if p==4:
        vals['beta4']=beta(N,4)
        residual=(7*vals['S']-58*vals['g41']-24*vals['g32']
                  -Q(19,512)*vals['pi']**5+14*vals['beta4']*vals['L'])
        identity='proved_S4_R'
    elif p==6:
        vals.update({'beta6':beta(N,6),'beta4':beta(N,4),'zeta3':zeta(N,3)})
        residual=(vals['S']+Q(12334,527)*vals['g61']+Q(384,31)*vals['g52']
                  +Q(2136,527)*vals['g43']-Q(3179,5713920)*vals['pi']**7
                  +2*vals['beta6']*vals['L']+Q(801,2108)*vals['beta4']*vals['zeta3'])
        identity='conjectured_S6_normalized'
    elif p==8:
        vals.update({f'beta{s}':beta(N,s) for s in [2,4,6,8]})
        vals.update({f'zeta{s}':zeta(N,s) for s in [3,5,7]})
        basis=[vals['S'],vals['g81'],vals['g72'],vals['g63'],vals['g54'],
               vals['pi']**9,vals['beta8']*vals['L'],vals['beta2']*vals['zeta7'],
               vals['beta4']*vals['zeta5'],vals['beta6']*vals['zeta3']]
        coefficients=[-6451250972,-4072849461,-710107844,-10984374763,-6393592639,
                      31875,-1955138863,3459066102,-1034180101,-1477786143]
        residual=sum((x*c for x,c in zip(basis,coefficients)),Interval.point(0))
        identity='rejected_S8_integer_relation'
    else:
        raise ValueError('Supported examples: 4, 6, 8')
    return {'schema':'proveit.signed-moment-interval.v1','N':N,'p':p,'identity':identity,
            'method':'exact rational binomial-tail Euler transform',
            'residual':residual.serial(),'contains_zero':residual.contains_zero(),
            'values':{key:v.serial() for key,v in vals.items()},
            'elapsed_seconds':round(time.monotonic()-start,3),
            'status':('proved independently by word certificate' if p==4 else
                      'numerically supported; not proved' if p==6 else
                      'refuted by rational interval exclusion')}

def main() -> None:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--N',type=int,default=1000)
    ap.add_argument('--p',type=int,choices=[4,6,8],required=True)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    result=evaluate(args.N,args.p)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['N','p','contains_zero','elapsed_seconds','status']}))
    print('residual:',result['residual']['lower_decimal'],result['residual']['upper_decimal'])
    print('width:',result['residual']['width_decimal'])
    if args.p==8 and result['contains_zero']:
        raise SystemExit('N insufficient for the requested exclusion')
    if args.p in [4,6] and not result['contains_zero']:
        raise SystemExit('Unexpected exclusion: recheck the identity and its implementation')

if __name__=='__main__': main()
