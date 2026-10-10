#!/usr/bin/env python3
"""Exact rational certificates for Gaussian harmonic-polylogarithm values.

Standard library only. Analytic tail bounds are proved in the accompanying
article. All coefficient enclosures use integer-root inequalities; no binary
floating-point evaluation, PSLQ, or special-function oracle is used.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from functools import lru_cache
from math import comb, factorial
from pathlib import Path
import argparse
import json

@dataclass(frozen=True)
class Interval:
    lo: F
    hi: F
    def __post_init__(self) -> None:
        if self.lo > self.hi:
            raise ValueError("reversed interval")
    def __add__(self, other: Interval | F | int) -> Interval:
        o = other if isinstance(other, Interval) else Interval(F(other), F(other))
        return Interval(self.lo + o.lo, self.hi + o.hi)
    __radd__ = __add__
    def __neg__(self) -> Interval:
        return Interval(-self.hi, -self.lo)
    def __sub__(self, other: Interval | F | int) -> Interval:
        return self + (-other if isinstance(other, Interval) else -F(other))
    def __mul__(self, other: Interval | F | int) -> Interval:
        o = other if isinstance(other, Interval) else Interval(F(other), F(other))
        vals = (self.lo*o.lo, self.lo*o.hi, self.hi*o.lo, self.hi*o.hi)
        return Interval(min(vals), max(vals))
    __rmul__ = __mul__
    def __truediv__(self, n: int | F) -> Interval:
        return self * (1/F(n))

ROOT_CHECKS = 0

def floor_root(n: int, q: int) -> int:
    """Return floor(n**(1/q)) with an integer Newton iteration and replay check."""
    if n < 0 or q < 1:
        raise ValueError("nonnegative radicand and positive root required")
    if n < 2 or q == 1:
        return n
    x = 1 << ((n.bit_length()+q-1)//q)
    while True:
        y = ((q-1)*x + n//pow(x, q-1))//q
        if y >= x:
            break
        x = y
    while pow(x, q) > n:
        x -= 1
    while pow(x+1, q) <= n:
        x += 1
    assert pow(x, q) <= n < pow(x+1, q)
    return x

@lru_cache(maxsize=None)
def inv_power(n: int, exponent: F, digits: int) -> Interval:
    global ROOT_CHECKS
    if n < 1 or exponent < 0:
        raise ValueError("positive base and nonnegative exponent required")
    p, q = exponent.numerator, exponent.denominator
    if q == 1:
        value = F(1, n**p)
        return Interval(value, value)
    scale = 10**digits
    target, denom = scale**q, n**p
    low = floor_root(target//denom, q)
    assert low**q * denom <= target < (low+1)**q * denom
    ROOT_CHECKS += 1
    if low**q * denom == target:
        value = F(low, scale)
        return Interval(value, value)
    return Interval(F(low, scale), F(low+1, scale))

def coefficients(a: F, b: F, n: int, digits: int) -> list[Interval]:
    out: list[Interval] = []
    harmonic = Interval(F(0), F(0))
    for k in range(n):
        if k:
            harmonic = harmonic + inv_power(2*k-1, b, digits) + inv_power(2*k, b, digits)
        out.append(harmonic * inv_power(2*k+1, a, digits))
    return out

def euler(coeff: list[Interval], n: int) -> Interval:
    if n < 1 or n > len(coeff):
        raise ValueError("insufficient coefficients")
    tail = (1 << n)-1
    result = Interval(F(0), F(0))
    for k in range(n):
        result += ((-1)**k * tail) * coeff[k]
        tail -= comb(n, k+1)
    assert tail == 0
    return result / (1 << n)

def atan_inverse(q: int, n: int = 120) -> Interval:
    total = sum((F((-1)**k, (2*k+1)*q**(2*k+1)) for k in range(n)), F(0))
    next_term = F((-1)**n, (2*n+1)*q**(2*n+1))
    return Interval(min(total, total+next_term), max(total, total+next_term))

def constants() -> tuple[Interval, Interval, Interval]:
    pi = 16*atan_inverse(5) - 4*atan_inverse(239)
    n = 180
    log2low = 2*sum((F(1, (2*k+1)*3**(2*k+1)) for k in range(n)), F(0))
    tail = 2*F(1, (2*n+1)*3**(2*n+1)) / (1-F(1,9))
    log2 = Interval(log2low, log2low+tail)
    critical = pi/4 + log2/2
    assert critical.hi < F(283,250)
    return pi, log2, critical

def elementary_j(n: int) -> F:
    return F(4**n * factorial(n)**2, factorial(2*n+1))

def endpoint_errors(n: int, pi: Interval, critical: Interval) -> tuple[Interval, Interval]:
    i = pi/4
    for j in range(n):
        i = 2*i - elementary_j(j)
    B = critical
    for j in range(1, n):
        B = 2*B - elementary_j(j-1) - F(1, 2*j)
    return i, B

def outward(q: F, digits: int, upper: bool) -> str:
    scale = 10**digits
    numerator = q.numerator*scale
    v = -((-numerator)//q.denominator) if upper else numerator//q.denominator
    sign = '-' if v < 0 else ''
    v = abs(v)
    return f'{sign}{v//scale}.{v%scale:0{digits}d}'

def record(x: Interval, digits: int = 32) -> dict[str, str]:
    return {'lower': str(x.lo), 'upper': str(x.hi),
            'decimal_lower': outward(x.lo,digits,False),
            'decimal_upper': outward(x.hi,digits,True),
            'width': str(x.hi-x.lo)}

def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--terms', type=int, default=160)
    ap.add_argument('--digits', type=int, default=140)
    ap.add_argument('--output', type=Path, default=Path(__file__).resolve().parents[1]/'data'/'exact_certificates.json')
    args = ap.parse_args()
    if args.terms < 32 or args.digits < args.terms//2+40:
        raise ValueError("use at least 32 terms and ample coefficient precision")
    pi, log2, critical = constants()
    pairs = [('1/10','9/10'),('1/4','3/4'),('1/2','1/2'),('3/4','1/4'),('9/10','1/10'),
             ('1/10','1/10'),('1/4','1/4'),('1/5','1/2'),('1/10','1'),('1','1'),('2','1'),('1','2')]
    records = []
    stored = {}
    for aa, bb in pairs:
        a,b = F(aa),F(bb)
        coeff = coefficients(a,b,args.terms,args.digits)
        e = euler(coeff,args.terms)
        if a+b == 1:
            # Use the universal critical upper bound; no unstable endpoint
            # recurrence at large N is needed to certify this interval.
            bound = critical.hi/F(1<<args.terms)
            tail_kind = 'sharp critical constant'
        else:
            bound = F(2*(args.terms+1), 1<<args.terms)
            tail_kind = 'all-positive-orders divided-difference bound'
        g = Interval(e.lo-bound,e.hi)
        assert g.hi < 0
        records.append({'a':aa,'b':bb,'terms':args.terms,'tail_kind':tail_kind,
                        'tail_upper':str(bound),'g':record(g)})
        stored[(a,b)] = (g,coeff)
        print(f'PASS a={aa}, b={bb}: {outward(g.lo,28,False)} < g < {outward(g.hi,28,True)}')
    critical_values = [stored[(F(aa),F(bb))][0] for aa,bb in pairs[:5]]
    assert all(critical_values[j].hi < critical_values[j+1].lo for j in range(4))
    # Deliberately test the stronger, false conjecture about EVERY A_N.
    g,coeff = stored[(F(1,10),F(9,10))]
    a8 = (euler(coeff,8)-g)*256
    i8,b8 = endpoint_errors(8,pi,critical)
    excess = a8-b8
    assert excess.lo > F(13,10000)
    assert a8.lo > i8.hi
    result = {
      'status':'PASS', 'arithmetic':'Python integers and fractions.Fraction only',
      'root_inequalities_checked':ROOT_CHECKS,
      'constants':{'pi':record(pi),'log2':record(log2),'C_star':record(critical)},
      'values':records,
      'stronger_monotonicity_counterexample':{
          'N':8,'a':'1/10','A8_a':record(a8),'A8_endpoint_a0':record(b8),
          'difference':record(excess),'strict_lower_threshold':'13/10000'},
      'limitations':'The analytic remainder bounds are supplied by the written proofs; this program is not a proof-assistant formalization.'
    }
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(f'PASS exact counterexample: A8(1/10)-A8(0) > 13/10000')
    print(f'PASS {ROOT_CHECKS} integer-root inequalities; output {args.output}')

if __name__ == '__main__':
    main()
