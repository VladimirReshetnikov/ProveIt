#!/usr/bin/env python3
"""Exact finite certificate for A306631 and the sharp inverse-bias bounds.

Only Python's standard library is used. All enclosures have rational
endpoints; no floating-point or special-function call enters a proof check.
The analytic n >= 400 argument is in article.tex (not formalized here).
Run: python code/certify.py --output results/certificate.json
"""
from __future__ import annotations
import argparse
import csv
import hashlib
import json
from dataclasses import dataclass
from fractions import Fraction
from math import factorial, isqrt
from pathlib import Path

SCALE = 10**70


def ceildiv(a: int, b: int) -> int:
    assert b > 0
    return -((-a) // b)


@dataclass(frozen=True)
class Interval:
    """Encloses [lo/SCALE, hi/SCALE] with inclusive endpoints."""
    lo: int
    hi: int

    def __post_init__(self) -> None:
        assert self.lo <= self.hi

    @staticmethod
    def rational(value: int | Fraction) -> Interval:
        q = Fraction(value)
        return Interval(q.numerator*SCALE//q.denominator,
                        ceildiv(q.numerator*SCALE, q.denominator))

    def __add__(self, other: Interval) -> Interval:
        return Interval(self.lo+other.lo, self.hi+other.hi)

    def __neg__(self) -> Interval:
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other: Interval) -> Interval:
        return self + (-other)

    def __mul__(self, other: Interval) -> Interval:
        products = [a*b for a in (self.lo,self.hi)
                    for b in (other.lo,other.hi)]
        return Interval(min(products)//SCALE,
                        ceildiv(max(products),SCALE))

    def __truediv__(self, other: Interval) -> Interval:
        assert other.lo > 0
        pairs = [(a*SCALE,b) for a in (self.lo,self.hi)
                 for b in (other.lo,other.hi)]
        return Interval(min(a//b for a,b in pairs),
                        max(ceildiv(a,b) for a,b in pairs))

    def sqrt(self) -> Interval:
        assert self.lo >= 0
        low = isqrt(self.lo*SCALE)
        high = isqrt(self.hi*SCALE)
        if high*high < self.hi*SCALE:
            high += 1
        return Interval(low,high)

    def exp(self) -> Interval:
        """Taylor to degree 80 on [0,1], then six exact squarings."""
        assert 0 <= self.lo <= self.hi <= 64*SCALE
        t = self / I(64)
        term = I(1)
        total = I(1)
        for j in range(1,81):
            term = term*t/I(j)
            total = total+term
        # For 0 <= t <= 1, tail <= (82/81)/81! < 2/81! < 1/SCALE.
        assert 2*SCALE < factorial(81)
        total = Interval(total.lo,total.hi+1)
        for _ in range(6):
            total = total*total
        return total

    def outward_decimal(self, places: int = 45) -> list[str]:
        assert 0 <= places <= 70
        factor = 10**(70-places)
        lower, upper = self.lo//factor, ceildiv(self.hi,factor)
        def render(x: int) -> str:
            sign = '-' if x < 0 else ''
            x = abs(x)
            return f'{sign}{x//10**places}.{x%10**places:0{places}d}'
        return [render(lower),render(upper)]


I = Interval.rational


def atan_reciprocal(q: int, terms: int) -> Interval:
    value = sum((Fraction((-1)**j,(2*j+1)*q**(2*j+1))
                 for j in range(terms)),Fraction(0))
    next_term = Fraction((-1)**terms,(2*terms+1)*q**(2*terms+1))
    lower, upper = sorted((value,value+next_term))
    return Interval(I(lower).lo,I(upper).hi)


PI = I(16)*atan_reciprocal(5,60)-I(4)*atan_reciprocal(239,15)
C = PI*I(Fraction(2,3)).sqrt()
DELTA = I(Fraction(1,24))+I(3)/(PI*PI)
SQRT3 = I(3).sqrt()


def hardy_ramanujan(x: Fraction) -> Interval:
    assert x > 0
    xx = I(x)
    return (C*xx.sqrt()).exp()/(I(4)*SQRT3*xx)


def partitions(limit: int) -> list[int]:
    assert limit >= 0
    p = [0]*(limit+1)
    p[0] = 1
    for n in range(1,limit+1):
        k = 1
        while (left := k*(3*k-1)//2) <= n:
            sign = 1 if k % 2 else -1
            p[n] += sign*p[n-left]
            right = k*(3*k+1)//2
            if right <= n:
                p[n] += sign*p[n-right]
            k += 1
    return p


def inverse_bias(n: int, y: int, steps: int = 190) -> Interval:
    """Bisect the increasing H branch, returning n - H^{-1}(y)."""
    lower, upper = Fraction(n-1), Fraction(n)
    assert hardy_ramanujan(lower).hi < y*SCALE
    assert hardy_ramanujan(upper).lo > y*SCALE
    for _ in range(steps):
        middle = (lower+upper)/2
        value = hardy_ramanujan(middle)
        if value.hi < y*SCALE:
            lower = middle
        elif value.lo > y*SCALE:
            upper = middle
        else:
            raise ArithmeticError('Working precision insufficient for bisection')
    return Interval(I(Fraction(n)-upper).lo,I(Fraction(n)-lower).hi)


def run(details_path: Path | None = None) -> dict:
    p = partitions(399)
    assert p[:12] == [1,1,2,3,5,7,11,15,22,30,42,56]
    # Independently recompute via the finite product, not the pentagonal recurrence.
    product = [1]+[0]*399
    for part in range(1,400):
        for n in range(part,400):
            product[n] += product[n-part]
    assert p == product
    checks = 0
    details: list[dict] = []
    margins: list[tuple[int,int,str]] = []
    def H_below(n: int, shift: Fraction, label: str) -> None:
        nonlocal checks
        value = hardy_ramanujan(Fraction(n)-shift)
        gap = p[n]*SCALE-value.hi
        details.append({'n':n, 'shift':str(shift), 'relation':'H < p',
                        'claim':label, 'p_n':p[n], 'H_lo':value.lo,
                        'H_hi':value.hi, 'endpoint_denominator':SCALE})
        assert gap > 0, (n,label,'H not below')
        checks += 1
        margins.append((gap,n,label))
    def H_above(n: int, shift: Fraction, label: str) -> None:
        nonlocal checks
        value = hardy_ramanujan(Fraction(n)-shift)
        gap = value.lo-p[n]*SCALE
        details.append({'n':n, 'shift':str(shift), 'relation':'H > p',
                        'claim':label, 'p_n':p[n], 'H_lo':value.lo,
                        'H_hi':value.hi, 'endpoint_denominator':SCALE})
        assert gap > 0, (n,label,'H not above')
        checks += 1
        margins.append((gap,n,label))
    for n in range(2,400):
        H_below(n,Fraction(1),'d < 1')
        H_above(n,Fraction(7,20),'d > 7/20')
    for n in range(10,400):
        if n != 11:
            H_below(n,Fraction(49,100),'d < 49/100')
    H_below(11,Fraction(499,1000),'beta11 < 499/1000')
    H_above(11,Fraction(498,1000),'beta11 > 498/1000')
    H_below(2,Fraction(797,1000),'beta2 < 797/1000')
    H_above(2,Fraction(796,1000),'beta2 > 796/1000')
    for n in range(3,10):
        H_below(n,Fraction(79,100),'d < 79/100')
    failures = [2,3,4,5,7,9]
    for n in range(2,10):
        if n in failures:
            H_above(n,Fraction(1,2),'nearest-integer failure')
        else:
            H_below(n,Fraction(1,2),'nearest-integer success')
    assert DELTA.hi < I(Fraction(7,20)).lo
    assert I(25).exp().lo > 9*50**4*SCALE
    assert I(Fraction(1,24)).hi + (I(Fraction(63,25))/(C*C)).hi < I(Fraction(43,100)).lo
    beta2, beta11 = inverse_bias(2,p[2]), inverse_bias(11,p[11])
    smallest = min(margins)
    sha = hashlib.sha256((','.join(map(str,p))).encode()).hexdigest()
    if details_path is not None:
        details_path.parent.mkdir(parents=True, exist_ok=True)
        with details_path.open('w', newline='') as stream:
            writer = csv.DictWriter(stream, fieldnames=list(details[0]))
            writer.writeheader()
            writer.writerows(details)
    return {
        'status':'PASS',
        'scope':'Exact finite certificate n=2..399; analytic proof for n>=400 is in article.tex.',
        'arithmetic':'Integer endpoints divided by 10^70; exact directed rounding.',
        'H_comparison_count':checks,
        'partition_values_independently_cross_checked':400,
        'partition_values_sha256':sha,
        'nearest_integer_exceptions_n_ge_2':failures,
        'pi_enclosure':PI.outward_decimal(),
        'delta_enclosure':DELTA.outward_decimal(),
        'beta2_enclosure':beta2.outward_decimal(),
        'beta11_enclosure':beta11.outward_decimal(),
        'best_shift_n_ge_10':((beta11+DELTA)/I(2)).outward_decimal(),
        'minimax_error_n_ge_10':((beta11-DELTA)/I(2)).outward_decimal(),
        'unshifted_symmetric_rounding_margin':(I(Fraction(1,2))-beta11).outward_decimal(),
        'smallest_absolute_comparison_margin':{
            'n':smallest[1], 'claim':smallest[2],
            'certified_lower_bound':Interval(smallest[0],smallest[0]).outward_decimal(30)[0]},
        'not_a_Lean_or_Rocq_kernel_certificate':True
    }


def main() -> None:
    if not __debug__:
        raise RuntimeError('Run without -O: assertions are proof checks.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    parser.add_argument('--details',type=Path, help='Optional CSV of every H interval comparison.')
    args = parser.parse_args()
    result = run(args.details)
    text = json.dumps(result,indent=2)+'\n'
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(text)
    print(text,end='')


if __name__ == '__main__':
    main()
