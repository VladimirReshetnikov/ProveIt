#!/usr/bin/env python3
"""Exact rational centered-resolvent evaluation of strict multiple polylogarithms.

Only integer indices are accepted by this implementation.  The article proves
an analytic extension to an arbitrary positive real final index.  No floating
point value is used in an enclosure or a sign decision.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from math import lcm, isqrt
from typing import Sequence

@dataclass(frozen=True)
class QC:
    re: Q = Q(0)
    im: Q = Q(0)
    def __add__(self, other: object) -> 'QC':
        if not isinstance(other, QC): other = QC(Q(other))
        return QC(self.re + other.re, self.im + other.im)
    __radd__ = __add__
    def __neg__(self) -> 'QC': return QC(-self.re, -self.im)
    def __sub__(self, other: object) -> 'QC': return self + (-other if isinstance(other, QC) else -Q(other))
    def __rsub__(self, other: object) -> 'QC': return -self + other
    def __mul__(self, other: object) -> 'QC':
        if not isinstance(other, QC): other = QC(Q(other))
        return QC(self.re*other.re-self.im*other.im, self.re*other.im+self.im*other.re)
    __rmul__ = __mul__
    def __truediv__(self, other: object) -> 'QC':
        if not isinstance(other, QC): other = QC(Q(other))
        n = other.norm2()
        if not n: raise ZeroDivisionError('zero complex denominator')
        return self * QC(other.re/n, -other.im/n)
    def norm2(self) -> Q: return self.re*self.re+self.im*self.im


def validate_index(index: Sequence[int]) -> tuple[int, ...]:
    out = tuple(index)
    if not out or any(isinstance(s, bool) or not isinstance(s, int) or s < 1 for s in out):
        raise ValueError('index must be a nonempty sequence of positive integers')
    return out


def coefficients(index: Sequence[int], nmax: int) -> list[Q]:
    """Return c[0..nmax], c[n]=[z^n]Li_index(z), by strict prefix sums."""
    index = validate_index(index)
    if nmax < 1: raise ValueError('nmax must be positive')
    c = [Q(0)] + [Q(1, n**index[-1]) for n in range(1,nmax+1)]
    for s in reversed(index[:-1]):
        nxt, total = [Q(0)]*(nmax+1), Q(0)
        for n in range(1,nmax+1):
            nxt[n] = total / n**s  # Add c[n] AFTER taking the strict prefix.
            total += c[n]
        c = nxt
    return c


def centered_moments(index: Sequence[int], terms: int) -> tuple[list[int], int]:
    """Integer numerators for b[k]=integral (2u-1)^k kappa(u) du.

    A common denominator avoids floating point cancellation in the binomial
    transform.  Repeated differences are an independent implementation of the
    displayed binomial formula in the paper.
    """
    if terms < 1: raise ValueError('terms must be positive')
    c = coefficients(index, terms)[1:]
    den = lcm(*(v.denominator for v in c))
    row = [(v.numerator*(den//v.denominator)) << j for j,v in enumerate(c)]
    nums = []
    while row:
        nums.append(row[0])
        row = [row[j+1]-row[j] for j in range(len(row)-1)]
    return nums, den


def centered_value(nums: Sequence[int], den: int, z: QC) -> QC:
    if z.re >= 1: raise ValueError('centered expansion requires Re(z)<1')
    q = z / (2-z)
    v = QC()
    for n in reversed(nums): v = v*q+n
    return z/(1-z/2) * v / den


def sqrt_upper(x: Q, bits: int = 64) -> Q:
    if x < 0: raise ValueError('negative radicand')
    if not x: return Q(0)
    n = isqrt((x.numerator << (2*bits)) // x.denominator)
    out = Q(n+1, 1 << bits)
    assert out*out > x
    return out


def enclosure(index: Sequence[int], z: QC, terms: int,
              moments: tuple[list[int],int] | None = None) -> tuple[QC,Q]:
    """Return (center,radius) containing Li_index(z) in a closed complex disk."""
    index = validate_index(index)
    nums, den = moments if moments is not None else centered_moments(index,terms)
    if len(nums) != terms: raise ValueError('moment length mismatch')
    value = centered_value(nums,den,z)
    mass_bound = 2**(len(index)-1)
    if z == QC(Q(0), Q(1)) and terms % 2 == 0:
        error = Q(2**len(index), 5**(terms//2))
    elif z.norm2() <= Q(1,4):
        error = Q(mass_bound, 3**terms)
    else:
        q = z/(2-z)
        r = sqrt_upper(q.norm2())
        if r >= 1: raise ValueError('increase norm-bound precision near Re(z)=1')
        prefactor = sqrt_upper((z/(1-z/2)).norm2())
        error = prefactor*mass_bound*r**terms/(1-r)
    return value,error


def half_circle(t: Q) -> QC:
    """rho=1/2, theta=2 atan(t); rational t yields a rational complex point."""
    if t <= 0: raise ValueError('positive t required')
    return QC((1-t*t)/(2*(1+t*t)),t/(1+t*t))


def as_record(v: QC, error: Q) -> dict:
    return {'real_lower':str(v.re-error),'real_upper':str(v.re+error),
            'imag_lower':str(v.im-error),'imag_upper':str(v.im+error),
            'complex_disk_radius':str(error)}

if __name__ == '__main__':
    import argparse, json, sys
    if hasattr(sys, "set_int_max_str_digits"): sys.set_int_max_str_digits(0)
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('index',nargs='+',type=int)
    ap.add_argument('--terms',type=int,default=200)
    args=ap.parse_args()
    v,e=enclosure(args.index,QC(Q(0),Q(1)),args.terms)
    print(json.dumps(as_record(v,e),indent=2))
