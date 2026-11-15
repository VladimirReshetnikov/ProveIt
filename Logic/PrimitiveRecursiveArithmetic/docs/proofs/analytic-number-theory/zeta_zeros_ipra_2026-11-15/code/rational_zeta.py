#!/usr/bin/env python3
"""Exact-rational zeta enclosures and a small Rouche certificate.

No floating point or numerical special-function library is used by the checker.
The mathematical enclosure proof is in the accompanying report.  This is an
executable arithmetic illustration, not a formal proof of its own correctness.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from math import comb, factorial
from functools import lru_cache
import json
from pathlib import Path

BITS = 384
SCALE = 1 << BITS


def down(x: Q) -> Q:
    return Q((x.numerator * SCALE) // x.denominator, SCALE)


def up(x: Q) -> Q:
    return -down(-x)


@dataclass(frozen=True)
class Ball:
    """A complex centre with an L1 error radius, all exact rationals."""
    re: Q
    im: Q = Q(0)
    rad: Q = Q(0)

    @staticmethod
    def make(re=0, im=0, rad=0):
        re, im, rad = Q(re), Q(im), Q(rad)
        assert rad >= 0
        a, b = down(re), down(im)
        return Ball(a, b, up(rad + abs(a-re) + abs(b-im)))

    def norm(self):
        return abs(self.re) + abs(self.im)

    def upper(self):
        return self.norm() + self.rad

    def __neg__(self):
        return Ball(-self.re, -self.im, self.rad)

    def __add__(self, other):
        if not isinstance(other, Ball):
            other = Ball.make(other)
        return Ball.make(self.re + other.re, self.im + other.im,
                         self.rad + other.rad)

    __radd__ = __add__

    def __sub__(self, other):
        return self + (-other if isinstance(other, Ball) else -Q(other))

    def __mul__(self, other):
        if not isinstance(other, Ball):
            other = Ball.make(other)
        return Ball.make(self.re*other.re-self.im*other.im,
                         self.re*other.im+self.im*other.re,
                         self.norm()*other.rad + other.norm()*self.rad
                         + self.rad*other.rad)

    __rmul__ = __mul__

    def scale(self, q):
        q = Q(q)
        return Ball.make(self.re*q, self.im*q, self.rad*abs(q))


def ceilq(q):
    return -((-q.numerator)//q.denominator)


@lru_cache(None)
def log_rational(x: Q, terms=160) -> Ball:
    """Atanh series, with a direct rational geometric tail."""
    assert x > 0
    if x < 1:
        return -log_rational(1/x, terms)
    k = 0
    while x >= 2:  # bounded by the bit length of numerator/denominator
        x /= 2
        k += 1

    def series(v):
        y = (v-1)/(v+1)
        yy = y*y
        power = y
        total = Q(0)
        for j in range(terms):
            total += 2*power/(2*j+1)
            power *= yy
        err = 2*abs(power)/((2*terms+1)*(1-yy))
        return Ball.make(total, 0, err)

    return series(x) + series(Q(2)).scale(k)


def exp_ball(x: Ball, precision=180) -> Ball:
    """Taylor centre and analytic perturbation/tail bounds in the L1 norm."""
    s = max(1, ceilq(x.norm()))
    degree = 4*s + precision + 8
    centre = Ball.make(x.re, x.im)
    term = Ball.make(1)
    total = term
    for n in range(1, degree+1):
        term = (term * centre).scale(Q(1,n))
        total = total + term
    assert x.rad <= 1
    tail = Q(1, 1 << (degree-4*s))
    perturbation = x.rad * (4 ** (s+1))
    return Ball.make(total.re, total.im,
                     total.rad + tail + perturbation)


def cpow_positive(n: int, exponent: Ball) -> Ball:
    return exp_ball(exponent * log_rational(Q(n)))


def inverse_exact(re: Q, im: Q) -> Ball:
    d = re*re + im*im
    assert d > 0
    return Ball.make(re/d, -im/d)


@lru_cache(None)
def bernoulli(n: int) -> Q:
    if n == 0:
        return Q(1)
    return -sum((Q(comb(n+1,k))*bernoulli(k) for k in range(n)), Q(0))/(n+1)


def zeta_ball(re: Q, im: Q, N=64, m=10) -> Ball:
    """Euler--Maclaurin, with |B_2m(x)| bounded by coefficient L1 norm.

    The displayed remainder bound uses re>=0, sufficient for this example.
    """
    re, im = Q(re), Q(im)
    assert re >= 0 and (re != 1 or im != 0) and N >= 2 and m >= 1
    s = Ball.make(re, im)
    result = Ball.make(0)
    for n in range(1,N):
        result += cpow_positive(n, -s)
    result += cpow_positive(N, Ball.make(1)-s) * inverse_exact(re-1, im)
    result += cpow_positive(N, -s).scale(Q(1,2))
    rising = Ball.make(1)
    for k in range(1,2*m+1):
        rising *= s + (k-1)
        if k % 2 == 1:
            j = (k+1)//2
            result += (rising * cpow_positive(N, Ball.make(-k)-s)).scale(
                bernoulli(2*j)/factorial(2*j))
    coeff_bound = sum((Q(comb(2*m,j))*abs(bernoulli(j))
                       for j in range(2*m+1)), Q(0))/factorial(2*m)
    product_bound = Q(1)
    for j in range(2*m):
        product_bound *= abs(re+j) + abs(im)
    remainder = coeff_bound*product_bound/(Q(2*m-1)*N**(2*m-1))
    # The integral bound is Euclidean.  A factor two makes it an L1 radius.
    return Ball.make(result.re, result.im, result.rad + 2*remainder)


def qstr(q):
    return str(q.numerator) if q.denominator == 1 else f"{q.numerator}/{q.denominator}"


def decimal(q, places=20):
    """Display only: truncated exact decimal, no float conversion."""
    sign = '-' if q < 0 else ''
    n = abs(q.numerator) * 10**places // q.denominator
    a,b = divmod(n,10**places)
    return f"{sign}{a}.{b:0{places}d}"


def zero_certificate():
    c_re, c_im = Q(1,2), Q('14.1347251417347')
    r, h, second = Q(1,10**6), Q(1,10**6), Q(4096)
    f0 = zeta_ball(c_re,c_im)
    fm = zeta_ball(c_re-h,c_im)
    fp = zeta_ball(c_re+h,c_im)
    difference = (fp-fm).scale(1/(2*h))
    derivative_error = difference.rad + second*h/2
    lower_centre_slope = max(abs(difference.re),abs(difference.im))
    lhs = f0.upper() + derivative_error*r + second*r*r/2
    rhs = lower_centre_slope*r
    derivative_lower = lower_centre_slope-derivative_error-second*r
    assert lhs < rhs and derivative_lower > 0
    contraction = (derivative_error+second*r)/lower_centre_slope
    centre_motion = f0.upper()/lower_centre_slope
    assert contraction < Q(1,64) and centre_motion < r/64
    return {
        'description': 'Rational Rouche certificate for one simple zeta zero in a disk.',
        'centre': [qstr(c_re),qstr(c_im)],
        'radius': qstr(r), 'finite_difference_step': qstr(h),
        'second_derivative_bound': qstr(second),
        'f_centre': [qstr(f0.re),qstr(f0.im)],
        'f_radius': qstr(f0.rad),
        'slope_centre': [qstr(difference.re),qstr(difference.im)],
        'slope_error': qstr(derivative_error),
        'rouche_left': qstr(lhs), 'rouche_right': qstr(rhs),
        'rouche_strict': lhs < rhs,
        'derivative_lower': qstr(derivative_lower),
        'derivative_positive': derivative_lower > 0,
        'newton_contraction_upper': qstr(contraction),
        'newton_centre_motion_upper': qstr(centre_motion),
        'newton_maps_disk_strictly_inside': contraction < Q(1,64) and centre_motion < r/64,
        'summary_decimal': {
            'f_l1_upper': decimal(f0.upper(),30),
            'slope_real': decimal(difference.re),
            'slope_imaginary': decimal(difference.im),
            'rouche_left': decimal(lhs,24),
            'rouche_right': decimal(rhs,24),
            'derivative_lower': decimal(derivative_lower),
            'newton_contraction_upper': decimal(contraction),
        },
        'interpretation': [
            'The report proves the enclosure, Taylor and Rouche implications.',
            'The disk has winding count one; the zero is simple.',
            'Functional-equation symmetry and uniqueness put it on Re(s)=1/2.',
            'No assertion that it is the lowest positive zero is made.',
            'This computation is not a Lean or iPRA proof certificate.'
        ]
    }


def main():
    cert = zero_certificate()
    out = Path(__file__).resolve().parent.parent/'verification'/'simple_zero.json'
    out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps(cert,indent=2)+'\n')
    print(json.dumps(cert['summary_decimal'],indent=2))
    print('Exact rational Rouche and simplicity checks passed.')


if __name__ == '__main__':
    main()
