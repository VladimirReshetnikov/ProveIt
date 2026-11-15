#!/usr/bin/env python3
"""Exact rational zeta enclosures using finite Euler--Maclaurin.

All error radii are rational and use the complex l1 norm. No floating point
is used here. Correctness is the mathematical argument in the manuscript;
this executable is not a formal proof checker or an iPRA derivation.
Only the Python standard library is required.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from functools import lru_cache
from math import comb, factorial
import argparse
import json


def ceilq(x):
    x = Q(x)
    return -((-x.numerator) // x.denominator)


def dyadic(k):
    return Q(1, 1 << k)


@dataclass(frozen=True)
class CQ:
    re: Q = Q(0)
    im: Q = Q(0)

    def __post_init__(self):
        object.__setattr__(self, 're', Q(self.re))
        object.__setattr__(self, 'im', Q(self.im))

    def __add__(self, other):
        other = cq(other)
        return CQ(self.re + other.re, self.im + other.im)

    __radd__ = __add__

    def __neg__(self):
        return CQ(-self.re, -self.im)

    def __sub__(self, other):
        return self + -cq(other)

    def __mul__(self, other):
        other = cq(other)
        return CQ(self.re*other.re-self.im*other.im,
                  self.re*other.im+self.im*other.re)

    __rmul__ = __mul__

    def inverse(self):
        d = self.re*self.re + self.im*self.im
        if d == 0:
            raise ZeroDivisionError('exact complex denominator is zero')
        return CQ(self.re/d, -self.im/d)

    def __truediv__(self, other):
        return self * cq(other).inverse()

    def norm1(self):
        return abs(self.re) + abs(self.im)


def cq(x):
    return x if isinstance(x, CQ) else CQ(Q(x))


@dataclass(frozen=True)
class Ball:
    c: CQ
    r: Q = Q(0)

    def __post_init__(self):
        object.__setattr__(self, 'c', cq(self.c))
        object.__setattr__(self, 'r', Q(self.r))
        if self.r < 0:
            raise ValueError('negative radius')

    def __add__(self, other):
        other = ball(other)
        return Ball(self.c + other.c, self.r + other.r)

    __radd__ = __add__

    def __neg__(self):
        return Ball(-self.c, self.r)

    def __sub__(self, other):
        return self + -ball(other)

    def __mul__(self, other):
        other = ball(other)
        return Ball(self.c*other.c,
                    self.c.norm1()*other.r + other.c.norm1()*self.r
                    + self.r*other.r)

    __rmul__ = __mul__

    def exact_div(self, other):
        return self * cq(other).inverse()

    def rounded(self, bits):
        d = 1 << bits
        a = Q((self.c.re*d).__floor__(), d)
        b = Q((self.c.im*d).__floor__(), d)
        err = self.r + abs(a-self.c.re) + abs(b-self.c.im)
        return Ball(CQ(a,b), Q(ceilq(err*d), d))


def ball(x):
    return x if isinstance(x, Ball) else Ball(cq(x))


@lru_cache(None)
def bernoullis(n):
    values = [Q(1)]
    for j in range(1, n+1):
        values.append(-sum((Q(comb(j+1,k))*values[k]
                            for k in range(j)), Q(0))/Q(j+1))
    return tuple(values)


def bernoulli_coefficients(n):
    b = bernoullis(n)
    # coefficient of x^j
    return tuple(Q(comb(n,j))*b[n-j] for j in range(n+1))


def bernoulli_bound(n):
    """|B_n(x)| <= this exact coefficient l1 sum, for 0 <= x <= 1."""
    return sum(map(abs, bernoulli_coefficients(n)), Q(0))


def _atanh_log_unit(u, bits):
    """1 <= u <= 2. Exact finite log series with a geometric tail."""
    if not Q(1) <= u <= Q(2):
        raise ValueError('log unit interval')
    v = (u-1)/(u+1)
    length = bits+4
    vv = v*v
    power = v
    total = Q(0)
    for j in range(length):
        total += 2*power/(2*j+1)
        power *= vv
    tail = 2*abs(power)/((2*length+1)*(1-vv))
    return Ball(CQ(total), tail).rounded(bits+4)


@lru_cache(None)
def log_positive(x, bits):
    x = Q(x)
    if x <= 0:
        raise ValueError('positive logarithm argument required')
    u, exponent = x, 0
    # Explicit finite bound, rather than unbounded minimization.
    bound = x.numerator.bit_length()+x.denominator.bit_length()+2
    for _ in range(bound):
        if u >= 2:
            u /= 2
            exponent += 1
        elif u < 1:
            u *= 2
            exponent -= 1
    assert Q(1) <= u < Q(2)
    extra = abs(exponent).bit_length()+5
    answer = (_atanh_log_unit(u, bits+extra)
              + _atanh_log_unit(Q(2), bits+extra)*exponent)
    return answer.rounded(bits+2)


def exp_rational(z, bits):
    """A l1 ball containing exp(z) for exact z in Q(i)."""
    z = cq(z)
    size = max(1, ceilq(z.norm1()))
    squares = (2*size).bit_length()
    h = z / (1 << squares)
    assert h.norm1() <= Q(1,2)
    internal = bits + 8*size + 24
    degree = internal + 6
    term, total = Ball(CQ(1)), Ball(CQ(1))
    for j in range(1, degree+1):
        term = (term*h).exact_div(j).rounded(internal)
        total = (total+term).rounded(internal)
    # All subsequent absolute term ratios are <= 1/2. The rounding
    # errors in every previous recurrence step are already in total.r.
    tail = 2*Q(1,2)**(degree+1)/factorial(degree+1)
    result = Ball(total.c, total.r+tail).rounded(internal)
    for _ in range(squares):
        result = (result*result).rounded(internal)
    return result.rounded(bits+3)


def exp_ball(z, bits):
    z = ball(z)
    base = exp_rational(z.c, bits+6)
    # |exp(c+d)-exp(c)|_1 <= exp(|c|_1+|d|_1) |d|_1.
    growth = 3**max(1, ceilq(z.c.norm1()+z.r))
    return Ball(base.c, base.r+growth*z.r).rounded(bits+2)


def power_positive(n, s, bits):
    """Enclose n^s; n is a positive rational and s exact complex rational."""
    n, s = Q(n), cq(s)
    if n == 1:
        return Ball(CQ(1))
    if s.im == 0 and s.re.denominator == 1:
        return Ball(CQ(n**s.re.numerator))
    # |log n| < bitlength(numerator)+bitlength(denominator).
    logbound = n.numerator.bit_length()+n.denominator.bit_length()
    growth = max(1, ceilq(s.norm1()*logbound))
    logbits = bits+3*growth+ceilq(s.norm1())+16
    w = log_positive(n, logbits)*s
    return exp_ball(w, bits)


def rising(s, n):
    result = CQ(1)
    for j in range(n):
        result = result*(s+j)
    return result


def em_remainder(s, n, m):
    """A rational bound for the analytic remainder at exact rational s.

    Formula: C_(2m) |(s)_(2m)| /(2m)! * N^(1-sigma-2m)/(sigma+2m-1).
    We include a factor 2 to convert the Euclidean tail to l1, use
    l1 bounds for the product, and replace sigma in N's exponent
    by floor(sigma), making the power integral and the bound larger.
    """
    s = cq(s)
    if n < 1 or m < 1 or s.re+2*m-1 <= 0:
        raise ValueError('Euler--Maclaurin domain condition fails')
    product = Q(1)
    for j in range(2*m):
        product *= (s+j).norm1()
    exponent = 1-s.re.__floor__()-2*m
    npower = Q(n)**exponent
    return (2*bernoulli_bound(2*m)*product*npower
            /(factorial(2*m)*(s.re+2*m-1)))


def zeta_em(s, n=32, m=10, bits=80, regularized=False):
    """Rigorous enclosure of zeta(s), or H(s)=zeta(s)-1/(s-1).

    At s=1 only regularized=True is meaningful. All truncations and
    quadrature-free formula terms are finite and use rational arithmetic.
    """
    s = cq(s)
    if s == CQ(1) and not regularized:
        raise ValueError('zeta has a pole at 1; ask for regularized=True')
    tail = em_remainder(s, n, m)
    acc = Ball(CQ(0))
    for j in range(1, n):
        acc += power_positive(Q(j), -s, bits)
    if s == CQ(1):
        acc -= log_positive(Q(n), bits)
    else:
        p = power_positive(Q(n), CQ(1)-s, bits)
        acc += (p - (1 if regularized else 0)).exact_div(s-1)
    acc += power_positive(Q(n), -s, bits)*Q(1,2)
    b = bernoullis(2*m)
    for k in range(1, m+1):
        coeff = rising(s, 2*k-1)*Q(b[2*k], factorial(2*k))
        acc += power_positive(Q(n), CQ(1-2*k)-s, bits)*coeff
    result = Ball(acc.c, acc.r+tail)
    return result if result.r == 0 else result.rounded(min(bits, 100))


def decimal_outward(x, digits, up=False):
    scale = 10**digits
    n = ceilq(x*scale) if up else (x*scale).__floor__()
    sign = '-' if n < 0 else ''
    n = abs(n)
    return sign+str(n//scale)+'.'+str(n%scale).zfill(digits)


def describe(b, digits=14):
    return {
        'center_re': str(b.c.re), 'center_im': str(b.c.im),
        'radius_l1': str(b.r),
        're_lower': decimal_outward(b.c.re-b.r,digits),
        're_upper': decimal_outward(b.c.re+b.r,digits,True),
        'im_lower': decimal_outward(b.c.im-b.r,digits),
        'im_upper': decimal_outward(b.c.im+b.r,digits,True),
        'radius_lt_2_pow_minus_30': b.r < dyadic(30)
    }


def samples():
    examples = [
        ('zeta_2', CQ(2), False), ('zeta_3', CQ(3), False),
        ('zeta_half', CQ(Q(1,2)), False),
        ('zeta_minus_1', CQ(-1), False),
        ('zeta_minus_2', CQ(-2), False),
        ('euler_gamma', CQ(1), True),
        ('zeta_half_plus_14i', CQ(Q(1,2),14), False),
    ]
    return {name: {'N':64, 'm':12, 'working_bits':70,
                   **describe(zeta_em(s,64,12,70,reg))}
            for name,s,reg in examples}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', default='verification/enclosures.json')
    args = parser.parse_args()
    result = samples()
    with open(args.output, 'w', encoding='utf-8') as stream:
        json.dump(result, stream, indent=2)
        stream.write('\n')
    for name, row in result.items():
        print(name, '['+row['re_lower']+', '+row['re_upper']+']',
              '+ i ['+row['im_lower']+', '+row['im_upper']+']')
