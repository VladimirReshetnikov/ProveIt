#!/usr/bin/env python3
"""Certify the polynomial product over reduced primitive positive forms.

All enclosures use the standard Python integer library.  Coefficient lists
start with the constant term.  The integrality of the class polynomial is the
classical theorem of complex multiplication (valid for arbitrary orders).
"""

import argparse
from dataclasses import dataclass
from math import factorial, gcd, isqrt
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
PRECISION = 1200
SCALE = 1 << PRECISION
K = 164


def ceil_div(n, d):
    return -(-n // d)


@dataclass(frozen=True)
class Real:
    """The real interval [lo,hi]/SCALE."""

    lo: int
    hi: int

    def __add__(self, other):
        return Real(self.lo + other.lo, self.hi + other.hi)

    def __neg__(self):
        return Real(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        vals = [a*b for a in (self.lo, self.hi) for b in (other.lo, other.hi)]
        return Real(min(vals) // SCALE, ceil_div(max(vals), SCALE))

    def scale(self, n):
        a, b = self.lo*n, self.hi*n
        return Real(min(a, b), max(a, b))

    def divide_int(self, n):
        assert n > 0
        return Real(self.lo // n, ceil_div(self.hi, n))

    def reciprocal(self):
        assert self.lo > 0
        return Real(SCALE**2 // self.hi, ceil_div(SCALE**2, self.lo))

    def expand(self, ticks):
        return Real(self.lo-ticks, self.hi+ticks)

    def unique_integer(self):
        val = ceil_div(self.lo, SCALE)
        assert val == self.hi // SCALE, "increase precision or truncation"
        return val


ZERO = Real(0, 0)
ONE = Real(SCALE, SCALE)


@dataclass(frozen=True)
class Box:
    """Complex numbers with independently enclosed real and imaginary parts."""

    re: Real
    im: Real

    def __add__(self, z):
        return Box(self.re + z.re, self.im + z.im)

    def __sub__(self, z):
        return Box(self.re - z.re, self.im - z.im)

    def __mul__(self, z):
        return Box(self.re*z.re-self.im*z.im, self.re*z.im+self.im*z.re)

    def divide_int(self, n):
        return Box(self.re.divide_int(n), self.im.divide_int(n))

    def reciprocal(self):
        t = (self.re*self.re + self.im*self.im).reciprocal()
        return Box(self.re*t, (-self.im)*t)

    def expand(self, ticks):
        return Box(self.re.expand(ticks), self.im.expand(ticks))


CZERO, CONE = Box(ZERO, ZERO), Box(ONE, ZERO)


def power(z, n):
    out = CONE
    while n:
        if n % 2:
            out = out*z
        z = z*z
        n //= 2
    return out


def arctan_inverse(n):
    total, sign, power_n, k = ZERO, 1, n, 0
    while (2*k + 1) * power_n <= SCALE:
        total = total + ONE.divide_int((2*k + 1) * power_n).scale(sign)
        sign = -sign
        power_n *= n*n
        k += 1
    # Alternating-series remainder has absolute value below one tick.
    return total.expand(1)


PI = arctan_inverse(5).scale(16) - arctan_inverse(239).scale(4)


def exponential(z):
    """Taylor series at z/256 followed by eight squarings."""
    w = z.divide_int(256)
    assert max(abs(w.re.lo), abs(w.re.hi)) + max(abs(w.im.lo), abs(w.im.hi)) <= SCALE
    term = total = CONE
    count = 205
    for i in range(1, count+1):
        term = (term*w).divide_int(i)
        total = total + term
    # |w| <= 1, so the error is <= e/(count+1)!.
    total = total.expand(ceil_div(3*SCALE, factorial(count+1)))
    for _ in range(8):
        total = total*total
    return total


def e4_coefficients():
    sigma = [0] * (K+1)
    for d in range(1, K+1):
        for n in range(d, K+1, d):
            sigma[n] += d**3
    return [CONE] + [Box(ONE.scale(240*s), ZERO) for s in sigma[1:]]


E4_COEFFS = e4_coefficients()


def singular_modulus(D, a, b):
    s = isqrt(D*SCALE*SCALE)
    sqrt_D = Real(s, s+1)
    # Using +b instead of -b enumerates the same conjugate multiset.
    q = exponential(Box((-(PI*sqrt_D)).divide_int(a), PI.scale(b).divide_int(a)))
    # Reduction gives sqrt(D)/a >= sqrt(3), hence |q| < 1/200.
    e4 = CZERO
    for c in reversed(E4_COEFFS):
        e4 = e4*q+c
    # sigma_3(n) < 2 n^3; successive bounds n^3 / 200^n
    # have ratio <= 8/200 < 1/2.
    e4 = e4.expand(ceil_div(960*(K+1)**3*SCALE, 200**(K+1)))
    product, qn = CONE, q
    for _ in range(K):
        product = product*(CONE-qn)
        qn = qn*q
    # The sum of |q|^n for n>K is <= 2/200^(K+1). The
    # truncated product has modulus < exp(1/199) < 2, while
    # |prod_tail-1| <= exp(sum_tail)-1 <= 2 sum_tail.
    product = product.expand(ceil_div(8*SCALE, 200**(K+1)))
    return power(e4, 3)*(q*power(product, 24)).reciprocal()


def reduced_forms(D):
    for a in range(1, isqrt(D//3)+1):
        for b in range(-a, a+1):
            c, rem = divmod(D+b*b, 4*a)
            if rem or c < a or gcd(gcd(a, b), c) != 1:
                continue
            if b < 0 and (a == c or a == -b):
                continue
            yield a, b, c


def class_polynomial(D, class_number):
    coeffs = [CONE]
    forms = list(reduced_forms(D))
    assert len(forms) == class_number
    for a, b, _ in forms:
        root = singular_modulus(D, a, b)
        coeffs = [old1-old2*root for old1, old2 in zip([CZERO]+coeffs, coeffs+[CZERO])]
    assert all(c.im.lo <= 0 <= c.im.hi for c in coeffs)
    return [c.re.unique_integer() for c in coeffs]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="regenerate class_polynomials.json")
    args = parser.parse_args()
    assert class_polynomial(3, 1) == [0, 1]
    assert class_polynomial(4, 1) == [-1728, 1]
    assert class_polynomial(15, 2) == [-121287375, 191025, 1]
    rows = [list(map(int, line.split())) for line in (HERE/"discriminants.txt").read_text().splitlines()]
    out = {str(-D): class_polynomial(D, h) for D, h in rows if D != 4075}
    assert len(out) == 79
    path = HERE/"class_polynomials.json"
    if args.write:
        path.write_text(json.dumps(out, indent=2)+"\n")
    else:
        assert json.loads(path.read_text()) == out
    print("Certified 79 integer ring class polynomials and the three reference polynomials.")


if __name__ == "__main__":
    main()
