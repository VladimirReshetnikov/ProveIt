#!/usr/bin/env python3
"""Enclose the unit oloid constants using only Python's exact rational arithmetic.

Usage: python check_values.py [number of decimal places, default 16]
An interval [a,b] in the output means the exact quantity lies between a and b,
inclusively; all printed bounds are rounded outwards.
"""
import argparse
from dataclasses import dataclass
from fractions import Fraction as F


@dataclass(frozen=True)
class Interval:
    lo: F
    hi: F

    def scale(self, scalar):
        left, right = self.lo * scalar, self.hi * scalar
        return Interval(min(left, right), max(left, right))

    def __add__(self, other):
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def __mul__(self, other):
        products = [x*y for x in (self.lo, self.hi) for y in (other.lo, other.hi)]
        return Interval(min(products), max(products))


def atan_reciprocal(denominator, count):
    """Enclose atan(1/denominator) between its consecutive alternating sums."""
    x = F(1, denominator)
    power = x
    partial = F(0)
    for n in range(count):
        partial += power / (2*n+1)
        power *= -x*x
    following = partial + power / (2*count+1)
    return Interval(min(partial, following), max(partial, following))


def enclose(digits):
    # 0.75**10 < 0.1. The extra terms absorb scaling and outward rounding.
    count = 10 * (digits + 8)
    # Machin's identity: pi/2 = 8 atan(1/5) - 2 atan(1/239).
    half_pi = atan_reciprocal(5, digits+8).scale(8) + atan_reciprocal(239, digits+8).scale(-2)
    m = F(3, 4)
    term = F(1)
    knorm = F(1)
    enorm = F(1)
    for j in range(1, count+1):
        # term_j = (binomial(2j,j)/4**j)**2 * m**j.
        term *= m * F(2*j-1, 2*j)**2
        knorm += term
        enorm -= term / (2*j-1)
    tail = m**(count+1) / (1-m)
    K = half_pi * Interval(knorm, knorm+tail)
    E = half_pi * Interval(enorm-tail, enorm)
    volume = K.scale(F(2,3)) + E.scale(F(4,3))
    axial = E.scale(F(32,45)) + K.scale(-F(2,45))
    transverse = E.scale(F(71,45)) + K.scale(-F(19,90))
    return dict(K=K, E=E, area=half_pi.scale(8), volume=volume,
                axial_inertia=axial, transverse_inertia=transverse)


def fixed(number, places):
    sign = "-" if number < 0 else ""
    integer, fraction = divmod(abs(number), 10**places)
    return f"{sign}{integer}.{fraction:0{places}d}" if places else f"{sign}{integer}"


def display(box, places):
    scale = 10**places
    lower, upper = scale*box.lo, scale*box.hi
    floor_lo = lower.numerator // lower.denominator
    ceil_hi = -(-upper.numerator // upper.denominator)
    return f"[{fixed(floor_lo, places)}, {fixed(ceil_hi, places)}]"


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("digits", type=int, nargs="?", default=16)
    args = parser.parse_args()
    if args.digits < 0:
        parser.error("digits must be nonnegative")
    for label, interval in enclose(args.digits).items():
        print(f"{label:18s} {display(interval, args.digits)}")
