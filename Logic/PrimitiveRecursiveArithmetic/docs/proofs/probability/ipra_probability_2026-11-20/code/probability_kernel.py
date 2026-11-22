"""Exact rational reference computations for the accompanying iPRA report.

No floating-point number participates in an acceptance check. This executable
is a reference implementation, not an object-language iPRA proof.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
from math import ceil


def dyadic(k):
    return Q(1, 2 ** k)


@dataclass(frozen=True)
class Cylinder:
    level: int
    values: tuple

    def __post_init__(self):
        if self.level < 0 or len(self.values) != 2 ** self.level:
            raise ValueError("a level-m cylinder has exactly 2**m rational values")
        object.__setattr__(self, "values", tuple(map(Q, self.values)))

    def refine(self, level):
        if level < self.level:
            raise ValueError("refinement cannot discard bits")
        return Cylinder(level, tuple(x for x in self.values
                                     for _ in range(2 ** (level - self.level))))

    def expectation(self):
        return sum(self.values, Q(0)) / 2 ** self.level

    def map(self, f):
        return Cylinder(self.level, tuple(f(x) for x in self.values))

    def combine(self, other, f):
        level = max(self.level, other.level)
        a, b = self.refine(level), other.refine(level)
        return Cylinder(level, tuple(f(x, y) for x, y in zip(a.values, b.values)))

    def d0(self, other):
        return self.combine(other, lambda x, y: min(1, abs(x-y))).expectation()

    def d1(self, other):
        return self.combine(other, lambda x, y: abs(x-y)).expectation()

    def conditional(self, level):
        if level >= self.level:
            return self
        size = 2 ** (self.level - level)
        return Cylinder(level, tuple(sum(self.values[i:i+size], Q(0)) / size
                                     for i in range(0, len(self.values), size)))


def uniform_midpoints(level):
    return Cylinder(level, tuple(Q(2*i+1, 2 ** (level+1))
                                 for i in range(2 ** level)))


def cantor_prefix(level):
    return Cylinder(level, tuple(sum((Q(2*((i >> (level-j)) & 1), 3 ** j)
                                     for j in range(1, level+1)), Q(0))
                                 for i in range(2 ** level)))


def independent_pair(left, right):
    """Use fixed even/odd bit positions, preserving coherence under refinement."""
    depth = max(left.level, right.level)
    level = 2 * depth
    lv, rv = [], []
    for word in range(2 ** level):
        li = ri = 0
        for j in range(depth):
            if j < left.level:
                li = 2*li + ((word >> (level-1-2*j)) & 1)
            if j < right.level:
                ri = 2*ri + ((word >> (level-2-2*j)) & 1)
        lv.append(left.values[li])
        rv.append(right.values[ri])
    return Cylinder(level, tuple(lv)), Cylinder(level, tuple(rv))


def outward(lo, hi, bits=24):
    scale = 2 ** bits
    return (Q((lo*scale).__floor__(), scale),
            Q((hi*scale).__ceil__(), scale))


def exp_negative_interval(t, bits=28):
    """Enclose exp(-t) by inverting a positive Taylor sum for exp(t).

    For N+2 >= 2*t, the positive tail after degree N is at most
    2*t**(N+1)/(N+1)!. The deterministic degree below is conservative;
    the width check is an exact rational certificate.
    """
    t = Q(t)
    if t < 0:
        raise ValueError("t must be nonnegative")
    degree = ceil(2*t) + bits + 2*ceil(t) + 6
    term = total = Q(1)
    for j in range(1, degree+1):
        term *= t / j
        total += term
    tail = 2 * term * t / (degree+1)
    if not Q(degree+2) >= 2*t:
        raise AssertionError("geometric-tail ratio certificate failed")
    lo, hi = 1/(total+tail), 1/total
    if hi-lo > dyadic(bits):
        raise AssertionError("Taylor degree did not meet its certified budget")
    return outward(lo, hi, bits)


def gaussian_kernel_integral(a, b, cells=512, bits=28):
    """Enclose integral_a^b exp(-x*x/2) dx, using |f''| <= 3.

    The composite midpoint error is 3*(b-a)*h*h/24. Taylor
    evaluation intervals and this error are added separately.
    """
    a, b = Q(a), Q(b)
    if not a <= b or cells < 1:
        raise ValueError("ordered endpoints and positive cell count required")
    h = (b-a)/cells
    lower = upper = Q(0)
    for i in range(cells):
        x = a + Q(2*i+1, 2)*h
        lo, hi = exp_negative_interval(x*x/2, bits)
        lower += lo
        upper += hi
    error = 3*(b-a)*h*h/24
    return max(Q(0), h*lower-error), h*upper+error


def normal_cdf_at_one():
    half_lo, half_hi = gaussian_kernel_integral(0, 8)
    _, tail_exp_hi = exp_negative_interval(32)
    # Both tails beyond R=8 have mass <= 2 exp(-32)/8.
    zlo, zhi = 2*half_lo, 2*half_hi + tail_exp_hi/4
    nlo, nhi = gaussian_kernel_integral(0, 1, cells=128)
    return {"Z": outward(zlo, zhi, 20),
            "Phi1": outward(Q(1, 2)+nlo/zhi,
                             Q(1, 2)+nhi/zlo, 20)}


def smooth_step(u):
    u = Q(u)
    if u <= 0:
        return Q(1)
    if u >= 1:
        return Q(0)
    return 1-10*u**3+15*u**4-6*u**5


def wlln_sample_size(variance_bound, epsilon, delta):
    if epsilon <= 0 or delta <= 0 or variance_bound < 0:
        raise ValueError("invalid quantitative hypotheses")
    return max(1, ceil(Q(variance_bound)/(Q(epsilon)**2*Q(delta))))


def strong_sample_size(variance_bound, epsilon, delta):
    if epsilon <= 0 or delta <= 0 or variance_bound < 0:
        raise ValueError("invalid quantitative hypotheses")
    return max(1, ceil(4*Q(variance_bound)/(Q(epsilon)**2*Q(delta))))


def clt_sample_size(third_moment_bound, delta):
    if delta <= 0 or third_moment_bound < 0:
        raise ValueError("invalid quantitative hypotheses")
    return max(1, ceil(25600*(Q(third_moment_bound)+2)**2/Q(delta)**8))
