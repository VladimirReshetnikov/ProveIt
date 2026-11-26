#!/usr/bin/env python3
"""Rational-arithmetic certificate for the exponent-six cofactor cutoff."""
from fractions import Fraction as Q
from math import factorial

# exp(47.2)>3.1*10^20 follows from a positive Taylor lower sum.
x0 = 31 * 10**19
t = Q(236, 5)
partial_sum = sum(t**k / factorial(k) for k in range(81))
assert partial_sum > x0
assert Q(1881, 1000) * t + Q(618, 100) < 95
assert x0 > (4 * 95**6) * 10**8
# For monotonicity, x0>exp(6) since exp(1)<3.
assert x0 > 3**6
print('At x0 = 3.1e20, B(x0) = 1.881 log(x0) + 6.18 < 95.')
print('The lower bound x0/(4*95^6) exceeds 100000000.')
print('For x >= x0, d(log(x/B(x)^6))/d(log x) = 1 - 6*1.881/B(x) > 0.')
