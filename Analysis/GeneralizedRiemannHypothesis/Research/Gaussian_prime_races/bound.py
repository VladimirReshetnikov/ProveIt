#!/usr/bin/env python3
"""Exact rational certificate for the upper endpoint of the modulo-four transition."""

from fractions import Fraction as Q
from math import factorial, isqrt

SCALE = 10**12
M = 2047


def log_ratio(x):
    """Enclose log(x) for 1 <= x <= 2 using the atanh series."""
    assert 1 <= x <= 2
    u = (x - 1) / (x + 1)
    lower = 2 * sum(u ** (2*j + 1) / (2*j + 1) for j in range(13))
    error = 2 * u**27 / (27 * (1 - u*u))
    return lower, lower + error


LOG2 = log_ratio(Q(2))


def log_integer(n):
    k = n.bit_length() - 1
    low, high = log_ratio(Q(n, 2**k))
    return k * LOG2[0] + low, k * LOG2[1] + high


def round_out(pair):
    low, high = pair
    return (Q((low * SCALE).__floor__(), SCALE),
            Q((high * SCALE).__ceil__(), SCALE))


def partial(power, cutoff):
    """Bounds for the indicated partial sums of beta and its derivative."""
    b_lo = b_hi = d_lo = d_hi = Q(0)
    for n in range(1, cutoff + 1, 2):
        root = isqrt(SCALE**2 * n)
        lo = Q(SCALE, n**power * (root + 1))
        hi = Q(SCALE, n**power * root)
        ll, lh = log_integer(n)
        low, high = round_out((lo, hi))
        dl, dh = round_out((lo * ll, hi * lh))
        if n % 4 == 1:
            b_lo, b_hi = b_lo + low, b_hi + high
            d_lo, d_hi = d_lo - dh, d_hi - dl
        else:
            b_lo, b_hi = b_lo - high, b_hi - low
            d_lo, d_hi = d_lo + dl, d_hi + dh
    return b_lo, b_hi, d_lo, d_hi


def main():
    # Elementary enclosures for pi and Euler's constant.
    pi_l, pi_u = Q(3141592, 10**6), Q(3141593, 10**6)
    ec_l, ec_u = Q(577215, 10**6), Q(577216, 10**6)
    # Machin's identity, with signed alternating Taylor remainders.
    def atan_small(x):
        value = sum((-1)**j * x**(2*j + 1)/(2*j + 1) for j in range(11))
        return value - x**23/23, value

    p, r = atan_small(Q(1, 5))
    u, v = atan_small(Q(1, 239))
    assert pi_l < 16*p - 4*v <= 16*r - 4*u < pi_u
    # Euler--Maclaurin for H_n: the next correction is between 0 and 1/(12n^2).
    n = 1024
    harmonic = sum(Q(1, j) for j in range(1, n+1))
    lower = harmonic - 10*LOG2[1] - Q(1, 2*n)
    upper = harmonic - 10*LOG2[0] - Q(1, 2*n) + Q(1, 12*n*n)
    assert ec_l < lower <= upper < ec_u
    log_c_l = log_ratio(4 / pi_u)[0]
    log_c_u = log_ratio(4 / pi_l)[1]
    a1_u = (log_c_u + 4 - ec_l - pi_l / 2 - 3 * LOG2[0]) / 2
    a2_l = (log_c_l + Q(4,3) - ec_u + pi_l / 2 - 3 * LOG2[1]) / 2
    b1_l, _, _, d1_u = partial(1, M)
    _, b2_u, d2_l, _ = partial(2, M + 2)
    assert b1_l > 0 and b2_u > 0 and d1_u > 0 and d2_l > 0
    D1_u = a1_u + d1_u / b1_l
    D2_l = a2_l + d2_l / b2_u
    assert D1_u < Q(15427,100000) and D2_l > Q(29847,100000)
    moment_u = (D1_u - D2_l / 2) / 3
    assert moment_u < Q(168,100000)
    exp_lower = sum(Q(83,44)**k / factorial(k) for k in range(16))
    assert 44**2 / exp_lower < 294
    assert 294 * moment_u < Q(1,2)
    print("Certified with rational arithmetic:")
    print("D(3/2) < 0.15427, D(5/2) > 0.29847")
    print("sum_gamma ((1+gamma^2)(4+gamma^2))^(-1) < 0.00168")
    print("For h>=1/22, sum_gamma exp(-h gamma^2) < 294*0.00168 < 1/2.")


if __name__ == "__main__":
    main()
