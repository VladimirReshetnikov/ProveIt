#!/usr/bin/env python3
"""Exact rational finite certificates used in the sharp BT reconstruction.

This verifies finite arithmetic side conditions. It does not check the
universal mathematical proof, and it is not an iPRA proof checker. No floating
point operation is used in deciding an assertion.
"""

from fractions import Fraction as F
from math import floor
import json


def small_log_interval(t, terms=18):
    """Bounds log(t) for 1<=t<=2 by an explicitly bounded positive series."""
    t = F(t)
    assert 1 <= t <= 2
    w = (t - 1) / (t + 1)
    lo = 2 * sum((w ** (2*j+1) / (2*j+1) for j in range(terms)), F(0))
    tail = 2 * w ** (2*terms+1) / ((2*terms+1)*(1-w*w))
    return lo, lo + tail


LOG2 = small_log_interval(F(2))


def log_interval(t):
    """Exact enclosure of log(t), with a bounded binary range reduction."""
    t = F(t)
    assert t >= 1
    exponent = 0
    # This loop executes at most numerator.bit_length() iterations.
    for _ in range(t.numerator.bit_length()):
        if t < 2:
            break
        t /= 2
        exponent += 1
    lo, hi = small_log_interval(t)
    return exponent * LOG2[0] + lo, exponent * LOG2[1] + hi


def atan_interval(t, terms=20):
    t = F(t)
    assert 0 <= t <= 1 and terms % 2 == 0
    lo = sum(((-1)**j * t**(2*j+1)/(2*j+1) for j in range(terms)), F(0))
    return lo, lo+t**(2*terms+1)/(2*terms+1)


def arith_arrays(limit):
    phi = list(range(limit+1))
    mu = [1] * (limit+1)
    primes = []
    phi[1] = 1
    for p in range(2, limit+1):
        if phi[p] == p:
            primes.append(p)
            for n in range(p, limit+1, p):
                phi[n] -= phi[n] // p
                mu[n] = -mu[n]
            for n in range(p*p, limit+1, p*p):
                mu[n] = 0
    return phi, mu, primes


def decimal_lower(r, places=9):
    scale = 10 ** places
    return str(F((r.numerator*scale)//r.denominator, scale))


def check():
    phi, mu, primes = arith_arrays(1000)
    atan_one = atan_interval(F(1), terms=100)
    pi_lower, pi_upper = 4*atan_one[0], 4*atan_one[1]
    assert pi_lower > F(31,10) and pi_upper*pi_upper < 10
    harmonic = sum((F(1,n) for n in range(1,10001)), F(0))
    gamma_lower = harmonic - log_interval(10001)[1]
    assert gamma_lower > F(577,1000)
    assert LOG2[0] > F(692,1000)
    assert log_interval(3)[0] > F(1098,1000)
    assert LOG2[1] < F(347,500)
    assert log_interval(6)[1] < F(224,125)
    assert log_interval(F(3,2))[1] < F(203,500)
    assert log_interval(10)[1] < F(5,2)

    # G(n) > log(n+1)+1.07 proves the whole real interval [n,n+1).
    g = F(0)
    minimum = None
    worst_n = None
    denominator_bounds = []
    for n in range(1,1000):
        g += F(mu[n]*mu[n], phi[n])
        if n >= 6:
            lower = g - log_interval(n+1)[1]
            assert lower > F(107,100)
            denominator_bounds.append([n, decimal_lower(lower,6)])
            if minimum is None or lower < minimum:
                minimum, worst_n = lower, n

    # Above 165, inclusion-exclusion with 2,3,5 gives pi(z)<=4z/15+11<=z/3.
    for z in range(100,165):
        assert 3 * sum(p <= z for p in primes) <= z

    small_ranges = [
        ("1<t<=20", F(1,4), F(3,2), (20,)),
        ("18<=t<=270", F(1,6), F(3), (18,270)),
        ("42<=t<=1000", F(2,15), F(11,2), (42,1000)),
        ("700<=t<=20000", F(96,1001), F(35), (700,20000)),
    ]
    endpoints = []
    for interval,a,b,points in small_ranges:
        for t in points:
            upper = (a+b/t)*log_interval(t)[1]
            assert upper < 1
            endpoints.append({"interval":interval,"endpoint":t,
                              "strict_margin_lower":decimal_lower(1-upper)})
    assert log_interval(6)[1] < 2  # positivity of f' in the first small range
    for lower,a,b in [(18,F(1,6),F(3)),(42,F(2,15),F(11,2)),
                      (700,F(96,1001),F(35))]:
        assert lower >= b/a  # derivative numerator increases: no interior maximum

    weighted_offset = F(107,100)-F(347,500)+(F(627,40)-6*(F(224,125)+F(107,100)))/106
    assert weighted_offset > F(361,1000)
    root_offset = F(361,1000)-F(203,1000)-F(1,100)
    assert root_offset > F(7,50)
    hilbert_squared = F(2150,961)+F(1,1000)
    assert hilbert_squared < F(1499,1000)**2
    assert F(143,24) < 6
    assert F(35,2)**2 - 16*F(35,2)-24 == F(9,4)

    return {
        "status":"all finite rational checks passed",
        "scope":"side-condition certificates; not a universal theorem checker or iPRA derivation",
        "log_series_terms_after_binary_range_reduction":18,
        "pi_lower_bound_from_100_arctangent_terms":decimal_lower(pi_lower),
        "gamma_lower_bound":decimal_lower(gamma_lower),
        "denominator_check_range":[6,999],
        "denominator_cases":994,
        "minimum_G_n_minus_log_n_plus_1_lower":decimal_lower(minimum),
        "worst_n":worst_n,
        "prime_count_check_range":[100,164],
        "small_range_endpoint_checks":endpoints,
        "weighted_denominator_offset_lower":str(weighted_offset),
        "root_floor_offset_lower":str(root_offset),
        "hilbert_squared_bound":str(hilbert_squared),
        "denominator_interval_certificates":denominator_bounds,
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
