"""Independent exact derivative-polynomial verification through C3.

This module deliberately does not import coefficients.py. It computes
Q_0=v^2, Q_r=r Q_{r-1}+Q'_{r-1}, so that
H^(r)(t)=(-1)^r Q_r(v)/(4 t^(r+1)). It uses explicit B1,B2,B3,
and ordinary truncated-series multiplication rather than the primary
exponential recurrence. All comparisons are finite checks, not a proof.
"""
from fractions import Fraction as Q
from math import factorial


def multiply(left, right):
    out = {}
    for (e1, d1), x in left.items():
        for (e2, d2), y in right.items():
            if e1 + e2 <= 6:
                key = (e1 + e2, d1 + d2)
                out[key] = out.get(key, Q(0)) + x * y
    return {key: value for key, value in out.items() if value}


def derivative_polynomials(order):
    p, result = [Q(0), Q(0), Q(1)], []
    result.append(p)
    for r in range(1, order + 1):
        p = [r * p[i] + ((i + 1) * p[i + 1] if i + 1 < len(p) else 0)
             for i in range(len(p))]
        result.append(p)
    return result


def independent_coefficients(v, s):
    if type(v) not in (int, Q) or type(s) not in (int, Q):
        raise ValueError('v and s must be int or Fraction')
    v, s = Q(v), Q(s)
    if v <= 0 or s < 0:
        raise ValueError('require v>0 and s>=0')
    D = v * v + 3 * v + 1
    alpha, a = (3 - 2 * s) / 4, Q(1, 2) - s
    B1, B2, B3 = a * a / 4 - v / 48, -a / 48, v / 5760 + Q(1, 2304)
    polys = derivative_polynomials(8)
    exponent = {}
    for m in range(1, 7):
        r = m + 2
        qr = sum((coefficient * v ** degree for degree, coefficient in enumerate(polys[r])), Q(0))
        exponent[m, r] = Q((-1) ** r, 4 * factorial(r)) * qr
        exponent[m, m] = alpha * Q((-1) ** m, m)
    # Corrections from z B1(v-log(1+delta))+z² B2+z³ B3.
    for key, value in { (2, 0): B1, (3, 1): B1 + Q(1, 48),
                        (4, 2): Q(1, 96), (4, 0): B2,
                        (5, 3): -Q(1, 288), (5, 1): 2 * B2,
                        (6, 4): Q(1, 576), (6, 2): B2,
                        (6, 0): B3 }.items():
        exponent[key] = exponent.get(key, Q(0)) + value
    term, series = {(0, 0): Q(1)}, {(0, 0): Q(1)}
    for k in range(1, 7):
        term = multiply(term, exponent)
        for key, value in term.items():
            series[key] = series.get(key, Q(0)) + value / factorial(k)
    gaussian = [Q(0)] * 7
    for (order, degree), coefficient in series.items():
        if degree % 2 == 0:
            moment = 1
            for odd in range(1, degree, 2):
                moment *= odd
            gaussian[order] += coefficient * (-2 / D) ** (degree // 2) * moment
    if any(gaussian[order] for order in (1, 3, 5)):
        raise RuntimeError('odd Gaussian coefficient did not vanish')
    return [gaussian[order] for order in (0, 2, 4, 6)]
