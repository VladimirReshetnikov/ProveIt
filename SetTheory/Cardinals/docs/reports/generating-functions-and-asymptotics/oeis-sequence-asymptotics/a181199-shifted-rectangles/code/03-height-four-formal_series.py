#!/usr/bin/env python3
"""Exact truncated formal power series; Python standard library only.

Coefficients are fractions and lists represent powers x**0 through x**(N-1).
All checks use explicit exceptions, including under python -O.
"""
from fractions import Fraction as F
from math import comb


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def series(values, length):
    return [F(values[i]) if i < len(values) else F(0) for i in range(length)]


def add(a, b):
    require(len(a) == len(b), "series lengths differ")
    return [x + y for x, y in zip(a, b)]


def scale(a, c):
    return [F(c) * x for x in a]


def mul(a, b):
    require(len(a) == len(b), "series lengths differ")
    length = len(a)
    return [sum((a[j] * b[k-j] for j in range(k+1)), F(0))
            for k in range(length)]


def reciprocal(a):
    require(bool(a) and a[0] != 0, "series has no multiplicative inverse")
    out = [1 / a[0]] + [F(0)] * (len(a)-1)
    for k in range(1, len(a)):
        out[k] = -sum((a[j] * out[k-j] for j in range(1, k+1)), F(0)) / a[0]
    return out


def div(a, b):
    return mul(a, reciprocal(b))


def power(a, exponent):
    require(isinstance(exponent, int) and exponent >= 0,
            "power exponent must be a nonnegative integer")
    out = series([1], len(a))
    while exponent:
        if exponent & 1:
            out = mul(out, a)
        a = mul(a, a)
        exponent //= 2
    return out


def compose(a, b):
    require(len(a) == len(b) and b[0] == 0,
            "formal composition requires equal lengths and zero inner constant")
    out = series([], len(a))
    for coefficient in reversed(a):
        out = mul(out, b)
        out[0] += coefficient
    return out


def exponential(a):
    require(a[0] == 0, "formal exponential requires zero constant")
    out = series([1], len(a))
    for k in range(1, len(a)):
        out[k] = sum((j * a[j] * out[k-j] for j in range(1, k+1)), F(0)) / k
    return out


def bernoulli(count):
    """B_0 through B_count, using the convention B_1=-1/2."""
    out = [F(1)]
    for m in range(1, count+1):
        out.append(-sum((comb(m+1, j) * out[j] for j in range(m)), F(0)) / (m+1))
    return out


def asymptotic_data(order=12):
    require(order >= 12, "at least six relative correction terms are required")
    length = order + 1
    one = series([1], length)
    factor = lambda a: series(a, length)
    # x=1/n; all negative powers have been canceled exactly.
    rn = scale(mul(power(factor([1, 1]), 2), factor([4, -1])), -1)
    rd = scale(mul(mul(factor([1, -1]), factor([3, 1])),
                   mul(factor([3, 2]), factor([4, 3]))), 3)
    sn = factor([0]*6 + [7, 0, -1])
    sd = scale(mul(mul(mul(factor([1, -1]), factor([3, 1])),
                       mul(factor([3, 2]), factor([4, 3]))),
                   mul(power(factor([2, -1]), 2), power(factor([2, 1]), 2))), 4)
    r, s = div(rn, rd), div(sn, sd)
    require(r[0] == -F(1, 27), "incorrect limiting multiplier R")
    shift = div(factor([0, 1]), factor([1, 1]))
    b = series([], length)
    # The coefficient of b_k is 1-R(0)=28/27, so the formal solution is unique.
    for k in range(length):
        rhs_known = add(mul(r, b), s)
        lhs_known = compose(b, shift)
        b[k] = (rhs_known[k] - lhs_known[k]) / (1-r[0])
    residual = add(compose(b, shift), scale(add(mul(r, b), s), -1))
    require(all(v == 0 for v in residual), "formal recurrence residual is not zero")
    require(all(v == 0 for v in b[:6]) and b[6] == F(3, 1024),
            "incorrect leading b_n coefficient")
    # Independently check the shift formula [x^k](x/(1+x))^j.
    shift_binomial = [b[0]] + [sum((b[j] * (-1)**(k-j) * comb(k-1, k-j)
                                      for j in range(1, k+1)), F(0))
                                  for k in range(1, length)]
    require(shift_binomial == compose(b, shift), "binomial shift cross-check failed")
    relative_order = order-6
    numbers = bernoulli(relative_order+1)
    log_m = series([], relative_order+1)
    for degree in range(1, relative_order+1, 2):
        k2 = degree+1
        log_m[degree] = numbers[k2] * (F(1, 4**degree)-4) / (k2*degree)
    stirling = exponential(log_m)
    normalized_b = [x/b[6] for x in b[6:]]
    final = mul(normalized_b, stirling)
    require(log_m[1] == -F(5, 16), "Stirling first correction failed")
    # Formal exponential is checked by M'=L'M, without transcendental arithmetic.
    for k in range(1, len(stirling)):
        require(k*stirling[k] == sum((j*log_m[j]*stirling[k-j]
                                     for j in range(1, k+1)), F(0)),
                "Stirling exponential differential identity failed")
    return {
        "variable": "x=1/n",
        "b_definition": "b_n=a_n/M_n; M_n=(4n)!/(n!)^4",
        "R_at_infinity": str(r[0]),
        "R_series_coefficients": [str(x) for x in r],
        "S_series_coefficients": [str(x) for x in s],
        "b_coefficients": {str(k): str(b[k]) for k in range(length)},
        "recurrence_residual_coefficients": [str(x) for x in residual],
        "stirling_log_relative_coefficients": [str(x) for x in log_m],
        "stirling_relative_coefficients": [str(x) for x in stirling],
        "a_relative_coefficients": [str(x) for x in final],
        "a_leading_form": "3*256^n/(1024*sqrt(2)*pi^(3/2)*n^(15/2))",
        "scope": "Exact formal coefficients; the analytic remainder argument is in the manuscript."
    }


if __name__ == "__main__":
    import json
    print(json.dumps(asymptotic_data(), indent=2, sort_keys=True))
