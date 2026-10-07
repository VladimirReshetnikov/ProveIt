"""Exact minimum-length composition counts (Report189); Python standard library.

The empty composition contributes a_s(0)=1 for every s; b_s(0)=0.
No floating arithmetic, network, output, or third-party imports occur here.
"""
from math import comb, isqrt


def nonnegative_integer(value, name):
    if type(value) is not int or value < 0:
        raise ValueError(name + ' must be a nonnegative integer (not bool)')
    return value


def a_count(n, s=0):
    """Stars-and-bars sum for parts >= k+s, including the empty composition."""
    nonnegative_integer(n, 'n')
    nonnegative_integer(s, 's')
    if n == 0:
        return 1
    return sum(comb(n - k * (k + s) + k - 1, k - 1)
               for k in range(1, isqrt(n) + 1) if k * (k + s) <= n)


def b_count(n, s=0):
    """Binomial difference for minimum exactly k+s; k=0 never contributes."""
    nonnegative_integer(n, 'n')
    nonnegative_integer(s, 's')
    result = 0
    for k in range(1, isqrt(n) + 1):
        residual = n - k * (k + s)
        if residual >= 0:
            result += comb(residual + k - 1, k - 1)
            if residual >= k:
                result -= comb(residual - 1, k - 1)
    return result


def a_gf_coefficients(limit, s=0):
    """Multiply geometric series, independently of the binomial formula."""
    nonnegative_integer(limit, 'limit')
    nonnegative_integer(s, 's')
    result, denominator = [1] + [0] * limit, [1] + [0] * limit
    for k in range(1, isqrt(limit) + 1):
        # One extra multiplication by 1/(1-q) in each row.
        for n in range(1, limit + 1):
            denominator[n] += denominator[n - 1]
        shift = k * (k + s)
        for n in range(shift, limit + 1):
            result[n] += denominator[n - shift]
    return result


def b_gf_coefficients(limit, s=0):
    """Multiply q^(k(k+s)) (1+...+q^(k-1))/(1-q)^(k-1)."""
    nonnegative_integer(limit, 'limit')
    nonnegative_integer(s, 's')
    result, denominator = [0] * (limit + 1), [1] + [0] * limit
    for k in range(1, isqrt(limit) + 1):
        shift = k * (k + s)
        for h in range(k):
            for n in range(shift + h, limit + 1):
                result[n] += denominator[n - shift - h]
        for n in range(1, limit + 1):
            denominator[n] += denominator[n - 1]
    return result
