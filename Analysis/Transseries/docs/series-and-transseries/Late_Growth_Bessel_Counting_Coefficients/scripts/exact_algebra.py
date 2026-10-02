#!/usr/bin/env python3
"""Finite formal coefficient algebra over Q; no asymptotic remainder claims.

All lists hold ordinary-power coefficients, starting with degree zero.
Gaussian polynomials are dictionaries {degree: Fraction}.
"""
from fractions import Fraction as Q
from math import comb, factorial


def rising(x, n):
    result = Q(1)
    for k in range(n):
        result *= x + k
    return result


def binomial(x, n):
    result = Q(1)
    for k in range(n):
        result *= (x - k) / (k + 1)
    return result


def bernoulli_numbers(n):
    """B1=-1/2 convention; entirely rational recurrence."""
    b = [Q(1)]
    for m in range(1, n + 1):
        b.append(-sum(Q(comb(m + 1, k)) * b[k]
                      for k in range(m)) / (m + 1))
    return b


def bernoulli_polynomial(n, x, b):
    return sum(Q(comb(n, k)) * b[k] * x ** (n - k)
               for k in range(n + 1))


def convolve(a, b, n):
    result = [Q(0) for _ in range(n + 1)]
    for i, x in enumerate(a[:n + 1]):
        for j, y in enumerate(b[:n + 1 - i]):
            result[i + j] += x * y
    return result


def exp_series(logarithm, n):
    assert logarithm[0] == 0
    result = [Q(1)]
    for j in range(1, n + 1):
        result.append(sum(k * logarithm[k] * result[j - k]
                          for k in range(1, j + 1)) / j)
    return result


def poly_add_product(destination, left, right, scale=Q(1)):
    for i, x in left.items():
        for j, y in right.items():
            destination[i + j] = destination.get(i + j, Q(0)) + scale * x * y


def gaussian_coefficients(n, mixed=False):
    """Exact t^0,...,t^n coefficients of the stated formal saddle transform.

    Pure: e^2 E[e^(2u) f(u)] has moments M0=1, M1=-2,
    M_p=-2 M_(p-1)-(p-1)M_(p-2), u=iV, V standard Gaussian.
    Mixed: E[f(iV)] has M1=0 and lacks the square-root phase.
    """
    a = [rising(Q(1, 2), k) ** 2 / (factorial(k) * 4 ** k)
         for k in range(n + 1)]
    h = [sum(a[k] * a[j - k] * ((-1) ** (j - k) if mixed else 1)
             for k in range(j + 1)) for j in range(n + 1)]
    r = [{}]
    for m in range(1, n + 1):
        p = {m + 2: Q((-1) ** m, m + 2)}
        if not mixed:
            p[m + 1] = 4 * binomial(Q(1, 2), m + 1)
        r.append(p)
    e = [{0: Q(1)}]
    for m in range(1, n + 1):
        p = {}
        for k in range(1, m + 1):
            poly_add_product(p, r[k], e[m - k], Q(k, m))
        e.append(p)
    mean = 0 if mixed else -2
    moments = [Q(1), Q(mean)]
    for p in range(2, 3 * n + 1):
        moments.append(mean * moments[-1] - (p - 1) * moments[-2])
    q = []
    for j in range(n + 1):
        p = {}
        for k in range(j + 1):
            for degree in range(j - k + 1):
                factor = (h[k] * (-1) ** degree
                          * rising(Q(k + 3, 2), degree) / factorial(degree))
                poly_add_product(p, {degree: factor}, e[j - k - degree])
        q.append(sum(value * moments[degree] for degree, value in p.items()))
    b = bernoulli_numbers(n + 2)
    logarithm = [Q(0) for _ in range(n + 1)]
    for k in range(1, (n + 2) // 4 + 1):
        degree = 4 * k - 2
        if degree <= n:
            logarithm[degree] = 2 * b[2 * k] / (2 * k * (2 * k - 1))
    return convolve(exp_series(logarithm, n), q, n)


def mixed_bernoulli_coefficients(n):
    """c0,...,cn from the finite Bernoulli/gamma-ratio generator.

    c_l=[x^l] sum_m ((1/2)_m)^3 x^m/(m! 4^m) exp(E_m(x)),
    E_m = sum_(k>=1) (-1)^(k+1)
          (2 B_(k+1)(1)-B_(k+1)(3/2+m)) x^k/(k(k+1)).
    Only m<=l and k<=l are ever used.
    """
    b = bernoulli_numbers(n + 1)
    c = [Q(0) for _ in range(n + 1)]
    for m in range(n + 1):
        logarithm = [Q(0)]
        for k in range(1, n - m + 1):
            logarithm.append(Q((-1) ** (k + 1), k * (k + 1)) * (
                2 * bernoulli_polynomial(k + 1, Q(1), b)
                - bernoulli_polynomial(k + 1, Q(3, 2) + m, b)))
        factor = rising(Q(1, 2), m) ** 3 / (factorial(m) * 4 ** m)
        for k, value in enumerate(exp_series(logarithm, n - m)):
            c[m + k] += factor * value
    return c


def recurrence_coefficients(n, convert=Q, validate_operator=False):
    """Formal normalized third-order recurrence in exact or mp arithmetic.

    R[D]=D(t)+sum_(s=1)^3 P_s(t)exp(E_s(t))
                  D(t/sqrt(1-s t^2))=0.
    R[t^k] has vanishing coefficients below k+4 and [t^(k+4)]=-4k.
    Hence d_n is fixed from degree n+4 and earlier d_k.
    """
    zero, one, half = convert(0), convert(1), convert(1) / 2
    limit = n + 4
    ps = {1: [-3, 0, -1, 0, 1],
          2: [3, 0, -5, 0, 1, 0, 1],
          3: [-1, 0, 6, 0, -13, 0, 12, 0, -4]}
    bs = {}
    for shift in (1, 2, 3):
        logarithm = [zero for _ in range(limit + 1)]
        for m in range(1, limit // 2 + 1):
            logarithm[2 * m] += convert(shift) ** (m + 1) / (m * (m + 1))
        choose = one
        for m in range(1, (limit + 1) // 2 + 1):
            choose *= (half - m + 1) / m
            logarithm[2 * m - 1] += 4 * choose * (-shift) ** m
        e = [one]
        for j in range(1, limit + 1):
            e.append(sum(k * logarithm[k] * e[j - k]
                         for k in range(1, j + 1)) / j)
        bs[shift] = [sum(convert(ps[shift][k]) * e[j - k]
                         for k in range(min(j + 1, len(ps[shift]))))
                     for j in range(limit + 1)]

    def coefficient(k, degree):
        gap = degree - k
        total = one if gap == 0 else zero
        for shift in (1, 2, 3):
            factor = one
            for m in range(gap // 2 + 1):
                if m:
                    factor *= (convert(k) / 2 + m - 1) * shift / m
                total += factor * bs[shift][gap - 2 * m]
        return total

    if validate_operator:
        for k in range(n + 1):
            assert all(coefficient(k, k + offset) == 0 for offset in range(4))
            assert coefficient(k, k + 4) == -4 * k
    d = [one]
    for j in range(1, n + 1):
        total = sum(d[k] * coefficient(k, j + 4) for k in range(j))
        d.append(total / (4 * j))
    return d
