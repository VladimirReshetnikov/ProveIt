#!/usr/bin/env python3
"""Exact rational coefficients for a fixed sector (optional SymPy dependency).

T_m(n) = C_m n^((3-m)/2) a_m^n sum_j c[m,j] n^(-j).
This is a finite algebraic replay of the report's coefficient formula, not a
standalone proof of the asymptotic expansion or its remainder bounds.
"""
from __future__ import annotations

import argparse
from functools import lru_cache
import math
import sys

try:
    import sympy as s
except ImportError as exc:
    raise SystemExit("Optional analytic replay requires SymPy; the default exact suite does not.") from exc

y, z, k, j = s.symbols("y z k j")


def integer(value, name, minimum):
    if type(value) is not int or value < minimum:
        raise ValueError(f"{name} must be an integer >= {minimum}; booleans are excluded")
    return value


def f_coefficients(order):
    integer(order, "order", 0)
    return _f_coefficients(order)


@lru_cache(maxsize=None)
def _f_coefficients(order):
    homogeneous = [s.Integer(1)]
    powers = [None] + [s.summation(j**q, (j, 1, k)) for q in range(1, order+1)]
    for ell in range(1, order+1):
        homogeneous.append(s.expand(sum(powers[q]*homogeneous[ell-q]
                                        for q in range(1, ell+1))/ell))
    euler_derivatives = [1/(1-y)]
    for degree in range(1, 2*order+1):
        euler_derivatives.append(s.factor(y*s.diff(euler_derivatives[-1], y)))
    result = []
    for ell in range(order+1):
        polynomial = s.Poly(homogeneous[ell], k)
        result.append(s.factor((-1)**ell*sum(coefficient*euler_derivatives[degree[0]]
                                            for degree, coefficient in polynomial.terms())))
    return tuple(result)


def truncate(expression, order):
    integer(order, "order", 0)
    return s.series(expression, z, 0, order+1).removeO().expand()


def coefficients(m, order):
    integer(m, "m", 1)
    integer(order, "order", 0)
    f = f_coefficients(order)
    # Coefficients of F^m, by finite truncated convolution.
    A = [s.Integer(1)] + [s.Integer(0)]*order
    for unused in range(m):
        A = [s.factor(sum(A[i]*f[ell-i] for i in range(ell+1)))
             for ell in range(order+1)]
    harmonic = s.harmonic(m)
    B = [s.factor(A[ell]-(harmonic/y*A[ell-1] if ell else 0))
         for ell in range(order+1)]
    center = s.Rational(m, m+1)
    moments = []
    for degree in range(2*order+1):
        moment = 0
        for p in range(degree+1):
            raw = s.prod(m+(i+2)*z for i in range(p))/s.Integer(m+1)**p
            moment += s.binomial(degree, p)*(-center)**(degree-p)*raw
        moments.append(s.expand(moment))
    expectation = 0
    for ell in range(order+1):
        derivative = B[ell]
        for degree in range(2*(order-ell)+1):
            if degree:
                derivative = s.diff(derivative, y)
            value = s.cancel(derivative).subs(y, center)/math.factorial(degree)
            expectation += z**ell*value*moments[degree]
    expectation = truncate(expectation, order)
    log_correction = 0
    for q in range(1, (order+1)//2+1):
        degree = 2*q-1
        log_correction += (s.bernoulli(2*q)/s.Integer(2*q*(2*q-1)) *
                           (s.Rational(1, m**degree)-m)*z**degree)
    stirling = truncate((1+z/m)*s.exp(log_correction), order)
    answer = truncate(stirling*expectation/s.Integer(m+1)**m, order)
    return [s.factor(answer.coeff(z, degree)) for degree in range(order+1)]


def kappa(m):
    integer(m, "m", 1)
    return (s.Rational(23*m, 12) + s.Rational(13, 12*m)
            - s.Rational(m*m*(m+1), 2) - s.Rational(m+1, m)*s.harmonic(m))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--order", type=int, default=3)
    parser.add_argument("--m", type=int, nargs="+", default=[1, 2, 3])
    args = parser.parse_args()
    try:
        integer(args.order, "order", 0)
        for m in args.m:
            integer(m, "m", 1)
        for m in args.m:
            print(f"m = {m}: {coefficients(m, args.order)}", flush=True)
    except ValueError as exc:
        parser.error(str(exc))
    return 0


if __name__ == "__main__":
    sys.exit(main())
