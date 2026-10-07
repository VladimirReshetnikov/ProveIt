#!/usr/bin/env python3
"""Exact finite Bernoulli/Gaussian algebra; no floating arithmetic or dependencies.

coeffs(N,m)[j] is {p: (a,b)}, meaning d_(m,j)=sum_p (a+i*b)/pi**p.
The analytic justification is in Report187; finite algebra is checked here.
"""
from fractions import Fraction as Q
from math import comb, factorial
import json
import sys
sys.dont_write_bytecode = True
MAX_ORDER, MAX_MODE = 12, 1000
ZERO, ONE = (Q(0), Q(0)), (Q(1), Q(0))


def need(condition, message):
    if not condition:
        raise ValueError(message)


def integer(value, low, high, name):
    need(type(value) is int and low <= value <= high,
         name + ' must be an integer in [' + str(low) + ', ' + str(high) + ']')


def cadd(a, b):
    return a[0] + b[0], a[1] + b[1]


def cmul(a, b):
    return a[0]*b[0] - a[1]*b[1], a[0]*b[1] + a[1]*b[0]


def scale(a, b):
    return a[0]*b, a[1]*b


def ipow(n):
    return (ONE, (Q(0), Q(1)), (Q(-1), Q(0)), (Q(0), Q(-1)))[n % 4]


def addto(polynomial, degree, value):
    polynomial[degree] = cadd(polynomial.get(degree, ZERO), value)
    if polynomial[degree] == ZERO:
        del polynomial[degree]


def pmul(left, right):
    product = {}
    for j, a in left.items():
        for k, b in right.items():
            addto(product, j+k, cmul(a, b))
    return product


def bernoulli(N):
    integer(N, 0, MAX_ORDER+1, 'Bernoulli order')
    # Convention B_1=-1/2, from sum_{k=0}^{n} binom(n+1,k) B_k=0.
    values = [Q(1)]
    for n in range(1, N+1):
        values.append(-sum(Q(comb(n+1, k))*values[k] for k in range(n))/Q(n+1))
    return values


def coeffs(N, m=1):
    integer(N, 0, MAX_ORDER, 'order')
    integer(m, 1, MAX_MODE, 'mode')
    alpha = Q(1, 8*m)
    beta = Q(1, 2)-alpha
    numbers = bernoulli(N+1)

    def polynomial(n):
        return sum(Q(comb(n,k))*numbers[k]*alpha**(n-k) for k in range(n+1))

    logarithm = [{} for _ in range(N+1)]
    for j in range(1, N+1):
        addto(logarithm[j], j, (beta*Q((-1)**(j+1), j), Q(0)))
    for r in range(1, N+1):
        z = scale(ipow(-r), -Q((-1)**(r+1))*polynomial(r+1)/Q(r*(r+1)))
        for j in range(N-r+1):
            addto(logarithm[r+j], j, scale(z, Q((-1)**j*comb(r+j-1,j))))
    for r in range(2, N+2):
        addto(logarithm[r-1], r, (Q(0), Q((-1)**(r-1),r*(r-1))))
    # If H=exp(L), then n H_n=sum_{j=1}^n j L_j H_(n-j).
    series = [{0: ONE}]
    for n in range(1, N+1):
        value = {}
        for j in range(1, n+1):
            for k, z in pmul(logarithm[j], series[n-j]).items():
                addto(value, k, scale(z, Q(j,n)))
        series.append(value)
    result = []
    for polynomial in series:
        value = {}
        for k, z in polynomial.items():
            if k % 2:
                continue
            r = k//2
            moment = Q(factorial(2*r), 2**r*factorial(r)*(4*m)**r)
            addto(value, r, scale(cmul(z, ipow(-r)), moment))
        result.append(value)
    return result


def encoded(values):
    return [{str(k): [str(a), str(b)] for k, (a,b) in sorted(value.items())}
            for value in values]


def verify_reference(values):
    expected = [{0: ONE},
                {0: (Q(0),Q(11,384)), 1: (Q(-1,8),Q(0))},
                {0: (Q(-2137,294912),Q(0)), 1: (Q(0),Q(79,3072)),
                 2: (Q(3,128),Q(0))}]
    need(isinstance(values, list) and len(values) >= 3 and values[:3] == expected,
         'm=1 coefficients d0,d1,d2 differ from the independent printed formulas')


def result():
    first = coeffs(6,1)
    verify_reference(first)
    return {'status': 'PASS', 'arithmetic': 'exact fractions.Fraction',
            'meaning': 'd_(m,j)=sum_p (real+i*imaginary)*pi^(-p)',
            'coefficients_m1': encoded(first), 'coefficients_m2': encoded(coeffs(6,2)),
            'reference_formulas_checked': ['m1,d0','m1,d1','m1,d2'],
            'supported_order': [0,MAX_ORDER], 'supported_mode': [1,MAX_MODE],
            'scope': 'finite algebra, not a numerical enclosure or analytic proof'}


if __name__ == '__main__':
    print(json.dumps(result(), sort_keys=True, indent=2, allow_nan=False))
