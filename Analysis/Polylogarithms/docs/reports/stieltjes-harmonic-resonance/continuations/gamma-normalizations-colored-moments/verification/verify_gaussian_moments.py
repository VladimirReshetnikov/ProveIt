#!/usr/bin/env python3
"""Check Gamma-ensemble Gaussian moments by 1D determinant jets.

No paired Gamma-product formula is used to compute the left-hand side.
The determinant of integrals with exp(t*g(x)) is differentiated by finite
polynomial arithmetic, with all entries obtained by ordinary quadrature.
"""
from functools import lru_cache
from itertools import permutations
from pathlib import Path
import json
import mpmath as mp

mp.mp.dps = 42
OUT = (Path(__file__).resolve().parent.parent / 'evidence' / 'gaussian_moment_checks.json')
checks = []


def product(a, b, order):
    return [sum(a[j]*b[k-j] for j in range(k+1))
            for k in range(order+1)]


def polynomial_determinant(matrix, order):
    n = len(matrix)
    result = [mp.mpf(0)]*(order+1)
    for p in permutations(range(n)):
        sign = (-1)**sum(p[i] > p[j] for i in range(n)
                         for j in range(i+1, n))
        term = [mp.mpf(1)]+[mp.mpf(0)]*order
        for i in range(n):
            term = product(term, matrix[i][p[i]], order)
        result = [a+sign*b for a, b in zip(result, term)]
    return result


def verify(n, sigma):
    order = n+1
    mean_unit = mp.polygamma(1, 2*sigma)
    scale = mp.sqrt(mp.polygamma(3, 2*sigma))

    @lru_cache(maxsize=None)
    def values(x):
        weight = abs(mp.gamma(sigma+mp.j*x/2))**(4*(n+1))
        g = (2*mp.re(mp.polygamma(1, sigma+mp.j*x/2))
             - 2*mean_unit)/scale
        return weight, g

    def entry(r, k, degree):
        def f(x):
            weight, g = values(x)
            return (x**(2*r-1)*mp.sinh(mp.pi*k*x)*weight
                    *g**degree/mp.factorial(degree))
        return mp.quad(f, [0, mp.mpf("0.25"), 1, 3, 7, 15, mp.inf])

    matrix = [[[entry(r, k, degree) for degree in range(order+1)]
               for k in range(1, n+1)] for r in range(1, n+1)]
    coefficients = polynomial_determinant(matrix, order)
    for degree in range(order+1):
        lhs = coefficients[degree]*mp.factorial(degree)/coefficients[0]
        rhs = (mp.mpf(0) if degree % 2
               else mp.factorial(degree)/(2**(degree//2)
                                         *mp.factorial(degree//2)))
        error = abs(lhs-rhs)
        row = {"n": n, "sigma": str(sigma), "degree": degree,
               "quadrature_moment": mp.nstr(lhs, 42),
               "Gaussian_moment": mp.nstr(rhs, 42),
               "absolute_error": mp.nstr(error, 9)}
        checks.append(row)
        print(json.dumps(row), flush=True)
        assert error < mp.mpf("1e-29"), row
    OUT.write_text(json.dumps({"working_dps": mp.mp.dps,
                               "checks": checks}, indent=2)+"\n")


for n, sigma in [(1, mp.mpf(1)/4), (1, mp.mpf("0.7")),
                 (2, mp.mpf("0.37")), (3, mp.mpf(1)/4)]:
    verify(n, sigma)

print("All Gaussian moment diagnostics passed", flush=True)
