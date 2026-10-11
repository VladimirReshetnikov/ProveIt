"""Exact diagnostics for the all-order source-to-retained normalization.

The article proves the identities for arbitrary a. This script compares
three independently written finite constructions for a=1,...,5 and
b=2*a,2*a+1. These examples are regression checks, not the proof.
All arithmetic is rational/integer; SymPy supplies Bernoulli numbers
and exact determinants.
"""
from __future__ import annotations

from fractions import Fraction as Q
import json
import math
from pathlib import Path
import sympy as sp


def factorial(n):
    return math.factorial(n)


def falling(x, n):
    return math.prod(x-r for r in range(n))


def bernoulli_even(j):
    assert j >= 0
    value = sp.bernoulli(2*j)
    return Q(int(sp.numer(value)), int(sp.denom(value)))


def mu(j):
    return Q(0) if j < 0 else bernoulli_even(j)/factorial(2*j)


def pade_coefficient(n, t):
    return Q(2*factorial(2*n+2*t+1)*factorial(2*n+1),
             factorial(4*n+2)*factorial(2*n-2*t+1)*factorial(2*t))


def h(n):
    return Q(factorial(2*n+1)**2, factorial(4*n+2)*factorial(4*n+3))


def c(n):
    return Q((2*n+1)*factorial(2*n+2), factorial(4*n+2))


def F(n, ell):
    return Q(math.prod((2*n-r)*(2*n+3+r) for r in range(2*ell)),
             factorial(2*ell+1))


def newton(n, i, order):
    def g(y):
        return (2*n+2-y)*falling(4*n+2-y, 2*i)
    coefficient = Q(sum((-1)**(order-r)*math.comb(order, r)*g(r)
                        for r in range(order+1)), factorial(order))
    assert coefficient.denominator == 1
    return coefficient.numerator


def matrix_entry(a, b, i, k):
    index = i+k-a+1
    if index < 0:
        return Q(0)
    value = Q(0)
    for upper, lower in ((2*i+2, 2*a-2*k),
                         (2*b+2*i-2*a+2, 2*b-2*k)):
        if 2 <= lower <= upper:
            value += Q(math.comb(upper, lower), upper)
    return bernoulli_even(index)*value


def retained_entry(a, b, i, k):
    n = b-a+i
    return sum((pade_coefficient(n, t)*mu(t+k-a+1)*
                (1+Q(factorial(2*t+1)*factorial(2*b-2*k),
                     factorial(2*a-2*k)*factorial(2*b+2*t-2*a+1)))
                for t in range(n+1)), Q(0))


def normalized_entry(a, b, i, ell):
    n = b-a+i
    N = 2*(n-ell)+1
    R = 2*b-2*a+2+2*ell
    prefactor = Q(factorial(R), (2*n+1)*(2*n+2)*factorial(2*ell+2)*factorial(N))
    correction = sum((newton(n, i, 2*k+1)*falling(N, 2*k+1)*
                      2*bernoulli_even(b-(a-i+ell+k))
                      for k in range(i+1)), Q(0))
    return 2*F(n, ell)+prefactor*correction


def run_case(a, b):
    assert b >= 2*a
    M = sp.Matrix(b, b, lambda i, k: matrix_entry(a, b, i, k))
    H = sp.Matrix(b, b, lambda i, k: mu(i+k-a+1))
    A = sp.Matrix(a, a, lambda i, ell: normalized_entry(a, b, i, ell))
    Fmatrix = sp.Matrix(a, a, lambda i, ell: F(b-a+i, ell))
    retained_checks = 0
    for i in range(a):
        n = b-a+i
        for ell in range(a):
            assert A[i, ell] == retained_entry(a, b, i, a-1-ell)/c(n)
            assert sum((pade_coefficient(n, t)*mu(t-ell)
                        for t in range(n+1)), Q(0)) == c(n)*F(n, ell)
            retained_checks += 1
    pade_checks = 0
    for n in range(b):
        for j in range(n+1):
            value = sum((pade_coefficient(n, t)*mu(t+j+1)
                         for t in range(n+1)), Q(0))
            assert value == (h(n) if j == n else 0)
            pade_checks += 1
    base_scalar = ((-1)**(a*(b-a)+a*(a-1)//2)*
                   math.prod(h(n) for n in range(b-a))*
                   math.prod(c(b-a+i) for i in range(a)))
    factorial_scalar = Q(math.prod(factorial(2*b+2*t-2*a+1) for t in range(b)),
                         math.prod(factorial(2*b-2*k) for k in range(b)))
    det_M, det_H, det_A, det_F = (matrix.det(method='domain-ge')
                                 for matrix in (M, H, A, Fmatrix))
    assert det_M == base_scalar*factorial_scalar*det_A
    assert det_H == base_scalar*det_F
    assert det_F > 0
    return {'a': a, 'b': b, 'retained_entry_comparisons': retained_checks,
            'Pade_orthogonality_comparisons': pade_checks,
            'exact_source_multiplier_verified': True,
            'exact_base_multiplier_verified': True,
            'base_det_F_positive': True}


def main():
    cases = [run_case(a, b) for a in range(1, 6) for b in (2*a, 2*a+1)]
    output = {'all_exact_checks_passed': True,
              'finite_examples_are_not_the_arbitrary_a_proof': True,
              'cases': cases}
    path = Path(__file__).with_name('general_normalization_checks.json')
    path.write_text(json.dumps(output, indent=2)+'\n')
    print(f'All {len(cases)} exact source/base determinant comparisons passed.')


if __name__ == '__main__':
    main()
