#!/usr/bin/env python3
"""Exact shifted Catalan Hankel polynomials, using only the Python standard library.

D_N^(m)(a,b) = det(a*C_(i+j+m) + b*C_(i+j+m+1))_(0<=i,j<N).
An empty determinant is 1. Polynomial coefficient lists use ascending order.
"""
from __future__ import annotations

from fractions import Fraction
from functools import lru_cache
from math import comb, factorial
from typing import Sequence


def require_nonnegative(**values: int) -> None:
    for name, value in values.items():
        if not isinstance(value, int) or isinstance(value, bool) or value < 0:
            raise ValueError(f"{name} must be a nonnegative integer")


@lru_cache(maxsize=None)
def catalan(n: int) -> int:
    require_nonnegative(n=n)
    return comb(2*n, n)//(n+1)


def bareiss(matrix: Sequence[Sequence[int]]) -> int:
    """Fraction-free determinant with exact pivoting; no floating-point arithmetic."""
    n = len(matrix)
    if any(len(row) != n for row in matrix):
        raise ValueError("matrix must be square")
    if n == 0:
        return 1
    a = [list(row) for row in matrix]
    previous, sign = 1, 1
    for k in range(n-1):
        if a[k][k] == 0:
            pivot_row = next((i for i in range(k+1, n) if a[i][k]), None)
            if pivot_row is None:
                return 0
            a[k], a[pivot_row] = a[pivot_row], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k+1, n):
            for j in range(k+1, n):
                numerator = pivot*a[i][j] - a[i][k]*a[k][j]
                value, rem = divmod(numerator, previous)
                if rem:
                    raise ArithmeticError("non-exact Bareiss division")
                a[i][j] = value
            a[i][k] = 0
        previous = pivot
    return sign*a[-1][-1]


@lru_cache(maxsize=None)
def shifted_catalan_hankel(N: int, m: int) -> int:
    """H_N^(m) = product_(1<=j<=i<m) (2N+i+j)/(i+j)."""
    require_nonnegative(N=N, m=m)
    value = Fraction(1)
    for i in range(1, m):
        for j in range(1, i+1):
            value *= Fraction(2*N+i+j, i+j)
    if value.denominator != 1:
        raise ArithmeticError("shifted Hankel product is not integral")
    return value.numerator


@lru_cache(maxsize=None)
def coefficients(N: int, m: int) -> tuple[int, ...]:
    """Return [a^k b^(N-k)] D_N^(m), k=0,...,N, in O(N+m^2) operations."""
    require_nonnegative(N=N, m=m)
    value = shifted_catalan_hankel(N, m+1)
    result = [value]
    for k in range(N):
        numerator = value*(N-k)*(N+m+1+k)
        denominator = 2*(k+1)*(2*m+2*k+1)
        value, rem = divmod(numerator, denominator)
        if rem:
            raise ArithmeticError("coefficient update is not integral")
        result.append(value)
    return tuple(result)


def hankel_formula(N: int, m: int, a: int, b: int) -> int:
    """Evaluate the homogeneous coefficient formula, including a=0 or b=0."""
    c = coefficients(N, m)
    total = c[-1]
    b_power = 1
    for k in range(N-1, -1, -1):
        b_power *= b
        total = a*total + c[k]*b_power
    return total


def hankel_direct(N: int, m: int, a: int, b: int) -> int:
    require_nonnegative(N=N, m=m)
    return bareiss([[a*catalan(i+j+m) + b*catalan(i+j+m+1)
                     for j in range(N)] for i in range(N)])


def poly_mul(a: Sequence, b: Sequence) -> list:
    out = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return out


def poly_eval(c: Sequence, x):
    out = 0
    for value in reversed(c):
        out = out*x + value
    return out


def denominator_coefficients(m: int, a: int, b: int) -> list[int]:
    require_nonnegative(m=m)
    out = [1]
    for _ in range(m*(m-1)//2+1):
        out = poly_mul(out, [1, -a-2*b, b*b])
    return out


def generating_function(m: int, a: int, b: int) -> tuple[list[int], list[int]]:
    """Return P,Q with F=P/Q and Q=(1-(a+2b)t+b^2*t^2)^(binom(m,2)+1).

    The representation is not reduced at exceptional parameters. Trailing zero
    coefficients are deliberately retained to expose the uniform degree bounds.
    """
    q = denominator_coefficients(m, a, b)
    K = (m-1)**2
    values = [hankel_formula(N, m, a, b) for N in range(K+1)]
    p = [sum(q[j]*values[k-j] for j in range(min(k, len(q)-1)+1))
         for k in range(K+1)]
    return p, q


def R(n: int, y):
    """Reversed Catalan orthogonal polynomial, extended to all integer indices."""
    if n < 0:
        n = -n-1
    if n == 0:
        return 1
    u, v = 1, y+1
    for _ in range(1, n):
        u, v = v, (y+2)*v-u
    return v


def polynomial_binomial(x: int, k: int) -> int:
    """Generalized binomial for integer x and nonnegative k."""
    require_nonnegative(k=k)
    if x >= 0:
        return comb(x, k) if x >= k else 0
    return (-1)**k*comb(k-x-1, k)


def minor(N: int, m: int, ell: int) -> int:
    require_nonnegative(m=m, ell=ell)
    if ell > m:
        raise ValueError("ell must not exceed m")
    cols = [j for j in range(m+1) if j != ell]
    return bareiss([[polynomial_binomial(N+j+i, 2*i) for j in cols]
                    for i in range(m)])


def small_determinant_formula(N: int, m: int, a: int, b: int) -> Fraction:
    require_nonnegative(N=N, m=m)
    if a == 0 or b == 0:
        raise ValueError("this representation requires a*b != 0")
    y = Fraction(a, b)
    result = sum((-1)**(m+ell)*minor(N, m, ell)*R(N+ell, y)
                 for ell in range(m+1))
    return b**N*result/y**m


def leading_constant(m: int) -> Fraction:
    require_nonnegative(m=m)
    out = Fraction(1)
    for i in range(1, m):
        for j in range(1, i+1):
            out *= Fraction(2, i+j)
    return out


def barry_printed_coefficient(n: int, k: int, s: int) -> Fraction:
    """The long formula in Barry (2020), Conjecture 2, exactly as printed.

    Its value is the coefficient for shift s-1, not shift s.
    Only the non-ambiguous domain n>=0, s>=2, 0<=k<=n+1 is supported.
    """
    require_nonnegative(n=n, k=k, s=s)
    if s < 2 or k > n+1:
        raise ValueError("require s>=2 and k<=n+1")
    value = Fraction(catalan(s)*comb(s+k-2, s-2)
                     *comb(n+k+2*s-2, 2*k+2*s-3), 2*s-2)
    for j in range((s-1)//2):
        value *= Fraction(comb(2*n+2*s-2*j-1, 2*s-4*j-5),
                          comb(2*s-2*j-1, 2*s-4*j-5))
    for j in range(s-2):
        value *= Fraction(2*s-j-2, n+k+2*s-j-2)
    return value


def minimal_denominator(m: int, a: int, b: int) -> list[int]:
    """Reduced denominator over characteristic zero, for numerical integer a,b."""
    require_nonnegative(m=m)
    d = m*(m-1)//2
    if a == b == 0:
        return [1]
    if b == 0:
        base, exponent = [1, -a], d+1
    elif a == 0:
        base, exponent = [1, -b], m*(m+1)//2+1
    elif a == -4*b:
        base, exponent = [1, b], d+2
    else:
        return denominator_coefficients(m, a, b)
    out = [1]
    for _ in range(exponent):
        out = poly_mul(out, base)
    return out


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('N', type=int, help='determinant size')
    parser.add_argument('m', type=int, help='Catalan shift')
    parser.add_argument('--a', type=int, default=1)
    parser.add_argument('--b', type=int, default=1)
    parser.add_argument('--direct', action='store_true', help='also compute Bareiss determinant')
    args = parser.parse_args()
    print(hankel_formula(args.N, args.m, args.a, args.b))
    if args.direct:
        direct = hankel_direct(args.N, args.m, args.a, args.b)
        print('direct:', direct)
        assert direct == hankel_formula(args.N, args.m, args.a, args.b)
