#!/usr/bin/env python3
"""Exact rational certificate for the cubic discriminant. Python 3, standard library."""
from fractions import Fraction as F
from math import prod


def rising(a, k):
    return prod(a + j for j in range(k))


def moment_interval(n, epsilon):
    # 1-y <= exp(-y) <= 1-y+y^2/2, integrated against Gamma(n+1/2,1).
    p = n + F(1, 2)
    lower = 1 - epsilon * rising(p, 3)
    upper = lower + epsilon**2 * rising(p, 6) / 2
    return lower, upper


def difference_of_products(a, b, c, d):
    # The four input intervals have positive lower bounds.
    assert min(a[0], b[0], c[0], d[0]) > 0
    return a[0]*b[0] - c[1]*d[1], a[1]*b[1] - c[0]*d[0]


def main():
    eps = F(1, 10**8)
    a, b, c, d = [moment_interval(n, eps) for n in range(4)]
    t1 = difference_of_products(b, b, a, c)
    t2 = difference_of_products(c, c, b, d)
    u = difference_of_products(b, c, a, d)
    assert min(t1[0], t2[0], u[0]) > 0
    # Discriminant of a + 3 b z + 3 c z^2 + d z^3 is 27 (4 t1 t2 - u^2).
    lower = 27*(4*t1[0]*t2[0] - u[1]**2) / eps**2
    upper = 27*(4*t1[1]*t2[1] - u[0]**2) / eps**2
    assert F(-975) < lower < upper < F(-969)
    print("For epsilon = 1/10^8, exact Fraction inequalities give")
    print("-975 < discriminant / epsilon^2 < -969.")
    print("The cubic has one real root and a nonreal conjugate pair.")


if __name__ == "__main__":
    main()
