"""Closed rational coefficients of canonical inverse-Gamma polynomials.

r(k,b,c) = k! [y**k z**b w**c] F(y,z,w).
This implementation uses only rational arithmetic, not polynomial reduction.
"""
from fractions import Fraction
from math import comb, factorial, prod


def r(k: int, b: int, c: int) -> Fraction:
    """Return a normalized coefficient, with all support restrictions enforced."""
    if any(not isinstance(n, int) or n < 0 for n in (k, b, c)):
        raise ValueError("k, b and c must be nonnegative integers")
    if (k+c) % 2 or c == 1 or (c == 0 and b == 1):
        return Fraction(0)
    if c == 0:
        if b == 0:
            return -Fraction(1, (k-1)*(k+1))
        value = sum((Fraction(comb(b-2,j)*3**j,
                    prod(k+1+2*j+2*h for h in range(3)))
                    for j in range(b-1)), Fraction(0))
        return value * Fraction(24, factorial(b)*24**b)
    value = sum((Fraction(comb(b,j)*3**j*comb(c-2,l),
                  prod(k+c-1+2*j+2*l+2*h for h in range(4)))
                  for j in range(b+1) for l in range(c-1)), Fraction(0))
    return value * Fraction(-12, factorial(b)*factorial(c)*24**b*48**c)


def coefficient(a: int, k: int, b: int, c: int) -> Fraction:
    """Coefficient of u0**a u1**k u2**b u3**c in N(A_m), m=a+2k+3b+4c."""
    if not isinstance(a, int) or a < 0:
        raise ValueError("a must be a nonnegative integer")
    m = a + 2*k + 3*b + 4*c
    return r(k,b,c)*Fraction(factorial(m), factorial(a)*2**k*factorial(k))
