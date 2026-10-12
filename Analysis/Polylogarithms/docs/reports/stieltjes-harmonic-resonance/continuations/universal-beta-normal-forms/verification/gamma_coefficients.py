"""Exact coefficients in the functional normal form of the inverse-Gamma hierarchy.

Only Python's standard library is required. Coefficients are fractions.Fraction.
This algorithm implements the polynomial beta formula, NOT integration by parts.
An exponent tuple e represents product(u_j**e[j]); trailing zeroes are optional.
"""
from __future__ import annotations
from fractions import Fraction
from functools import lru_cache
from math import comb, factorial, prod
from typing import Iterable
F = Fraction
Exponents = tuple[int, ...]
Polynomial = tuple[Fraction, ...]


def canonical(exponents: Iterable[int]) -> Exponents:
    e = tuple(exponents)
    if any(not isinstance(x, int) or x < 0 for x in e):
        raise ValueError("Exponents must be nonnegative integers.")
    while e and e[-1] == 0:
        e = e[:-1]
    return e


def multiply(p: Polynomial, q: Polynomial) -> Polynomial:
    out = [F(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                if b:
                    out[i + j] += a * b
    return tuple(out)


@lru_cache(maxsize=None)
def power(p: Polynomial, n: int) -> Polynomial:
    if n < 0:
        raise ValueError("Polynomial powers must be nonnegative.")
    if n == 0:
        return (F(1),)
    half = power(p, n // 2)
    square = multiply(half, half)
    return multiply(square, p) if n % 2 else square


@lru_cache(maxsize=None)
def theta(j: int) -> Polynomial:
    """Theta_j(v)=((v+1)^(j+1)-(v-1)^(j+1))/(2^(j+1)(j+1)!)."""
    if j < 1:
        raise ValueError("j must be positive.")
    den = 2 ** (j + 1) * factorial(j + 1)
    return tuple(F(comb(j + 1, k) * (1 - (-1) ** (j + 1 - k)), den)
                 for k in range(j + 1))


@lru_cache(maxsize=None)
def _coefficient(e: Exponents) -> Fraction:
    if len(e) <= 1:
        return F(1)
    d = len(e) - 1
    if e[d] == 1:
        return F(0)
    if sum(j * e[j] for j in range(1, d + 1)) % 2:
        return F(0)
    m = sum((j + 1) * e[j] for j in range(d + 1))
    powers = list(e); powers[d] -= 2
    integrand = power((F(1), F(0), F(-1)), d)
    for j in range(1, d + 1):
        if powers[j]:
            integrand = multiply(integrand, power(theta(j), powers[j]))
    # One HALF of the integral on [-1,1].
    half_integral = sum((a / (k + 1) for k, a in enumerate(integrand)
                         if k % 2 == 0), F(0))
    den = 2 ** (2*d) * factorial(d) * factorial(d+1) * prod(factorial(x) for x in e)
    return F((-1) ** d * factorial(m), den) * half_integral


def coefficient(exponents: Iterable[int], weight: int | None = None) -> Fraction:
    """Return [u**exponents] N_weight; infer weight when omitted."""
    e = canonical(exponents)
    m = sum((j + 1) * x for j, x in enumerate(e))
    if weight is not None and weight != m:
        return F(0)
    return _coefficient(e)


def mixed_square(a: int, k: int, b: int, r: int) -> Fraction:
    """Finite sum for [u0^a u1^k u2^b ur^2] N_m, r>=3."""
    if min(a, k, b) < 0 or r < 3:
        raise ValueError("Require a,k,b>=0 and r>=3.")
    if k % 2:
        return F(0)
    m = a + 2*k + 3*b + 2*r + 2
    total = sum((F(comb(b,j)*3**j, prod(k+2*j+2*l+1 for l in range(r+1)))
                 for j in range(b+1)), F(0))
    den = factorial(a)*2**(k+r+1)*factorial(k)*factorial(r+1)*factorial(b)*24**b
    return F((-1)**r*factorial(m), den)*total


if __name__ == "__main__":
    for e in [(0,0,1,2),(0,1,0,3),(0,0,2,2)]:
        print(e, coefficient(e))
