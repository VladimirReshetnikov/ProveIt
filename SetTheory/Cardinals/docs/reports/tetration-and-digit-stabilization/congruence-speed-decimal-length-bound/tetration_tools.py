#!/usr/bin/env python3
"""Exact arithmetic for tetration bases a == 1 (mod 10).

No power tower is constructed by the valuation functions.  The independent
modular-tower routine at the end is intended for small regression tests only.
Python 3.9+; standard library only.
"""
from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache


def valuation(n: int, p: int) -> int:
    """Return the exponent of p in nonzero n, for p in {2,5}."""
    if p not in (2, 5):
        raise ValueError("This implementation supports only p=2 or p=5.")
    if n == 0:
        raise ValueError("The valuation of zero is not a finite integer.")
    n = abs(n)
    if p == 2:
        return (n & -n).bit_length() - 1
    count = 0
    while n % p == 0:
        count += 1
        n //= p
    return count


def ceil_div(n: int, d: int) -> int:
    if d <= 0:
        raise ValueError("The denominator must be positive.")
    return -((-n) // d)


@dataclass(frozen=True)
class Profile:
    """Valuation profile. Heights refer to Delta_n = T_(n+1)-T_n."""
    alpha: int
    beta: int
    c: int

    def __post_init__(self) -> None:
        if min(self.alpha, self.beta, self.c) < 1:
            raise ValueError("All valuations must be positive.")
        if min(self.alpha, self.beta) != 1 or max(self.alpha, self.beta) < 2:
            raise ValueError("Consecutive even neighbors of an odd base required.")

    @classmethod
    def from_base(cls, a: int) -> 'Profile':
        if a <= 1 or a % 10 != 1:
            raise ValueError("The base must be >1 and congruent to 1 modulo 10.")
        return cls(valuation(a-1, 2), valuation(a+1, 2), valuation(a-1, 5))

    @property
    def sigma(self) -> int:
        return self.alpha + self.beta - 1

    @property
    def eventual_speed(self) -> int:
        return min(self.sigma, self.c)

    def stable(self, n: int) -> int:
        """Exact exponent of 10 in Delta_n, including the genuine n=0."""
        if n < 0:
            raise ValueError("Height must be nonnegative.")
        return min(self.alpha + n*self.sigma, (n+1)*self.c)

    def speed(self, b: int) -> int:
        """Raw congruence gain. Published early-digit conventions may differ."""
        if b < 1:
            raise ValueError("Speed height must be positive.")
        return self.stable(b) - self.stable(b-1)

    @property
    def onset(self) -> int:
        """Least B>=1 at which the raw gains remain constant forever."""
        if self.alpha >= 2 or self.beta <= self.c:
            return 1
        return 1 + ceil_div(self.c - 1, self.beta - self.c)


def crt_base(c: int) -> int:
    """Least positive a with a=1 mod 5^c and a=-1 mod 2^(c+1)."""
    if c < 1:
        raise ValueError("c must be positive.")
    q, m = 5**c, 1 << (c+1)
    return 1 + q*((-2*pow(q, -1, m)) % m)


def extended_gcd(a: int, b: int) -> tuple[int, int, int]:
    """Return (g,x,y) with ax+by=g=gcd(a,b), using Euclid's algorithm."""
    if a < 0 or b < 0:
        raise ValueError("Nonnegative inputs required.")
    r0, r1, x0, x1, y0, y1 = a, b, 1, 0, 0, 1
    while r1:
        k = r0 // r1
        r0, r1 = r1, r0-k*r1
        x0, x1 = x1, x0-k*x1
        y0, y1 = y1, y0-k*y1
    return r0, x0, y0


def crt_base_euclid(c: int) -> int:
    """Independent construction not using Python's modular inverse."""
    if c < 1:
        raise ValueError("c must be positive.")
    q, m = 5**c, 1 << (c+1)
    g, x, y = extended_gcd(q, m)
    if g != 1 or q*x + m*y != 1:
        raise ArithmeticError("Invalid Bezout identity.")
    return 1 + q*((-2*x) % m)


def phi_2_5_smooth(m: int) -> int:
    """Euler's phi for a positive integer with no primes except 2 and 5."""
    if m < 1:
        raise ValueError("Positive modulus required.")
    result, rest = m, m
    for p in (2, 5):
        if rest % p == 0:
            result = result // p * (p-1)
            while rest % p == 0:
                rest //= p
    if rest != 1:
        raise ValueError("Modulus has a prime factor other than 2 or 5.")
    return result


@lru_cache(maxsize=200000)
def tower_mod(a: int, h: int, m: int) -> int:
    """T_h(a) modulo m for gcd(a,10)=1 and 2,5-smooth m.

    Uses Euler reduction, not any stable-digit formula. For small tests only;
    very large h may exceed Python's recursion limit.
    """
    if a <= 1 or a % 2 == 0 or a % 5 == 0 or h < 0 or m < 1:
        raise ValueError("Invalid base, height, or modulus.")
    if m == 1:
        return 0
    if h == 0:
        return 1 % m
    ph = phi_2_5_smooth(m)
    return pow(a, tower_mod(a, h-1, ph), m)
