#!/usr/bin/env python3
"""Reproduce finite examples in the prime-power slope theorem (Python 3.11+)."""
from decimal import Decimal as D, getcontext
from fractions import Fraction
from itertools import product
from math import gcd, isqrt

getcontext().prec = 72
PI = D("3.141592653589793238462643383279502884197169399375105820974944592307816406286")
EULER = D("0.577215664901532860606512090082402431042159335939923598805767234884867726778")
LOG_2PI = (2 * PI).ln()
K0 = 2 + EULER - (4 * PI).ln()


def prime_powers(bound):
    """Yield (power, prime) with no duplicate powers."""
    for p in range(2, bound + 1):
        if any(p % d == 0 for d in range(2, isqrt(p) + 1)):
            continue
        n = p
        while n <= bound:
            yield n, p
            n *= p


def scalar_k(t):
    """Exact arithmetic formula evaluated in Decimal arithmetic.

    The elementary log expression is the closed sum of the trivial-zero
    correction. Comparing log(n) with t keeps prime-power endpoints stable.
    """
    if t < 0:
        return scalar_k(-t)
    if t == 0:
        return K0
    x = t.exp()
    u = (-t).exp()
    prime_sum = D(0)
    for n, p in prime_powers(int(x) + 1):
        if D(n).ln() <= t:
            prime_sum += D(p).ln() * (1 / D(n) - u)
    w = x.sqrt() * (1 + EULER - t + prime_sum)
    correction = ((1 + u) * (1 + u).ln() - (1 - u) * (1 - u).ln() - 2 * u) / 2
    return w - x.sqrt() * (u * LOG_2PI + correction)


def scalar_d2(t):
    return 2 * (K0 - scalar_k(t))


def derivative_jump(center, step):
    """Difference of forward and backward secant slopes of squared distance."""
    middle = scalar_d2(center)
    left = (middle - scalar_d2(center - step)) / step
    right = (scalar_d2(center + step) - middle) / step
    return left, right, right - left


def character_mod_small(x, modulus, parity):
    """Principal or nonprincipal real character at conductor 3 or 4."""
    if parity == 0:
        return 1  # primitive inducing character has conductor 1
    if gcd(x, modulus) != 1:
        return 0
    return 1 if x % modulus == 1 else -1


def coefficient_mod12(a, n):
    total = 0
    for eps3, eps4 in product(range(2), repeat=2):
        chi_a = character_mod_small(a, 3, eps3) * character_mod_small(a, 4, eps4)
        induced_n = character_mod_small(n, 3, eps3) * character_mod_small(n, 4, eps4)
        total += chi_a * induced_n
    return Fraction(total, 4)


def coefficient_crt(q, a, n, p):
    m = q
    while m % p == 0:
        m //= p
    if (a - n) % m:
        return Fraction(0)
    primary_modulus = q // m
    phi = sum(gcd(x, primary_modulus) == 1 for x in range(1, primary_modulus + 1))
    return Fraction(1, phi)


def check_examples():
    print("Scalar zeta kernel. Jump in the derivative of 2(K(0)-K(t)).")
    print("72-digit Decimal working precision. Values below are rounded.")
    print(f"K(0) = {K0:.22f}")
    for n, p in ((2, 2), (4, 2), (6, None)):
        t = D(n).ln()
        jump = -2 * D(p).ln() / D(n).sqrt() if p else D(0)
        print(f"n = {n}, predicted jump = {jump:.20f}")
        for k in (3, 6, 12, 24):
            step = D(10) ** -k
            left, right, estimate = derivative_jump(t, step)
            error = abs(estimate - jump)
            print(f"  step 1e-{k:<2}  left {left: .15f}  right {right: .15f}  |jump error| {error:.3E}")
            assert error <= 10 * step
    y = D('1e-30')
    assert abs(K0 - scalar_k(y)) < D('1e-27')
    print("\nq=12. Primitive-inducer character average in residue order 1,5,7,11.")
    units = (1, 5, 7, 11)
    for n, p in sorted(prime_powers(250)):
        actual = [coefficient_mod12(a, n) for a in units]
        assert actual == [coefficient_crt(12, a, n, p) for a in units]
        assert sum(actual) == 1
        if n in (2, 3, 4, 5, 9, 11):
            print(f"  {n:2d} -> " + ", ".join(str(v) for v in actual))
    print("All prime powers through 250 passed both q=12 identities.")
    print("\nq=5. Test the conjugation convention using the complex character chi(2)=i.")
    # On units, every character is a power of chi. Roots of unity here are
    # Gaussian integers and their complex arithmetic is exact in binary floats.
    exponent = {pow(2, j, 5): j for j in range(4)}
    units5 = (1, 2, 3, 4)
    def average(a, n, reverse):
        sign = -1 if reverse else 1
        return sum(1j ** ((j * (sign * exponent[n % 5] - exponent[a])) % 4)
                   for j in range(4)) / 4
    direct = [average(a, 2, False) for a in units5]
    reversed_phase = [average(a, 2, True) for a in units5]
    assert direct == [0, 1, 0, 0]
    assert reversed_phase == [0, 0, 1, 0]
    print("  n=2, positive log location -> residue 2, negative log location -> residue 3.")
    print("All checks passed.")


if __name__ == "__main__":
    check_examples()
