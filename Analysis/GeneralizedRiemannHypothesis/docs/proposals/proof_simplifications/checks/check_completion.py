#!/usr/bin/env python3
"""Exact finite checks of the Gauss identity used for Fourier completion.

Only the Python standard library is required. All arithmetic is in Z[z]/Phi_N(z).
"""
from functools import lru_cache
from math import gcd, lcm


def trim(polynomial):
    while polynomial and polynomial[-1] == 0:
        polynomial.pop()
    return polynomial


def divide_monic(polynomial, divisor):
    """Quotient and remainder for low-degree-first integer coefficients."""
    work = trim(polynomial.copy())
    quotient = [0] * max(0, len(work) - len(divisor) + 1)
    while len(work) >= len(divisor):
        shift = len(work) - len(divisor)
        lead = work[-1]
        quotient[shift] = lead
        for offset, coefficient in enumerate(divisor):
            work[shift + offset] -= lead * coefficient
        trim(work)
    return quotient, work


@lru_cache(maxsize=None)
def cyclotomic(n):
    result = [-1] + [0] * (n - 1) + [1]
    for divisor in range(1, n):
        if n % divisor == 0:
            result, remainder = divide_monic(result, cyclotomic(divisor))
            assert not remainder
    return tuple(result)


def test_family(c, p):
    conductor = c * p
    order = lcm(4, conductor)
    modulus = cyclotomic(order)
    # The quartic character maps the generator 2 mod 5 to i.
    powers = {1: 0, 2: 1, 4: 2, 3: 3}

    def character_exponent(a):
        if gcd(a, conductor) != 1:
            return None
        value = 0 if c == 1 else powers[a % 5] * (order // 4)
        if pow(a, (p - 1) // 2, p) != 1:
            value += order // 2
        return value % order

    def fourier_sum(m):
        result = [0] * order
        for a in range(conductor):
            exponent = character_exponent(a)
            if exponent is not None:
                phase = a * m * (order // conductor)
                result[(phase + exponent) % order] += 1
        return result

    gauss = fourier_sum(1)
    for m in range(conductor):
        exponent = character_exponent(m)
        expected = [0] * order
        if exponent is not None:
            for i, count in enumerate(gauss):
                expected[(i - exponent) % order] += count
        diff = [a - b for a, b in zip(fourier_sum(m), expected)]
        assert not divide_monic(diff, modulus)[1], (c, p, m)

    norm = [0] * order
    terms = [(i, a) for i, a in enumerate(gauss) if a]
    for i, a in terms:
        for j, b in terms:
            norm[(i - j) % order] += a * b
    norm[0] -= conductor
    assert not divide_monic(norm, modulus)[1], (c, p, "norm")
    return conductor


if __name__ == "__main__":
    moduli = [test_family(c, p) for c in (1, 5) for p in (3, 7, 11, 13)]
    print(f"Verified all {sum(moduli)} frequencies for {len(moduli)} characters.")
    print("Verified the conductor identity for every squared Gauss-sum norm.")
