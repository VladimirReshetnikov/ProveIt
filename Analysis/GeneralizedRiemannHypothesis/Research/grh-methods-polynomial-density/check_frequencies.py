"""Verify exact prime-power frequencies in the finite example for localized.tex.

The amplifier uses unit cosine weights. A(t) is the imaginary part of
the product of 1 + i*cos(t*log p) over three primes. Multiply by the
sample phase polynomial F(t) = (1+cos(t*log 2))*(1+cos(t*log 3)).
This checks the finite diagonal calculation, independently of zero data.
"""
from fractions import Fraction
from itertools import product
from math import isqrt, prod


def is_prime(n):
    return n >= 2 and all(n % k for k in range(2, isqrt(n) + 1))


def is_prime_power(n):
    if n < 2:
        return False
    factor = next((k for k in range(2, isqrt(n) + 1) if n % k == 0), n)
    while n % factor == 0:
        n //= factor
    return n == 1


def main():
    q, d = 8, 7
    phase = (2, 3)
    inert = (17, 41, 73)
    for p in inert:
        assert is_prime(p) and p % q == 1
        assert pow(p, (d - 1) // 2, d) == d - 1

    coeffs = {}
    for exponents in product((-1, 0, 1), repeat=len(phase) + len(inert)):
        active_inert = sum(k != 0 for k in exponents[len(phase):])
        if active_inert % 2 == 0:
            continue
        active = sum(k != 0 for k in exponents)
        # Imaginary part of i**active_inert, and coefficient 1/2 per cosine.
        coefficient = Fraction((-1) ** ((active_inert - 1) // 2), 2 ** active)
        ratio = prod(Fraction(p) ** k for p, k in zip(phase + inert, exponents))
        assert ratio not in coeffs
        coeffs[ratio] = coefficient

    diagonal = {r: a for r, a in coeffs.items()
                if (r.denominator == 1 and is_prime_power(r.numerator))
                or (r.numerator == 1 and is_prime_power(r.denominator))}
    expected = {r: Fraction(1, 2) for p in inert
                for r in (Fraction(p), Fraction(1, p))}
    assert Fraction(1) not in coeffs
    assert diagonal == expected
    print(f"{len(coeffs)} nonzero frequencies, {len(diagonal)} prime-power diagonals")
    for p in inert:
        print(f"{p} and 1/{p} each have Fourier coefficient {diagonal[Fraction(p)]}")


if __name__ == "__main__":
    main()
