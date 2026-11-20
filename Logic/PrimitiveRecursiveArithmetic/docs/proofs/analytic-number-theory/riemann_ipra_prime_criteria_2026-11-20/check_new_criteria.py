#!/usr/bin/env python3
"""Exact finite checks for the split-prime and Taylor formulas in the report."""
from fractions import Fraction
from math import factorial, prod

from check_packets import (
    euler_product, normalize, power_mod, primes_through, remainder,
)


def split_by_linear_division(f, p):
    remaining = list(normalize(f, p))
    for root in range(p):
        while len(remaining) > 1:
            quotient = [0] * (len(remaining) - 1)
            quotient[-1] = remaining[-1]
            for j in reversed(range(len(quotient) - 1)):
                quotient[j] = (remaining[j + 1] + root * quotient[j + 1]) % p
            if (remaining[0] + root * quotient[0]) % p:
                break
            remaining = quotient
    return len(remaining) == 1


def split_by_power(f, p):
    degree = len(f) - 1
    factor = list(power_mod((0, 1), p, f, p))
    factor += [0] * max(0, 2 - len(factor))
    factor[1] -= 1
    return not remainder(power_mod(tuple(factor), degree, f, p), f, p)


def prime_bits(y, active):
    return prod(p for p in primes_through(y) if active(p)).bit_length() - 1


def congruence_gap(m, n):
    def active(p):
        return p % m == 1
    return abs(prime_bits(2*n, active) - 2*prime_bits(n, active))


def log_numerator(n, N):
    return sum(N*N // (N+i) for i in range(1, N*(n-1)+1))


def taylor_example(f, c, k, N):
    B = [euler_product(f, n).bit_length()-1 for n in range(N+1)]
    b = [0] + [B[n]-B[n-1]-2*(B[n//2]-B[(n-1)//2]) for n in range(1, N+1)]
    assert sum(b) == B[N]-2*B[N//2]
    A = 0
    direct = Fraction(0)
    for n in range(1, N+1):
        J = log_numerator(n, N)
        log_lower = Fraction(J, N*N)
        right = sum((Fraction(1, N+i) for i in range(1, N*(n-1)+1)), Fraction(0))
        left = right + Fraction(n-1, N*n)
        assert log_lower <= right <= left <= log_lower + Fraction(n, N)
        direct += b[n] * log_lower**k / (factorial(k) * n**c)
        A += b[n] * J**k * (factorial(N)//n)**c
    D = factorial(k) * N**(2*k) * factorial(N)**c
    assert Fraction(A, D) == direct
    return A, D


def main():
    polynomials = [(-1, 1), (1, 0, 1), (-2, 0, 0, 1), (1, -2, 1), (0, 0, 0, 0, 1)]
    for f in polynomials:
        for p in primes_through(101):
            assert split_by_power(f, p) == split_by_linear_division(f, p)
    cubic = (-2, 0, 0, 1)
    assert [p for p in (2, 3, 5, 7, 31) if split_by_power(cubic, p)] == [2, 3, 31]
    print("Complete splitting: 130 cross-checks including repeated roots.")
    for n in (100, 200, 500):
        gaps = [congruence_gap(m, n) for m in range(2, 2*n+1)]
        print(f"n={n}: max gap {max(gaps)}, least maximizing modulus {gaps.index(max(gaps))+2}")
        assert congruence_gap(2*n+1, n) == 0
        assert max(gaps)**2 <= n * (64 * (2*n).bit_length()**2)**2
    count = 0
    for f in polynomials:
        for N in (1, 2, 5, 8):
            for c in (5, 8):
                for k in range(4):
                    taylor_example(f, c, k, N)
                    count += 1
    print(f"Taylor coefficients: {count} exact signed-sum and denominator comparisons.")
    for c in (36, 68):
        radius = c-Fraction(1, 2)-Fraction(1, 2*c)
        inside = (c-Fraction(3, 4))**2+25 < radius**2
        assert inside == (c == 68)
        print(f"3/4+5i inside the disk at {c}: {inside}")


if __name__ == "__main__":
    main()
