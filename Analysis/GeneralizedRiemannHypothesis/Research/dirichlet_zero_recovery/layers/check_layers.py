#!/usr/bin/env python3
"""Exact finite checks for weighted prime-zeta layers. Python 3.9+, no dependencies.

Each character sum is evaluated in Z[z]/Phi_e(z). Tests use every point
indicator (a basis for all complex weights) and compare expanded Euler
factors coefficient by coefficient. They do not use numerical L-function zeros.
"""

from fractions import Fraction
from itertools import product
from math import gcd, lcm, prod


def mobius(n):
    result = 1
    divisor = 2
    while divisor * divisor <= n:
        if n % divisor == 0:
            n //= divisor
            if n % divisor == 0:
                return 0
            result *= -1
        divisor += 1
    return -result if n > 1 else result


def reduce_at_root(coeffs, cyclotomic):
    """Exact remainder of a polynomial upon division by monic Phi."""
    coeffs = list(coeffs)
    degree = len(cyclotomic) - 1
    for leading in range(len(coeffs) - 1, degree - 1, -1):
        multiple = coeffs[leading]
        for j, coefficient in enumerate(cyclotomic):
            coeffs[leading - degree + j] -= multiple * coefficient
    return tuple(coeffs[:degree])


def exact_rank(rows):
    matrix = [[Fraction(x) for x in row] for row in rows]
    rank = 0
    for col in range(len(matrix[0])):
        pivot = next((r for r in range(rank, len(matrix)) if matrix[r][col]), None)
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        divisor = matrix[rank][col]
        matrix[rank] = [x / divisor for x in matrix[rank]]
        for r in range(rank + 1, len(matrix)):
            factor = matrix[r][col]
            if factor:
                matrix[r] = [x - factor * y for x, y in zip(matrix[r], matrix[rank])]
        rank += 1
    return rank


def check_group(modulus, generators, orders, phi, max_degree=36):
    exponent = lcm(*orders)
    indices = list(product(*(range(order) for order in orders)))
    units = sorted(a for a in range(1, modulus) if gcd(a, modulus) == 1)
    residues = [prod(pow(g, x, modulus) for g, x in zip(generators, coords)) % modulus
                for coords in indices]
    assert sorted(residues) == units
    size = len(units)

    phases = [
        [sum(j * t * (exponent // order)
             for j, t, order in zip(index, coords, orders)) % exponent
         for coords in indices]
        for index in indices
    ]
    # For each basis weight 1_a, its Fourier coefficients are
    # conjugate(chi(a))/|G|. After pullback x -> x^m, chi becomes chi^m.
    # Test inversion of those transformed coefficients at every b.
    evaluations = {}
    for m in range(exponent):
        for a_index, a in enumerate(residues):
            for b_index, b in enumerate(residues):
                polynomial = [0] * exponent
                for phase in phases:
                    polynomial[(m * phase[b_index] - phase[a_index]) % exponent] += 1
                remainder = reduce_at_root(polynomial, phi)
                expected = size if pow(b, m, modulus) == a else 0
                assert remainder == (expected,) + (0,) * (len(phi) - 2)
                evaluations[m, a, b] = Fraction(remainder[0], size)

    # At a prime p == b (mod q), put t=p^(-s). The k-th log Euler
    # factor has coefficients (chi(b)^k)/k. We compare the Mobius
    # sum and its s-derivative (divided by log p) with 1_a(b)*t
    # and -1_a(b)*t. Keep both the log weights and -degree for d/ds.
    divisors = [[m for m in range(1, r + 1) if r % m == 0]
                for r in range(max_degree + 1)]
    for a in units:
        for b in units:
            for degree in range(1, max_degree + 1):
                log_coeff = Fraction(0)
                derivative_coeff = Fraction(0)
                for m in divisors[degree]:
                    k = degree // m
                    value = evaluations[m % exponent, a, pow(b, k, modulus)]
                    log_coeff += Fraction(mobius(m), m * k) * value
                    derivative_coeff -= mobius(m) * value
                expected = int(degree == 1 and b == a)
                assert log_coeff == expected
                assert derivative_coeff == -degree * log_coeff == -expected

    print(f"q={modulus}, generators={generators}, orders={orders}, exponent={exponent}")
    print(f"  exact character sums: {exponent * size**2}, "
          f"prime-power coefficients and derivatives: {max_degree * size**2} pairs")
    print("  m  mu(m)   rank   observable units")
    for m in (1, 2, 3, 4, 5, 6, 7, 10):
        mu = mobius(m)
        rows = [[mu * int(pow(b, m, modulus) == a) for a in units] for b in units]
        rank = exact_rank(rows)
        image = sorted({pow(b, m, modulus) for b in units}) if mu else []
        expected_rank = prod(d // gcd(m, d) for d in orders) if mu else 0
        assert rank == expected_rank == len(image)
        print(f" {m:2} {mu:6} {rank:6}   {','.join(map(str, image)) or 'none'}")


def main():
    if not __debug__:
        raise SystemExit("Use ordinary Python with assertions enabled.")
    # Phi_12(z)=z^4-z^2+1, Phi_4(z)=z^2+1.
    check_group(13, (2,), (12,), (1, 0, -1, 0, 1))
    check_group(15, (2, 14), (4, 2), (1, 0, 1))
    check_group(16, (3, 15), (4, 2), (1, 0, 1))
    print("All exact finite identities passed.")


if __name__ == "__main__":
    main()
