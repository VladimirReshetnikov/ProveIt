#!/usr/bin/env python3
"""Recheck finite Mertens identities with exact standard-library arithmetic."""

import json
from functools import cache
from math import factorial, gcd, lcm


def mobius(n):
    """Find prime factors by trial division, detecting a repeated factor."""
    result = 1
    divisor = 2
    while divisor * divisor <= n:
        if n % divisor == 0:
            n //= divisor
            if n % divisor == 0:
                return 0
            result = -result
        divisor += 1
    return -result if n > 1 else result


def require_equal(actual, expected, case):
    if actual != expected:
        raise ValueError(f'{case}: {actual!r} != {expected!r}')


def redheffer_det(n):
    """Bareiss elimination, independent of the row proof in the paper."""
    a = [[int(j == 1 or j % i == 0) for j in range(1, n + 1)]
         for i in range(1, n + 1)]
    previous, sign = 1, 1
    for k in range(n - 1):
        if a[k][k] == 0:
            pivot_row = next((i for i in range(k + 1, n) if a[i][k]), None)
            if pivot_row is None:
                return 0
            a[pivot_row], a[k] = a[k], a[pivot_row]
            sign = -sign
        pivot = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                numerator = pivot * a[i][j] - a[i][k] * a[k][j]
                a[i][j], remainder = divmod(numerator, previous)
                require_equal(remainder, 0, ('Bareiss division', n, k, i, j))
            a[i][k] = 0
        previous = pivot
    return sign * a[-1][-1]


def strip(poly):
    while poly and poly[-1] == 0:
        poly.pop()
    return poly


def divide_monic(numerator, denominator):
    """Coefficients are in increasing order of degree. [] represents zero."""
    remainder = strip(list(numerator))
    quotient = [0] * max(0, len(remainder) - len(denominator) + 1)
    while len(remainder) >= len(denominator):
        shift = len(remainder) - len(denominator)
        lead = remainder[-1]
        quotient[shift] = lead
        for j, c in enumerate(denominator):
            remainder[shift + j] -= lead * c
        strip(remainder)
    return strip(quotient), remainder


@cache
def cyclotomic(m):
    poly = [-1] + [0] * (m - 1) + [1]
    for d in range(1, m):
        if m % d == 0:
            poly, remainder = divide_monic(poly, cyclotomic(d))
            require_equal(remainder, [], ('cyclotomic division', m, d))
    return tuple(poly)


def cyclic_multiplier(length):
    """D_L is the product of (1-X^k), 1 <= k < L, modulo X^L-1."""
    coeffs = [1] + [0] * (length - 1)
    for k in range(1, length):
        coeffs = [a - b for a, b in zip(coeffs, coeffs[-k:] + coeffs[:-k])]
    return coeffs


def check_farey(mu, mertens):
    denominator_cases = 0
    frequency_cases = 0
    for n in range(1, 7):
        length = factorial(n)
        multiplier = cyclic_multiplier(length)
        modulus = cyclotomic(length)
        for h in range(2 * n + 2):
            farey_polynomial = [1] + [0] * (length - 1)  # 0/1
            for q in range(1, n + 1):
                exponents = [(h * a * (length // q)) % length
                             for a in range(1, q + 1) if gcd(a, q) == 1]
                expected = sum(r * mu[q // r] for r in range(1, q + 1)
                               if q % r == 0 and h % r == 0)
                polynomial = [0] * length
                for exponent in exponents:
                    polynomial[exponent] += 1
                    farey_polynomial[exponent] += 1
                _, remainder = divide_monic(polynomial, modulus)
                require_equal(remainder, strip([expected]), ('Ramanujan', n, q, h))
                for i in range(length):
                    coeff = sum(multiplier[(i - e) % length] for e in exponents)
                    require_equal(coeff, expected * multiplier[i],
                                  ('cyclic certificate', n, q, h, i))
                denominator_cases += 1
            weighted = 1 + sum(r * mertens[n // r] for r in range(1, n + 1)
                               if h % r == 0)
            _, remainder = divide_monic(farey_polynomial, modulus)
            require_equal(remainder, strip([weighted]), ('Farey', n, h))
            frequency_cases += 1
    return {'maximum_order': 6, 'largest_cyclic_list_length': factorial(6),
            'frequencies_per_order': '0 through 2N+1 inclusive',
            'order_frequency_pairs': frequency_cases,
            'order_denominator_frequency_triples': denominator_cases}


def check_ordered_products(mertens, limit):
    # Record each nonempty tuple once, then sum by its exact product.
    weights = [0] * (limit + 1)

    def extend(product, sign):
        weights[product] += sign
        for factor in range(2, limit // product + 1):
            extend(product * factor, -sign)

    extend(1, 1)  # empty tuple
    total = 0
    for n in range(1, limit + 1):
        total += weights[n]
        require_equal(total, mertens[n], ('ordered products', n))


def main():
    limit = 256
    mu = [0] + [mobius(n) for n in range(1, limit + 1)]
    mertens = [0]
    for m in mu[1:]:
        mertens.append(mertens[-1] + m)

    phi_total, lcm_total = 0, 1
    for n in range(1, limit + 1):
        phi_total += sum(gcd(n, b) == 1 for b in range(1, n + 1))
        lcm_total = lcm(lcm_total, n)
        floor_sum, weighted, positive, negative = 0, 0, 1, 1
        for a in range(1, n + 1):
            weight = mertens[n // a]
            floor_sum += weight
            weighted += a * weight
            if weight < 0:
                negative *= a ** (-weight)
            else:
                positive *= a ** weight
        require_equal(floor_sum, 1, ('floor sum', n))
        require_equal(weighted, phi_total, ('totient sum', n))
        require_equal(positive, negative * lcm_total, ('Chebyshev product', n))

    for n in range(1, 65):
        require_equal(redheffer_det(n), mertens[n], ('Redheffer determinant', n))
    check_ordered_products(mertens, limit)
    print(json.dumps({'floor_totient_chebyshev_orders': [1, limit],
                      'ordered_product_orders': [1, limit],
                      'redheffer_determinant_orders': [1, 64],
                      'farey': check_farey(mu, mertens), 'status': 'passed'},
                     indent=2))


if __name__ == '__main__':
    main()
