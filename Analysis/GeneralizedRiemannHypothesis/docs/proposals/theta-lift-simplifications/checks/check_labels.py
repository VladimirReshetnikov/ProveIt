#!/usr/bin/env python3
"""Exact checks of the finite-field label replacement. Python standard library."""
from fractions import Fraction
from itertools import combinations
from math import gcd, isqrt, lcm, prod
from random import Random


def prime_divisors(n):
    result = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            result.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        result.append(n)
    return result


def local_data(q, r, n):
    group_order = q**r - 1
    a = q ** (r // 3)
    h = (a*a + a + 1) // 3
    bad_moduli = [3, h] + [p**6 for p in prime_divisors(n) if p != 3]
    assert all(group_order % m == 0 for m in bad_moduli)
    assert all(gcd(i, j) == 1 for i, j in combinations(bad_moduli, 2))
    assert (q-1) % n**2 == 0
    return group_order, bad_moduli


def selected(k, bad_moduli):
    return all(k % m for m in bad_moduli)


def orbit_degree(q, r, order):
    for degree in range(1, r+1):
        if pow(q, degree, order) == 1 % order:
            return degree
    raise AssertionError('Order does not divide the group order')


def check_operators(q, r, n, k, shifts, coefficient_primes):
    group_order, moduli = local_data(q, r, n)
    for shift in shifts:
        t = (k + (group_order // n) * shift) % group_order
        assert selected(t, moduli) == selected(k, moduli)
        if not selected(k, moduli):
            continue
        order = group_order // gcd(group_order, t)
        norm_order = order // gcd(order, group_order // (q-1))
        assert norm_order % n == 0
        for ell in coefficient_primes:
            reduced = order
            while reduced % ell == 0:
                reduced //= ell
            assert orbit_degree(q, r, reduced) == r


def count_by_crt(group_order, moduli):
    count = group_order * prod(Fraction(m-1, m) for m in moduli)
    assert count.denominator == 1
    return int(count)


def count_by_inclusion_exclusion(group_order, moduli):
    return sum((-1)**j * (group_order // lcm(*subset))
               for j in range(len(moduli)+1) for subset in combinations(moduli, j))


def small_model():
    q, r, n = 19, 3, 3
    group_order, moduli = local_data(q, r, n)
    roots = {k for k in range(group_order) if selected(k, moduli)}
    frobenius_orbits = {min(k*q**j % group_order for j in range(r)) for k in roots}
    primitive = sum(gcd(k, group_order) == 1 for k in range(group_order)) // r
    assert len(roots) == count_by_crt(group_order, moduli) == 4536
    assert len(frobenius_orbits) == len(roots)//r == 1512 and primitive == 756
    primes = prime_divisors(group_order) + [5]
    for k in range(group_order):
        check_operators(q, r, n, k, range(n), primes)
    print('F_19^3, N=3: 6858 exponents, all three scalings, every relevant coefficient prime; '
          '4536 selected roots, 1512 selected polynomials, 756 primitive polynomials.')


def mul(x, y):
    # F_19[t]/(t^3-2), in the power basis (1,t,t²).
    coeff = [0]*5
    for i, v in enumerate(x):
        for j, w in enumerate(y):
            coeff[i+j] += v*w
    coeff[0] += 2*coeff[3]
    coeff[1] += 2*coeff[4]
    return tuple(c % 19 for c in coeff[:3])


def power(x, exponent):
    result = (1, 0, 0)
    while exponent:
        if exponent % 2:
            result = mul(result, x)
        x = mul(x, x)
        exponent //= 2
    return result


def polynomial_example():
    one = (1, 0, 0)
    assert all(t**3 % 19 != 2 for t in range(19))
    g = (1, 1, 0)
    order = 19**3 - 1
    assert power(g, order) == one
    assert all(power(g, order//p) != one for p in prime_divisors(order))
    z = mul(g, g)
    coeff = [one]
    for i in range(3):
        root = power(z, 19**i)
        new = [(0,0,0)] * (len(coeff) + 1)
        for j, c in enumerate(coeff):
            new[j] = tuple((a-b) % 19 for a, b in zip(new[j], mul(c, root)))
            new[j+1] = tuple((a+b) % 19 for a, b in zip(new[j+1], c))
        coeff = new
    assert coeff == [(10,0,0), (10,0,0), (16,0,0), one]
    assert power(z, order//18) == (9,0,0)
    assert pow(9, 9, 19) == 1 and pow(9, 3, 19) != 1
    print('Field arithmetic: g=1+t has order 6858; minpoly(g²)=X³+16X²+10X+10, norm 9 of order 9.')


def large_order_models():
    rng = Random(20261127)
    for q, n in [(147457, 64), (32651735041, 6**6)]:
        assert all(q % p for p in range(2, isqrt(q)+1))
        for r in (3, 9):
            group_order, moduli = local_data(q, r, n)
            count = count_by_crt(group_order, moduli)
            assert count == count_by_inclusion_exclusion(group_order, moduli)
            assert count % r == 0 and 2*count >= q**r
            cases = [0, 1, 2, group_order-1, *(m for m in moduli)]
            cases.extend(rng.randrange(group_order) for _ in range(150))
            for k in cases:
                check_operators(q, r, n, k, (0, 1, n-1, rng.randrange(n)), (2, 3, 5, 7, 19, 127))
            print(f'q={q}, r={r}, N={n}: exact count by CRT and inclusion-exclusion; '
                  f'{len(cases)} exponents tested for scaling, norm and residue degrees.')
    assert (1-Fraction(1,19**3))*Fraction(2,3)*Fraction(126,127)*Fraction(313,320) > Fraction(1,2)


if __name__ == '__main__':
    small_model()
    polynomial_example()
    large_order_models()
