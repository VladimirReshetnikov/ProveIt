#!/usr/bin/env python3
"""Exact six-power certificates for H_{-87} and H_{-152}; standard library only.

The proof for unbounded exponents is in the report's confluent-certificate section. This program
verifies its finite modular input; it does not enumerate unbounded exponents.
The integer class polynomial is reused from the audited incoming CM report.
"""
if not __debug__:
    raise SystemExit("Run this certificate without Python optimization (-O).")

from fractions import Fraction
import json
from math import comb
from pathlib import Path

H152 = [
    472390748138731280269312000000000000000000,
    -1380504171426125758791680000000000000000,
    2783058624787093614292992000000000000,
    6854544294799483688960000000000,
    17024071380555203520000000,
    -66246265919280000,
    1,
]
H87 = [
    549806430204864490157810211181640625,
    432181202257616392838287353515625,
    497577733884372638735595703125,
    28321090578679361484375000,
    85585228375218750,
    5321761711875,
    1,
]

CERTIFICATES = [
    {'discriminant': -87, 'polynomial_ascending': H87,
     'prime': 2, 'depth': 4, 'period': 63,
     'power_remainder': [1, 16, 16, 16, 0, 0],
     'D_remainder_mod_p': [0, 1, 1, 1, 0, 0],
     'integer_determinant': -1},
    {'discriminant': -152, 'polynomial_ascending': H152,
     'prime': 3, 'depth': 2, 'period': 182,
     'power_remainder': [26, 0, 18, 9, 0, 18],
     'D_remainder_mod_p': [0, 0, 2, 1, 0, 2],
     'integer_determinant': -2},
]


def multiply(a, b, h, modulus):
    degree = len(h) - 1
    c = [0] * (2 * degree - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            c[i + j] += ai * bj
    for i in range(len(c) - 1, degree - 1, -1):
        for j in range(degree):
            c[i - degree + j] -= c[i] * h[j]
    return tuple(ci % modulus for ci in c[:degree])


def power(a, n, h, modulus):
    out = (1,) + (0,) * (len(h) - 2)
    while n:
        if n & 1:
            out = multiply(out, a, h, modulus)
        a = multiply(a, a, h, modulus)
        n //= 2
    return out


def determinant(a):
    a = [list(map(Fraction, row)) for row in a]
    out = Fraction(1)
    for j in range(len(a)):
        pivot = next((i for i in range(j, len(a)) if a[i][j]), None)
        if pivot is None:
            return 0
        if pivot != j:
            a[j], a[pivot] = a[pivot], a[j]
            out *= -1
        out *= a[j][j]
        for i in range(j + 1, len(a)):
            q = a[i][j] / a[j][j]
            a[i] = [x - q * y for x, y in zip(a[i], a[j])]
    assert out.denominator == 1
    return out.numerator


def valuation_factorial(n, p):
    out = 0
    while n:
        n //= p
        out += n
    return out


def main():
    x = (0, 1, 0, 0, 0, 0)
    for certificate in CERTIFICATES:
        h = certificate['polynomial_ascending']
        p, s, m = (certificate[k] for k in ['prime', 'depth', 'period'])
        modulus = p ** (s + 1)
        result = power(x, m, h, modulus)
        assert result == tuple(certificate['power_remainder'])
        assert result[0] % p and all(c % p**s == 0 for c in result[1:])
        d = (0,) + tuple(c // p**s for c in result[1:])
        assert d == tuple(certificate['D_remainder_mod_p'])
        columns = [(1, 0, 0, 0, 0, 0)]
        for _ in range(5):
            columns.append(multiply(columns[-1], d, h, p))
        matrix = list(zip(*columns))
        det = determinant(matrix)
        assert det == certificate['integer_determinant']
        assert det % p == 1
        assert 6 < p**s
        # An independent recurrence confirms the modular power computation.
        v = [1, 0, 0, 0, 0, 0]
        for _ in range(m):
            top = v[-1]
            v = [0] + v[:-1]
            v = [(v[j] - top * h[j]) % modulus for j in range(6)]
        assert tuple(v) == result
        print(f"H_{certificate['discriminant']}: x^{m} modulo (H,{modulus}) = {result}")
        print(f'D modulo (H,{p}) = {d}')
        print(f'Power-basis determinant = {det}; modulo {p} = 1.')
        print('Matrix rows:', [list(row) for row in matrix])
        print('Independent recurrence agrees.')
    input_path = Path(__file__).with_name('confluent_certificates.json')
    if input_path.exists():
        assert json.loads(input_path.read_text()) == CERTIFICATES
    # These are finite sanity checks of the general factorial inequality;
    # the proof, not this sampled check, covers every i and every prime.
    count = 0
    for p, s in [(2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (5, 1), (7, 1)]:
        for j in range(p**s - 1):
            for i in range(j + 1, 300):
                loss = valuation_factorial(i, p) - valuation_factorial(j, p)
                assert s * (i - j) > loss
                count += 1
        j = p**s - 1
        i = p**s
        assert s == valuation_factorial(i, p) - valuation_factorial(j, p)
        k = p**s
        # Boundary polynomial has exactly k nonzero terms.
        coeff = [(-1)**(k-j) * comb(k, j) for j in range(k + 1)]
        for j in range(k):
            coeff[j] += k * (-1)**(k-1-j) * comb(k-1, j)
        coeff[0] -= k**k
        assert coeff[k-1] == 0
        assert sum(c != 0 for c in coeff) == k
    print('Factorial sanity checks:', count, '; boundary checks: 7.')
    print('Certified finite input for all six-exponent sets in one residue class modulo 63 or 182, respectively.')


if __name__ == '__main__':
    main()
