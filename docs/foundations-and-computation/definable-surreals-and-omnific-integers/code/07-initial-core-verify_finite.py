#!/usr/bin/env python3
"""Exact finite checks accompanying 'Definable Surreal Numbers and Omnific Integers'.

Only finite normal forms with rational exponents and coefficients are represented.
These checks are not proofs about transfinite series, satisfaction, HOD, or the core.
Standard library only; tested with Python 3.11. Run:
    python3 verify_finite.py --output verification.json
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
from typing import Iterable

Term = tuple[F, F]  # (Conway exponent, coefficient)
Form = tuple[Term, ...]


def normalize(terms: Iterable[Term]) -> Form:
    coeffs: dict[F, F] = {}
    for exponent, coefficient in terms:
        if not isinstance(exponent, F) or not isinstance(coefficient, F):
            raise TypeError('Exponents and coefficients must be Fraction objects.')
        coeffs[exponent] = coeffs.get(exponent, F(0)) + coefficient
    return tuple((a, c) for a, c in sorted(coeffs.items(), reverse=True) if c)


def compare(left: Form, right: Form) -> int:
    difference = normalize((*left, *((a, -c) for a, c in right)))
    if not difference:
        return 0
    return 1 if difference[0][1] > 0 else -1


def bit_encode(n: int, bits: frozenset[int]) -> Form:
    if isinstance(n, bool) or not isinstance(n, int) or n < 0:
        raise ValueError('Length must be a nonnegative integer.')
    if any(isinstance(i, bool) or not isinstance(i, int) or not 0 <= i < n
           for i in bits):
        raise ValueError('Every bit position must belong to range(n).')
    return ((F(3, 4), F(1)),) + tuple(
        (F(1, i + 2), F(1 + (i in bits))) for i in range(n)
    )


def bit_decode(series: Form) -> tuple[int, frozenset[int]]:
    if not series or series[0] != (F(3, 4), F(1)):
        raise ValueError('The leading marker is missing or incorrect.')
    recovered: set[int] = set()
    for i, (exponent, coefficient) in enumerate(series[1:]):
        if exponent != F(1, i + 2) or coefficient not in (F(1), F(2)):
            raise ValueError('This is not a finite canonical bit code.')
        if coefficient == 2:
            recovered.add(i)
    return len(series) - 1, frozenset(recovered)


def rational_sqrt(value: F) -> F:
    if value < 0:
        raise ValueError('Negative radicand.')
    numerator, denominator = isqrt(value.numerator), isqrt(value.denominator)
    if numerator * numerator != value.numerator or denominator * denominator != value.denominator:
        raise ValueError('This radicand has no rational square root.')
    return F(numerator, denominator)


def tau(x: F) -> F:
    return (1 + x / rational_sqrt(1 + x * x)) / 2


def tau_inverse(t: F) -> F:
    if not 0 < t < 1:
        raise ValueError('Input must lie strictly between zero and one.')
    u = 2 * t - 1
    return u / rational_sqrt(1 - u * u)


def run_checks() -> dict[str, object]:
    bit_cases = 0
    marker = ((F(3, 4), F(1)),)
    twice_marker = ((F(3, 4), F(2)),)
    omega = ((F(1), F(1)),)
    for n in range(13):
        for mask in range(1 << n):
            bits = frozenset(i for i in range(n) if mask & (1 << i))
            value = bit_encode(n, bits)
            assert bit_decode(value) == (n, bits)
            assert all(a > 0 for a, _ in value)
            assert all(value[i][0] > value[i + 1][0] for i in range(len(value) - 1))
            assert compare(value, marker) == (0 if n == 0 else 1)
            assert compare(value, twice_marker) == -1
            assert compare(twice_marker, omega) == -1
            bit_cases += 1

    malformed = (
        (),
        ((F(3, 4), F(2)),),
        ((F(3, 4), F(1)), (F(1, 2), F(3))),
        ((F(3, 4), F(1)), (F(1, 3), F(1))),
    )
    for value in malformed:
        try:
            bit_decode(value)
        except ValueError:
            pass
        else:
            raise AssertionError('Malformed code was accepted.')

    # Rational parametrization ensures that sqrt(1+x^2) is rational.
    parameters = {F(n, d) for d in range(2, 31) for n in range(1 - d, d)}
    inputs = sorted({2 * s / (1 - s * s) for s in parameters})
    values = []
    for x in inputs:
        t = tau(x)
        assert 0 < t < 1
        assert tau_inverse(t) == x
        values.append(t)
    assert all(a < b for a, b in zip(values, values[1:]))
    assert tau(F(0)) == F(1, 2)
    assert tau(F(3, 4)) == F(4, 5)
    assert tau(F(-3, 4)) == F(1, 5)

    floor_cases = 0
    for denominator in range(1, 10):
        for numerator in range(-21, 22):
            r = F(numerator, denominator)
            for eps_sign in (-1, 0, 1):
                integer = r.numerator // r.denominator
                if r.denominator == 1 and eps_sign < 0:
                    integer -= 1
                x = normalize(((F(1), F(7)), (F(0), r), (F(-1), F(eps_sign))))
                z = normalize(((F(1), F(7)), (F(0), F(integer))))
                z_plus_one = normalize((*z, (F(0), F(1))))
                assert compare(z, x) <= 0
                assert compare(x, z_plus_one) < 0
                floor_cases += 1

    shift_cases = 0
    for a in (F(-7), F(-3, 2), F(-1, 10), F(0), F(1, 3), F(5)):
        for b in (F(-8), F(-2), F(1, 7), F(3)):
            form = normalize(((a, F(2)), (b, F(-3))))
            bound = max(abs(a), abs(b)).__ceil__() + 1
            shifted = normalize((e + bound, c) for e, c in form)
            assert all(e > 0 for e, _ in shifted)
            recovered = normalize((e - bound, c) for e, c in shifted)
            assert recovered == form
            shift_cases += 1

    return {
        'status': 'PASS',
        'arithmetic': 'exact rational and finite formal normal-form arithmetic',
        'finite_bit_codes_exhaustive_lengths': [0, 12],
        'finite_bit_codes_checked': bit_cases,
        'malformed_codes_rejected': len(malformed),
        'rational_compression_and_inverse_pairs': len(inputs),
        'monotonicity_adjacent_pairs': len(inputs) - 1,
        'floor_correction_cases': floor_cases,
        'finite_support_shift_cases': shift_cases,
        'boundary': (
            'No transfinite, set-theoretic satisfaction, HOD, epsilon-cutoff, '
            'elementarity, or maximal-core theorem is computationally verified here.'
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('verification.json'))
    args = parser.parse_args()
    result = run_checks()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
