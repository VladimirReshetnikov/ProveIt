#!/usr/bin/env python3
"""Exact tests of the code and reflection decoder in carriers.tex.

All arithmetic uses integers or fractions. Spectra below are synthetic, and
the code coefficients are truncated strictly after every block used to read
digits. The infinite tail bound is proved in the paper.
"""
from collections import Counter, defaultdict
from fractions import Fraction
from math import isqrt


def places(weights, last_stage):
    """Map dyadic block and slot to (radix, denominator)."""
    layout = {}
    stage, denominator = 1, 1
    while stage <= last_stage:
        minimum = 8 * (stage + 1) * max(weights[:stage + 1])
        radix = 1 << (minimum - 1).bit_length()
        for slot in range(stage + 1):
            denominator *= radix
            layout[stage, slot] = radix, denominator
        stage *= 2
    return layout


def encode(digits, layout):
    total = Fraction(digits.get(0, 0))
    for (_, slot), (_, denominator) in layout.items():
        total += Fraction(digits.get(slot, 0), denominator)
    return total


def read_digit(value, location):
    radix, denominator = location
    return round(value * denominator) % radix


def test_overflow():
    # Several early radices are too small. In a late block the digits fit
    # even when nearly maximal positive or negative observation noise is added.
    weights = [i + 1 for i in range(129)]
    layout = places(weights, 128)
    envelope = 64
    patterns = [
        {i: envelope * w for i, w in enumerate(weights)},
        {i: (envelope * w if i % 3 == 0 else i % 7) for i, w in enumerate(weights)},
        {i: (envelope * w if i % 5 else 0) for i, w in enumerate(weights)},
    ]
    tests = 0
    assert patterns[0][0] > layout[1, 0][0]
    for digits in patterns:
        value = encode(digits, layout)
        for slot in range(65):
            radix, denominator = layout[64, slot]
            noise = Fraction(249, 1000 * denominator)
            for shift in (-noise, Fraction(0), noise):
                assert read_digit(value + shift, (radix, denominator)) == digits[slot]
                tests += 1
    return tests


# Points a+b*sqrt(2) represented as (a,b) in Z^2.
SHIFTS = ((0, 0), (1, 0), (0, 1))


def plus(x, y):
    return x[0] + y[0], x[1] + y[1]


def minus(x):
    return -x[0], -x[1]


def reflect(x, k):
    return minus(plus(plus(x, SHIFTS[k]), SHIFTS[k]))


def exact_sqrt(value):
    a, b = isqrt(value.numerator), isqrt(value.denominator)
    assert a*a == value.numerator and b*b == value.denominator
    return Fraction(a, b)


def make_powers(spectra, layout):
    # Forward model of 4 |rho(rho+1)|^2 P: sum all translated and reflected
    # contributions BEFORE squaring. Distinct labels can collide at one height.
    digits_at = defaultdict(Counter)
    for j, spectrum in enumerate(spectra):
        for x, multiplicity in spectrum.items():
            for k, shift in enumerate(SHIFTS):
                t = plus(x, shift)
                digits_at[t][3*j+k] += multiplicity
                digits_at[minus(t)][3*j+k] += multiplicity
    return {t: encode(digits, layout)**2 for t, digits in digits_at.items()}, digits_at


def decode_multiplicity(j, x, power_at, layout, stage):
    def edge(z, k):
        t = plus(z, SHIFTS[k])
        amplitude = exact_sqrt(power_at.get(t, Fraction(0)))
        return read_digit(amplitude, layout[stage, 3*j+k])

    y, n, path = x, 0, []
    while edge(y, 0):
        integer_part = isqrt(2*n*n)
        n += 1
        decrement = isqrt(2*n*n) - integer_part
        for k in (2, 0) + (0, 1)*decrement:
            path.append(edge(y, k))
            y = reflect(y, k)
        assert y == plus(x, (-2*isqrt(2*n*n), 2*n))
    multiplicity = 0
    for edge_sum in reversed(path):
        multiplicity = edge_sum - multiplicity
    return multiplicity, n


def test_collisions():
    start = (3, -1)
    # Populate a long initial stretch of the decoder's orbit.
    first = Counter({plus(start, (-2*isqrt(2*n*n), 2*n)): n%4+1 for n in range(10)})
    first.update({(0, 0): 3, (-1, 0): 2, (0, -1): 1})
    # Include its conjugate divisor, central zeros and deliberately shared
    # and oppositely oriented shifted zeros.
    spectra = [
        first,
        Counter({minus(x): v for x, v in first.items()}),
        Counter({(0, 0): 2, (0, -1): 4, (-1, 0): 3, start: 2}),
    ]
    layout = places([2]*33, 32)
    powers, digits = make_powers(spectra, layout)
    assert len(digits[(0, 0)]) >= 7
    assert all(v % 2 == 0 for v in digits[(0, 0)].values())
    assert all(powers.get(minus(t), 0) == p for t,p in powers.items())
    cases = set(powers) | {(-10, 7), (7, 3)}
    for spectrum in spectra:
        cases.update(spectrum)
    for j, spectrum in enumerate(spectra):
        for x in cases:
            result, _ = decode_multiplicity(j, x, powers, layout, 16)
            assert result == spectrum.get(x, 0)
    _, hops = decode_multiplicity(0, start, powers, layout, 16)
    assert hops >= 10
    return len(cases)*len(spectra), len(digits[(0,0)]), hops


if __name__ == "__main__":
    print("Exact noisy digit checks:", test_overflow())
    queries, central, hops = test_collisions()
    print("Signed labelled multiplicity checks:", queries)
    print("Populated character/carrier slots colliding at zero:", central)
    print("Hops before first zero anchor in long-path example:", hops)
