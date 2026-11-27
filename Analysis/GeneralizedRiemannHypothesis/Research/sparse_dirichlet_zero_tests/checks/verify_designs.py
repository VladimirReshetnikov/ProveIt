#!/usr/bin/env python3
"""Independent finite checks of the fixed-stride table and the sampling designs."""

from fractions import Fraction
from functools import lru_cache
from itertools import combinations, product
from math import comb


def trim(poly):
    while poly and poly[-1] == 0:
        poly.pop()
    return poly


def divide_monic(poly, divisor):
    """Integer polynomial division; coefficients are in ascending order."""
    remainder = trim(list(poly))
    quotient = [0] * max(0, len(remainder) - len(divisor) + 1)
    while len(remainder) >= len(divisor):
        degree = len(remainder) - len(divisor)
        factor = remainder[-1]
        quotient[degree] = factor
        for i, coefficient in enumerate(divisor):
            remainder[degree + i] -= factor * coefficient
        trim(remainder)
    return quotient, remainder


@lru_cache(None)
def cyclotomic(m):
    poly = [-1] + [0] * (m - 1) + [1]
    for d in range(1, m):
        if m % d == 0:
            poly, remainder = divide_monic(poly, cyclotomic(d))
            assert not remainder
    return poly


def rational_ratios(m):
    """Compute in Q[X]/Phi_m. Return every rational normalized triple ratio."""
    phi = cyclotomic(m)
    dimension = len(phi) - 1
    powers = []
    for i in range(m):
        _, rem = divide_monic([0] * i + [1], phi)
        powers.append(rem + [0] * (dimension - len(rem)))

    def differences_product(a, b, c, d):
        # (X^a-X^b)(X^c-X^d), using X^m = 1.
        terms = [powers[i % m] for i in (a + c, a + d, b + c, b + d)]
        return [p - q - r + s for p, q, r, s in zip(*terms)]

    ratios = set()
    for a, b, c in combinations(range(1, m), 3):
        num = differences_product(c, a, b, 0)
        den = differences_product(b, a, c, 0)
        pivot = next(i for i, x in enumerate(den) if x)
        if all(x * den[pivot] == y * num[pivot] for x, y in zip(num, den)):
            ratio = Fraction(num[pivot], den[pivot])
            assert ratio > 1
            ratios.add(ratio)
    return ratios


def check_strides():
    exceptional = {Fraction(x) for x in ("4/3", "3/2", "2", "3", "4")}
    triples = 0
    for m in range(1, 41):
        expected = set()
        if m % 6 == 0:
            expected = exceptional
        elif m % 2 == 0 and m >= 4:
            expected = {Fraction(2)}
        observed = rational_ratios(m)
        assert observed == expected, (m, observed, expected)
        triples += comb(m - 1, 3) if m >= 4 else 0
    print(f"Fixed-stride rational ratios checked for m=1..40, {triples} cotangent triples.")


def check_sphere_design():
    digits, dim = 4, 4
    levels = {}
    for vec in product(range(digits), repeat=dim):
        norm = sum(x * x for x in vec)
        encoded = sum(x * (4 * digits) ** i for i, x in enumerate(vec))
        levels.setdefault(norm, []).append(encoded)
    norm, largest = max(sorted(levels.items()), key=lambda item: len(item[1]))
    centers = sorted(largest)
    forbidden = {Fraction(x) for x in ("1/4", "1/3", "1/2", "2/3", "3/4")}
    for a, b, c in combinations(centers, 3):
        assert Fraction(b - a, c - a) not in forbidden
    print(f"Behrend digit design: {len(centers)} centers at squared norm {norm}, "
          f"diameter {centers[-1]-centers[0]}, {comb(len(centers), 3)} triples checked.")


def check_sharp_count():
    model = (-3, -1, 0, 1, 3)
    for D in range(51):
        positions = [10 * 2**j for j in range(D)]
        blind = {x + t for x in positions for t in model}
        mergers = {(x + y) // 2 for x, y in combinations(positions, 2)}
        assert len(blind) == 5 * D
        assert len(mergers) == comb(D, 2)
        assert blind.isdisjoint(mergers)
    print("Sharp family: disjoint disappearances and mergers checked for D=0..50.")


if __name__ == "__main__":
    check_strides()
    check_sphere_design()
    check_sharp_count()

