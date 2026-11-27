"""Exact checks of the Grover periodicity and multiplicity statements.

Run with Python 3.9+. Field elements are power-basis vectors obtained by
polynomial reduction modulo Phi_N. No spectral floating-point test is used.
"""
from collections import Counter
from functools import lru_cache
from itertools import combinations_with_replacement
from math import comb, factorial, prod


def divide_monic(numerator, denominator):
    """Return quotient and remainder of ascending integer coefficient lists."""
    remainder = list(numerator)
    width = len(denominator) - 1
    quotient = [0] * max(0, len(remainder) - width)
    for i in range(len(quotient) - 1, -1, -1):
        coefficient = remainder[i + width]
        quotient[i] = coefficient
        for j, value in enumerate(denominator):
            remainder[i + j] -= coefficient * value
    return quotient, remainder[:width]


@lru_cache(maxsize=None)
def cyclotomic(n):
    polynomial = [-1] + [0] * (n - 1) + [1]
    for divisor in range(1, n):
        if n % divisor == 0:
            polynomial, remainder = divide_monic(polynomial, cyclotomic(divisor))
            assert not any(remainder)
    return polynomial


@lru_cache(maxsize=None)
def cosine_vectors(n):
    polynomial = cyclotomic(n)
    width = len(polynomial) - 1
    values = []
    for a in range(n):
        coefficients = [0] * n
        coefficients[a] += 1
        coefficients[-a % n] += 1
        _, remainder = divide_monic(coefficients, polynomial)
        values.append(tuple((remainder + [0] * width)[:width]))
    return values


def degree_four_checks():
    tested = 0
    for n in range(1, 73):
        vectors = cosine_vectors(n)
        for a, va in enumerate(vectors):
            for b, vb in enumerate(vectors):
                integral = all((x + y) % 2 == 0 for x, y in zip(va, vb))
                aligned = (a + b) % n == 0 or (a - b) % n == 0
                opposite = n % 2 == 0 and n // 2 in ((a + b) % n, (a - b) % n)
                real_imag = (
                    n % 4 == 0
                    and ((2 * a % n == 0 and 2 * b % n == n // 2)
                         or (2 * b % n == 0 and 2 * a % n == n // 2))
                )
                assert integral == (aligned or opposite or real_imag), (n, a, b)
                tested += 1
    return tested


def primary_checks(n, p, d):
    vectors = cosine_vectors(n)
    multiplicities = Counter()
    totals = 0
    # Sort inverse pairs and restore the mass of ordered tuples by multinomials.
    for representatives in combinations_with_replacement(range(n // 2 + 1), d):
        counts = Counter(representatives)
        multiplicity = factorial(d) * 2 ** (d - counts[0])
        multiplicity //= prod(factorial(c) for c in counts.values())
        totals += multiplicity
        numerator = [0] * len(vectors[0])
        for a, count in counts.items():
            for i, value in enumerate(vectors[a]):
                numerator[i] += count * value
        integral = all(coefficient % d == 0 for coefficient in numerator)
        aligned = len(counts) == 1
        k = None
        if not any(numerator[1:]) and numerator[0] in (0, d):
            k = numerator[0] // d
            multiplicities[k] += multiplicity
        # Independently check the coset decomposition when a tuple is unaligned.
        histogram = [0] * n
        for a, count in counts.items():
            histogram[a] += count
            histogram[-a % n] += count
        stride = n // p
        predicted = None
        for trace in (0, 1):
            adjusted = histogram.copy()
            adjusted[0] -= trace * d
            if min(adjusted) >= 0 and all(
                len(set(adjusted[j::stride])) == 1 for j in range(stride)
            ):
                predicted = trace
        assert predicted == k
        assert integral == (aligned or k is not None)
    assert totals == n**d
    if d % p:
        assert not multiplicities
    if p == 3 and d == 6:
        b = (n // p - 1) // 2
        assert multiplicities[0] == 240 + 17280 * b + 46080 * comb(b, 2)
        assert multiplicities[1] == 60 + 960 * b
    return totals, multiplicities[0], multiplicities[1]


if __name__ == "__main__":
    print("Degree-four character pairs checked:", degree_four_checks())
    print(" N  p  d      labelled tuples       trace 0       trace 1")
    for p, n, d in [(3, 9, 2), (3, 9, 3), (3, 9, 4), (3, 3, 6),
                    (3, 9, 6), (3, 27, 6), (5, 5, 5), (5, 25, 3),
                    (7, 7, 2), (7, 7, 7)]:
        total, fourth, sixth = primary_checks(n, p, d)
        print(f"{n:2} {p:2} {d:2} {total:19,} {fourth:13,} {sixth:13,}")
