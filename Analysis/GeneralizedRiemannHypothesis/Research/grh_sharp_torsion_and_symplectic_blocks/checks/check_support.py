"""Exact support versus signed-character-mass calculation for rational A5 tests.

Usage: python3 check_support.py
"""
from fractions import Fraction
from itertools import combinations
from math import gcd


# Rows are |G| times degree times Fourier coefficient, from the A5
# character table with the two 5-cycle classes pooled. The first row
# combines the two degree-three representations.
SIGNED_MASS = ((-90, 0, 72), (0, 80, -96), (75, -100, 0))
CLASS_SIZES = (15, 20, 24)


def candidates():
    for index in range(3):
        yield tuple(int(other == index) for other in range(3))
    # On a two-order support the ratio of the two weights varies on
    # an interval; only axis rays and changes of Fourier sign matter.
    for left, right in combinations(range(3), 2):
        for row in SIGNED_MASS:
            if row[left] * row[right] < 0:
                divisor = gcd(row[left], row[right])
                ray = [0, 0, 0]
                ray[left] = abs(row[right]) // divisor
                ray[right] = abs(row[left]) // divisor
                yield tuple(ray)
    # Once every order is available this weight attains zero.
    yield (1, 1, 1)


def evaluate(weights):
    mass = [sum(w * c for w, c in zip(weights, row)) for row in SIGNED_MASS]
    ratio = Fraction(sum(max(0, x) for x in mass), -sum(min(0, x) for x in mass))
    size = sum(s for s, w in zip(CLASS_SIZES, weights) if w)
    return size, ratio, weights


def main():
    rays = list(map(evaluate, candidates()))
    previous = None
    for budget in range(61):
        permitted = [(ratio, w) for size, ratio, w in rays if size <= budget]
        if not permitted:
            continue
        ratio, weights = min(permitted)
        if previous != ratio:
            print(f"support >= {budget:2d}   minimum {str(ratio):>3}   witness {weights}")
            previous = ratio


if __name__ == "__main__":
    main()
