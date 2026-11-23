"""Exhaustive small checks for the finite coloring arguments (standard library)."""

from itertools import product
from math import gcd


def braid_action(word, row, modulus, parameter=-1):
    """A signed letter k acts on positions |k| and |k|+1 (1-based)."""
    row = list(row)
    inverse = pow(parameter, -1, modulus)
    for letter in word:
        i = abs(letter) - 1
        x, y = row[i : i + 2]
        if letter > 0:
            row[i : i + 2] = [((1 - parameter) * x + parameter * y) % modulus, x]
        else:
            row[i : i + 2] = [y, (inverse * x + (1 - inverse) * y) % modulus]
    return tuple(row)


def closed_count(width, word, modulus, parameter=-1):
    rows = product(range(modulus), repeat=width)
    return sum(braid_action(word, row, modulus, parameter) == row for row in rows)


def rational_closure_counts(word, modulus):
    """Trace both physical strands, independent of the integer slope update."""
    numerator = denominator = 0
    for north, south in product(range(modulus), repeat=2):
        a, b, c, d = north, north, south, south
        for event in word:
            if event == "+":
                b, c = c, (2 * c - b) % modulus
            elif event == "-":
                b, c = (2 * b - c) % modulus, b
            else:
                a, b, c, d = d, a, b, c
        numerator += a == b and c == d
        denominator += a == d and b == c
    return numerator, denominator


def rational_fraction_pair(word):
    p, q = 0, 1
    for event in word:
        if event == "+":
            p += q
        elif event == "-":
            p -= q
        else:
            p, q = -q, p
    return p, q


def run_checks():
    comparisons = 0
    for modulus in range(2, 11):
        for crossings in range(-8, 9):
            word = (1 if crossings >= 0 else -1,) * abs(crossings)
            assert closed_count(2, word, modulus) == modulus * gcd(modulus, abs(crossings))
            comparisons += 1
        assert closed_count(3, (1, -2) * 2, modulus) == modulus * gcd(modulus, 5)
        comparisons += 1

    for modulus in range(2, 6):
        for width in range(1, 6):
            block = tuple(range(1, width))
            for repeat in range(1, 8):
                if gcd(width, repeat) != 1:
                    continue
                if repeat % 2 == 0:
                    expected = modulus * gcd(modulus, width)
                elif width % 2 == 0:
                    expected = modulus * gcd(modulus, repeat)
                else:
                    expected = modulus
                assert closed_count(width, block * repeat, modulus) == expected
                comparisons += 1

    rational_comparisons = 0
    for length in range(5):
        for word in product("+-R", repeat=length):
            p, q = rational_fraction_pair(word)
            for modulus in range(2, 8):
                expected = modulus * gcd(modulus, abs(p)), modulus * gcd(modulus, abs(q))
                assert rational_closure_counts(word, modulus) == expected
                rational_comparisons += 2

    row = (0, 1, 6)
    expected_rows = [(7, 11, 0), (4, 20, 7), (23, 25, 4), (6, 14, 23), (0, 1, 6)]
    for expected in expected_rows:
        row = braid_action((1, 2), row, 31, 7)
        assert row == expected
    assert closed_count(3, (1, 2) * 5, 31, 7) == 31**2
    print(f"{comparisons} Fox count comparisons passed.")
    print(f"{rational_comparisons} rational closure comparisons passed.")
    print("The affine T(3,5) witness and the exhaustive count of 961 agree.")


if __name__ == "__main__":
    run_checks()
