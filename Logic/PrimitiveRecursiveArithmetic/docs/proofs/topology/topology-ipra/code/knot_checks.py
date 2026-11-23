"""Verify the Fox coloring identities and braid closure counts by enumeration."""

from itertools import product
from math import gcd


def cross(colors, signed_generator, modulus):
    colors = list(colors)
    i = abs(signed_generator) - 1
    x, y = colors[i:i + 2]
    if signed_generator > 0:
        colors[i:i + 2] = ((2*x - y) % modulus, x)
    else:
        colors[i:i + 2] = (y, (2*y - x) % modulus)
    return tuple(colors)


def braid(colors, word, modulus):
    for letter in word:
        colors = cross(colors, letter, modulus)
    return colors


def fixed_vectors(strands, word, modulus):
    return sum(braid(colors, word, modulus) == colors
               for colors in product(range(modulus), repeat=strands))


def check():
    two_strand_tests = 0
    for n in range(1, 13):
        def reflect(x, y):
            return (2*y - x) % n

        for x, y, z in product(range(n), repeat=3):
            assert reflect(x, x) == x
            assert reflect(reflect(x, y), y) == x
            assert reflect(reflect(x, y), z) == reflect(reflect(x, z), reflect(y, z))
            assert (x - y) % n == (reflect(y, x) - x) % n
        for exponent in range(-12, 13):
            word = [1 if exponent > 0 else -1] * abs(exponent)
            assert fixed_vectors(2, word, n) == n * gcd(abs(exponent), n)
            two_strand_tests += 1
        assert fixed_vectors(3, [1, -2]*2, n) == n * gcd(5, n)
        assert fixed_vectors(3, [-1, 2]*2, n) == n * gcd(5, n)
        assert fixed_vectors(3, [-1, -2, 1, -2], n) == n
    print(f"Passed all local identities for moduli 1–12, {two_strand_tests}"
          " two-strand tests, and 36 figure-eight, mirror, and crossing-change tests.")


if __name__ == "__main__":
    check()
