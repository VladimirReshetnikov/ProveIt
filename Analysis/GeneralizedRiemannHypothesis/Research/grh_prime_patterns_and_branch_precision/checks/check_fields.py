"""Exact congruences and masses for the two number-field constructions."""
from fractions import Fraction
from math import isqrt, prod


def relative_gain(marker, satellites):
    delta = prod(satellites) * (marker**2 * (1 + sum(satellites)) - (1 + marker))
    original = (1 + marker) * prod(1 + u for u in satellites)
    return delta, delta / original


if __name__ == '__main__':
    assert all(431 % d for d in range(2, isqrt(431)+1))
    assert pow(2, 43, 431) == pow(3, 43, 431) == 1
    w = Fraction(1, 2)
    examples = [(9*[w] + 2*[Fraction(1, 3)], 110592, 11337408),
                (11*[w], 16384, 2125764)]
    for satellites, a, b in examples:
        absolute, relative = relative_gain(w, satellites)
        assert (absolute, relative) == (Fraction(1, a), Fraction(1, b))
        print(f"Added digit mass {absolute}; relative density gain {relative}.")
    print("431 prime; residues 2^43 and 3^43 modulo 431 are both 1.")
