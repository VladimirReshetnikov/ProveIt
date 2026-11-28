#!/usr/bin/env python3
"""Exact finite checks for the examples in the exposition. Uses only Python 3."""
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import product
from math import gcd


def require(actual, expected, label):
    if actual != expected:
        raise AssertionError(f"{label}: got {actual!r}, expected {expected!r}")


def check_residue_fibres():
    units = [n for n in range(21) if gcd(n, 21) == 1]
    source = [n for n in units if n % 3 == 1]
    marked = {2, 11}
    require(source, [1, 4, 10, 13, 16, 19], "fibre above 1")
    for n in units:
        count = sum((-n * tau) % 21 in marked for tau in source)
        require(count, len(marked) if n % 3 == 1 else 0, f"partner places for {n}")


def check_fourier_path():
    # In the three-vertex path, each nonzero residue occurs equally often.
    # Thus a nontrivial Fourier coefficient is count[0] - count[1] exactly.
    for prime in (2, 3, 5, 7, 11):
        counts = Counter((y * (x + z)) % prime
                         for x, y, z in product(range(prime), repeat=3))
        require(counts[0], 2 * prime**2 - prime, f"zero-path count modulo {prime}")
        for residue in range(1, prime):
            require(counts[residue], prime**2 - prime, "nonzero-path count")
        require(counts[0] - counts[1], prime**2, "nontrivial Fourier coefficient")


def elliptic_derivative(poly):
    # Monomials x^i y^j, with j=0 or 1. Reduce y^2 to x^3-x.
    output = defaultdict(int)
    for (i, j), coeff in poly.items():
        if j == 0:
            if i:
                output[i - 1, 1] += 2 * i * coeff
        else:
            output[i + 2, 0] += (2 * i + 3) * coeff
            output[i, 0] -= (2 * i + 1) * coeff
    return {exponent: c for exponent, c in output.items() if c}


def check_elliptic_curve():
    for start in (((1, 0), "x"), ((0, 1), "y")):
        generator, name = start
        derivatives = [{generator: 1}]
        for _ in range(5):
            derivatives.append(elliptic_derivative(derivatives[-1]))
        if name == "x":
            require(derivatives[3], {(1, 1): 24}, "D^3 x")
            require(derivatives[5], {(2, 1): 720, (0, 1): -144}, "D^5 x")
        else:
            require(derivatives[3], {(3, 0): 60, (1, 0): -36}, "D^3 y")
        require(all(n % 3 == 0 for n in derivatives[3].values()), True, "D^3 modulo 3")
        for term in set(derivatives[1]) | set(derivatives[5]):
            require((derivatives[5].get(term, 0) - 3 * derivatives[1].get(term, 0)) % 5,
                    0, "D^5 = 3D modulo 5")


def check_projection():
    projector = ((Fraction(1, 10), Fraction(3, 10)),
                 (Fraction(3, 10), Fraction(9, 10)))
    squared = tuple(tuple(sum(projector[i][k] * projector[k][j] for k in range(2))
                          for j in range(2)) for i in range(2))
    require(squared, projector, "orthogonal projector is idempotent")
    for vec, expected in (((1, 3), (1, 3)), ((-3, 1), (0, 0))):
        result = tuple(sum(row[j] * vec[j] for j in range(2)) for row in projector)
        require(result, expected, "projector action")


def check_twist_exponent():
    beta = Fraction(3, 4)
    delta = (beta - Fraction(1, 2)) / 9
    require(delta, Fraction(1, 36), "density parameter")
    require((2 + delta - 2 * delta) / 2, Fraction(71, 72), "exceptional primes exponent")


if __name__ == "__main__":
    for check in (check_residue_fibres, check_fourier_path, check_elliptic_curve,
                  check_projection, check_twist_exponent):
        check()
        print(f"Passed {check.__name__[6:].replace('_', ' ')}")
