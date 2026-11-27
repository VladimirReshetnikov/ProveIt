#!/usr/bin/env python3
"""Verify four single-time collisions by exact arithmetic in cyclotomic rings.

Run with Python 3: python3 gauss-check.py
Polynomials are stored in order of increasing degree. For each discriminant
d, the two multisets put one atom at the roots with character +1 and -1,
respectively. Their Li exponents differ by -G(n). The identities checked
below imply coincident laws at t = 2*pi/sqrt(|d|) and its integer multiples.
"""

# d, values of the primitive quadratic character on 0,...,|d|-1, Phi_|d|
EXAMPLES = [
    (-3, [0, 1, -1], [1, 1, 1]),
    (-4, [0, 1, 0, -1], [1, 0, 1]),
    (-7, [0, 1, 1, -1, 1, -1, -1], [1] * 7),
    (-8, [0, 1, 0, 1, 0, -1, 0, -1], [1, 0, 0, 0, 1]),
]


def reduce_polynomial(coeffs, modulus):
    """Return the canonical remainder modulo the monic polynomial modulus."""
    coeffs = list(coeffs)
    degree = len(modulus) - 1
    for i in range(len(coeffs) - 1, degree - 1, -1):
        leading = coeffs[i]
        for j in range(degree + 1):
            coeffs[i - degree + j] -= leading * modulus[j]
    return (coeffs + [0] * degree)[:degree]


def gauss_sum(character, n, modulus):
    order = len(character)
    coeffs = [0] * order
    for j, value in enumerate(character):
        coeffs[(n * j) % order] += value
    return reduce_polynomial(coeffs, modulus)


def check(discriminant, character, modulus):
    order = abs(discriminant)
    if len(character) != order or sum(character) != 0:
        raise ValueError("invalid character table")

    gauss_one = gauss_sum(character, 1, modulus)
    for n, value in enumerate(character):
        if gauss_sum(character, n, modulus) != [value * c for c in gauss_one]:
            raise ArithmeticError(f"Fourier identity failed for d={discriminant}, n={n}")

    square = [0] * (2 * len(gauss_one) - 1)
    for i, left in enumerate(gauss_one):
        for j, right in enumerate(gauss_one):
            square[i + j] += left * right
    if reduce_polynomial(square, modulus) != reduce_polynomial([discriminant], modulus):
        raise ArithmeticError(f"Gauss square failed for d={discriminant}")
    positive = [j for j, value in enumerate(character) if value == 1]
    negative = [j for j, value in enumerate(character) if value == -1]
    print(f"d={discriminant:2d}  positive={positive}  negative={negative}"
          f"  checked all {order} frequencies and G(1)^2={discriminant}")


if __name__ == "__main__":
    for example in EXAMPLES:
        check(*example)
