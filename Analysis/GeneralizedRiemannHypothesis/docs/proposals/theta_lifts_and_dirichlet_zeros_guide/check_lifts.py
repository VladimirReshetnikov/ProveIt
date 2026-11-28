"""Exact finite examples for the first reading, curve analogy, and compression."""
from itertools import product
from math import comb
from fractions import Fraction


def curve_count(quadratic):
    # a + b*u in F_5[u]/(u^2-2); 2 is a quadratic nonresidue.
    field = list(product(range(5), range(5) if quadratic else [0]))

    def mul(z, w):
        a, b = z
        c, d = w
        return (a*c + 2*b*d) % 5, (a*d + b*c) % 5

    affine = 0
    for x in field:
        r, s = mul(mul(x, x), x)
        rhs = (r + x[0] + 1) % 5, (s + x[1]) % 5
        affine += sum(mul(y, y) == rhs for y in field)
    return 1 + affine


def gram(columns):
    return [[sum(a*b for a, b in zip(v, w)) for w in columns] for v in columns]


def det(matrix):
    return matrix[0][0]*matrix[1][1] - matrix[0][1]*matrix[1][0]


def main():
    assert comb(12, 6) == 2**2 * 3 * 7 * 11 == 924
    assert [a for a in range(7) if pow(a, 3, 7) == 1] == [1, 2, 4]
    assert curve_count(False) == 9 and curve_count(True) == 27
    u = [(1, 1, 0), (0, 0, 2)]
    projected = [(a, 0, c) for a, _, c in u]
    measured_ratio = det(gram(projected)) / Fraction(det(gram(u)))
    assert measured_ratio == Fraction(1, 2)
    assert (det(gram(u)), det(gram(projected))) == (8, 4)
    print('Checked the binomial coefficient, finite-field point counts, and Gram compression.')


if __name__ == '__main__':
    main()
