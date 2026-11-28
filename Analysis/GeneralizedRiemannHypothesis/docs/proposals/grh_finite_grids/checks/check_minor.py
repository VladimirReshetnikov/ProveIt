#!/usr/bin/env python3
"""Exact regressions for the second-order exponent of a compressed product.
Uses Python and SymPy. These coefficient checks are independent of the analytic error proof.
"""
from fractions import Fraction as F
from itertools import permutations, product
from random import Random
from sympy import I, Matrix, eye, zeros


def mul_jets(left, right):
    """Coefficients through degree two of two matrix polynomials."""
    return [
        sum((left[i] * right[k - i] for i in range(k + 1)), zeros(left[0].rows))
        for k in range(3)
    ]


def determinant_jet(product_jet, projection):
    """Truncate the Leibniz determinant of I + P(g(t)-I) over Gaussian rationals."""
    n = projection.rows
    coeffs = [eye(n), projection * product_jet[1], projection * product_jet[2]]
    result = [0, 0, 0]
    for perm in permutations(range(n)):
        inversions = sum(perm[i] > perm[j] for i in range(n) for j in range(i + 1, n))
        term = [(-1)**inversions, 0, 0]
        for row, col in enumerate(perm):
            term = [
                sum(term[k-i] * coeffs[i][row, col] for i in range(k + 1))
                for k in range(3)
            ]
        result = [a + b for a, b in zip(result, term)]
    return result[1], result[2]


def ordered_exponent_jet(generators, projector):
    complement = eye(projector.rows) - projector

    def crossing(a, b):
        return (projector * a * complement * b).trace()

    first = sum((projector * a).trace() for a in generators)
    second = sum(crossing(a, a) for a in generators) / 2
    second += sum(crossing(a, b) for i, a in enumerate(generators) for b in generators[i + 1 :])
    return first, second


def check_jet(matrices, projector):
    n = projector.rows
    assert projector == projector.H and (projector**2 - projector).applyfunc(lambda x: x.expand()) == zeros(n)
    cumulative = [eye(n), zeros(n), zeros(n)]
    for a in matrices:
        cumulative = mul_jets(cumulative, [eye(n), a, a**2 / 2])
    actual = determinant_jet(cumulative, projector)
    linear, quadratic = ordered_exponent_jet(matrices, projector)
    assert (actual[0] - linear).expand() == 0
    assert (actual[1] - quadratic - linear**2 / 2).expand() == 0


def run():
    rng = Random(27011)
    count = 0
    for n in (1, 2, 3):
        # The unitary reflection gives exact real or complex non-coordinate projectors.
        v = Matrix([1 + k * I for k in range(n)])
        h = eye(n) - 2 * (v * v.H) / (v.H * v)[0]
        for rank in range(n + 1):
            projector = (h[:, :rank] * h[:, :rank].H).applyfunc(lambda x: x.expand(complex=True))
            for repeat in range(3):
                generators = [
                    Matrix(n, n, lambda i, j: rng.randint(-2, 2) + I * rng.randint(-1, 1))
                    for _ in range(3)
                ]
                check_jet(generators, projector)
                count += 1
    # All 64 ordered triples of 2-by-2 matrix units test missing and reversed cross terms.
    units = []
    for i, j in product(range(2), repeat=2):
        e = zeros(2)
        e[i, j] = 1
        units.append(e)
    projector = eye(2)[:, :1] * eye(2)[:, :1].T
    for triple in product(units, repeat=3):
        check_jet(triple, projector)
        count += 1
    e12, e21 = units[1:3]
    assert ordered_exponent_jet([e12, e21, zeros(2)], projector)[1] == 1
    assert ordered_exponent_jet([e21, e12, zeros(2)], projector)[1] == 0
    # Asymmetric cubic term: det of compressed exp(te12)exp(te22)exp(te21) = 1+t^2 exp(t).
    e22 = units[3]
    cubic = e12 * e22 * e21
    assert (projector * cubic * projector).trace() == 1
    # Proof constants: exp(3/20) <= (1-3/20)^(-1) <= 6/5; no floating-point estimates.
    assert 1 / (1 - F(3, 20)) <= F(6, 5)
    assert 1 / (1 - F(1, 5)) == F(5, 4)
    assert F(5, 4) * F(6, 5) == F(3, 2)
    assert F(3, 2) * 2 * F(3)**3 / 3 == 27
    print(f"Passed {count} exact Taylor-coefficient checks, including ranks zero and full.")
    print("The ordered matrix-unit witness distinguishes the products in opposite orders.")
    print("The cubic witness has nonzero remainder at degree three.")
    print("The rational majorant arithmetic closes with constant 27.")


if __name__ == "__main__":
    run()
