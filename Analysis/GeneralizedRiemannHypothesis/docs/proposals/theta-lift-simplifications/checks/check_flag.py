#!/usr/bin/env python3
"""Exact arithmetic checks for a flag-adapted integral clearing operator.

Run with Python 3.10+ and its standard library. The rational-number examples
use the valuation v_p normalized by v_p(p)=1 and never use a numerical norm.
Vectors in the embedding are columns; matrices acting on coordinates have
their usual row-by-column convention.
"""
from fractions import Fraction as Q
from itertools import permutations, product
from math import inf, prod
from random import Random


def valuation(x, p):
    if not x:
        return inf
    x = Q(x)
    n, d, count = abs(x.numerator), x.denominator, 0
    while n % p == 0:
        count += 1
        n //= p
    while d % p == 0:
        count -= 1
        d //= p
    return count


def min_valuation(v, p):
    return min((valuation(t, p) for t in v), default=inf)


def linear_combination(columns, coefficients):
    return [sum(x * c for x, c in zip(row, coefficients)) for row in zip(*columns)]


def subtract_multiple(v, c, w):
    return [x - c * y for x, y in zip(v, w)]


def adapted_basis(columns, p):
    """Choose an integral unit-pivot column for every step of the given flag."""
    basis, pivots = [], []
    for source in columns:
        residual = list(source)
        for pivot, vector in zip(pivots, basis):
            residual = subtract_multiple(residual, residual[pivot], vector)
        pivot = min(range(len(residual)), key=lambda a: valuation(residual[a], p))
        assert residual[pivot] and pivot not in pivots
        scale = Q(1, 1) / residual[pivot]
        vector = [scale * x for x in residual]
        assert vector[pivot] == 1 and all(vector[t] == 0 for t in pivots)
        assert min_valuation(vector, p) == 0
        basis.append(vector)
        pivots.append(pivot)
    return basis, pivots


def coordinates(v, basis, pivots):
    residual = list(v)
    coeffs = []
    for pivot, vector in zip(pivots, basis):
        c = residual[pivot]
        coeffs.append(c)
        residual = subtract_multiple(residual, c, vector)
    assert all(t == 0 for t in residual)
    return coeffs


def unit_vector(d, j):
    return [Q(int(i == j)) for i in range(d)]


def action(matrix, v):
    return [sum(c * x for c, x in zip(row, v)) for row in matrix]


def determinant(matrix):
    # Independent permutation formula, including det(empty matrix)=1.
    total = 0
    for perm in permutations(range(len(matrix))):
        inversions = sum(i > j for a, i in enumerate(perm) for j in perm[a + 1:])
        total += (-1)**inversions * prod(row[j] for row, j in zip(matrix, perm))
    return total


def prepare(columns, eigenvalues, p):
    """Express operators given in an eigenbasis in the integral flag basis."""
    d = len(columns)
    basis, pivots = adapted_basis(columns, p)
    # The change of basis has upper-triangular columns: z_j in b coordinates.
    z_in_b = [coordinates(v, basis, pivots) for v in columns]
    b_in_z = []
    for j in range(d):
        residual = unit_vector(d, j)
        c = [Q(0)] * d
        for k in reversed(range(d)):
            c[k] = residual[k] / z_in_b[k][k]
            residual = subtract_multiple(residual, c[k], z_in_b[k])
        assert not any(residual)
        b_in_z.append(c)

    matrices = []
    for lambdas in eigenvalues:
        image_columns = [
            linear_combination(z_in_b, [v * a for v, a in zip(c, lambdas)])
            for c in b_in_z
        ]
        matrix = [list(row) for row in zip(*image_columns)]
        for i, row in enumerate(matrix):
            assert row[i] == lambdas[i]
            assert all(row[j] == 0 for j in range(i))
        matrices.append(matrix)

    chosen_rows = [matrices[j][j] for j in range(d)]
    assert determinant(chosen_rows) == prod(eigenvalues[j][j] for j in range(d))
    return basis, pivots, matrices, chosen_rows


def example_with_projection():
    # Z = span(b1,b2), and the ordinary rational orthogonal projection of e2
    # onto Z is b2/2. The two given operators send it to integral vectors.
    b1, b2 = [Q(1), Q(0), Q(0)], [Q(0), Q(1), Q(1)]
    z2 = [x + 2*y for x, y in zip(b1, b2)]
    basis, pivots, matrices, result = prepare([b1, z2], [[4, 4], [2, 2]], 2)
    assert basis == [b1, b2]
    y = [Q(0), Q(1), Q(0)]
    projection = [Q(0), Q(1, 2), Q(1, 2)]
    assert all(sum((a-b)*c for a, b, c in zip(y, projection, v)) == 0 for v in basis)
    x = coordinates(projection, basis, pivots)
    assert all(min_valuation(action(g, x), 2) >= 0 for g in matrices)
    assert action(result, x) == [0, 1]
    assert determinant(result) == 8
    # Gluing in the nonintegral eigenbasis instead would form diag(4,2)
    # there.  x = -z1/4 + z2/4 would map to -z1 + z2/2.
    naive = linear_combination([b1, z2], [-1, Q(1, 2)])
    assert min_valuation(naive, 2) == -1
    # Our operator need not preserve the Hecke eigenspaces.
    assert action(result, coordinates(z2, basis, pivots)) == [4, 4]


def finite_residue_example():
    diag_g, diag_h = [1, 0, 1], [0, 1, 1]
    for u, v in product(range(2), repeat=2):
        assert any((u*a + v*b) % 2 == 0 for a, b in zip(diag_g, diag_h))
    _, _, _, result = prepare([unit_vector(3, j) for j in range(3)],
                                [diag_g, diag_h, diag_g], 2)
    assert determinant(result) == 1


def random_case(rng, p, d, negatives):
    # Embed a d-plane as the graph of an integral map, then permute the
    # ambient coordinates. Generate the eigenflag by a random rational basis
    # change.  Distinct scales and collinear reductions test delicate pivots.
    n = d + 2
    ambient_basis = [unit_vector(d, i) + [Q(rng.randint(-4, 4)) for _ in range(2)]
                     for i in range(d)]
    order = list(range(n))
    rng.shuffle(order)
    ambient_basis = [[v[i] for i in order] for v in ambient_basis]
    change = [unit_vector(d, j) for j in range(d)]
    for _ in range(3 * d):
        if d > 1:
            j, k = rng.sample(range(d), 2)
            c = Q(rng.randint(-5, 5)) * Q(p)**rng.randint(-2, 2)
            change[j] = subtract_multiple(change[j], c, change[k])
    columns = [linear_combination(ambient_basis, [x * Q(p)**(j-2) for x in v])
               for j, v in enumerate(change)]
    values = []
    for j in range(d):
        row = [Q(rng.choice([-1, 1])) * Q(p)**rng.randint(-2 if negatives else 1, 4)
               for _ in range(d)]
        if d > 1:
            row[(j+1) % d] = Q(0)  # Every individual operator is singular.
        values.append(row)
    basis, pivots, matrices, result = prepare(columns, values, p)
    if d > 1:
        assert all(determinant(g) == 0 for g in matrices)

    # Choose a scale for arbitrary test vectors at which every G_i clears.
    # Some of the resulting vectors have nonintegral coordinates themselves.
    nonintegral_inputs = 0
    for _ in range(12):
        raw = [Q(rng.randint(-5, 5)) * Q(p)**rng.randint(-2, 2) for _ in range(d)]
        if not any(raw):
            raw[0] = Q(1)
        images = [action(g, raw) for g in matrices]
        smallest = min(min_valuation(v, p) for v in images)
        assert smallest != inf  # Some G_i detects each eigendirection.
        x = [a * Q(p)**(-smallest) for a in raw]
        ambient_x = linear_combination(basis, x)
        assert coordinates(ambient_x, basis, pivots) == x
        assert min_valuation(ambient_x, p) == min_valuation(x, p)
        nonintegral_inputs += min_valuation(x, p) < 0
        images = [action(g, x) for g in matrices]
        assert all(min_valuation(linear_combination(basis, v), p) >= 0 for v in images)
        output = action(result, x)
        assert output == [v[j] for j, v in enumerate(images)]
        assert min_valuation(linear_combination(basis, output), p) >= 0
    return nonintegral_inputs


def main():
    assert determinant([]) == 1
    finite_residue_example()
    example_with_projection()
    rng = Random(20261127)
    count = nonintegral = 0
    for p, d, negatives in product([2, 3, 5, 7], range(1, 6), [False, True]):
        for _ in range(3):
            nonintegral += random_case(rng, p, d, negatives)
            count += 1
    assert nonintegral > 0
    print('PASS  empty determinant, finite residue obstruction, actual orthogonal projection')
    print(f'PASS  {count} exact rational flag examples over 4 prime valuations; ranks 1 through 5')
    print(f'PASS  {12*count} admissible inputs, including {nonintegral} nonintegral before clearing')


if __name__ == '__main__':
    main()
