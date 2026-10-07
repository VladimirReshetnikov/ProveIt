#!/usr/bin/env python3
"""Deterministic positive and corruption tests; also run with Python -O."""
import argparse
import copy
import itertools
import json
import random
from fractions import Fraction as F
from pathlib import Path
import certify_rational_circle as c


def reject(name, function, fragment):
    try:
        function()
    except ArithmeticError as error:
        c.require(fragment in str(error), name + ': wrong rejection reason')
        return {'test': name, 'result': 'rejected', 'reason': str(error)}
    raise ArithmeticError(name + ': corrupted input was accepted')


def naive_determinant(matrix):
    n = len(matrix)
    total = 0
    for permutation in itertools.permutations(range(n)):
        inversions = sum(permutation[i] > permutation[j]
                         for i in range(n) for j in range(i + 1, n))
        term = (-1)**inversions
        for i in range(n):
            term *= matrix[i][permutation[i]]
        total += term
    return total


def multiply_coefficients(p, factor):
    out = [0]*(len(p) + len(factor) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(factor):
            out[i + j] += a*b
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent/'data'
    data = json.loads((root/'N_H8.json').read_text())
    ad = json.loads((root/'adjugate_H8.json').read_text())
    p, vs = c.validate_data(data, ad)
    raw = c.polynomial_matrix(vs, False)
    gauged = c.polynomial_matrix(vs, True)
    tests = []

    rng = random.Random(394326)
    for size in range(5):
        for _ in range(25):
            matrix = [[rng.randrange(-3, 4) for _ in range(size)] for _ in range(size)]
            c.require(c.bareiss_integer_determinant(matrix) == naive_determinant(matrix),
                      'Bareiss disagrees with independent permutation determinant')
    # Force a pivot swap, a zero first column, and a rank-deficient later pivot.
    for matrix in [[[0, 2], [3, 4]], [[0, 1], [0, 2]],
                   [[1, 2, 3], [2, 4, 6], [4, 5, 6]]]:
        c.require(c.bareiss_integer_determinant(matrix) == naive_determinant(matrix),
                  'Bareiss exceptional pivot test failed')
    tests.append({'test': 'Bareiss versus independent Leibniz determinant',
                  'result': 'PASS', 'cases': 128})

    for _ in range(40):
        a, b, d = rng.randrange(-8, 9), rng.randrange(-8, 9), rng.randrange(1, 9)
        poly = [rng.randrange(-5, 6) for _ in range(7)]
        real, imag = F(0), F(0)
        for coefficient in reversed(poly):
            real, imag = (real*F(a, d) - imag*F(b, d) + coefficient,
                          real*F(b, d) + imag*F(a, d))
        x, y, den = c.evaluate_complex_integer(poly, a, b, d)
        c.require(F(x, den) == real and F(y, den) == imag,
                  'common-denominator Horner disagrees with Fraction arithmetic')
    tests.append({'test': 'integer complex Horner versus Fraction arithmetic',
                  'result': 'PASS', 'cases': 40})

    # Intersections have genuinely different coordinate denominators.
    for v, w in [((2, -3, 7), (5, 11, 13)), ((-2, -3, 7), (-5, 11, 13)),
                 ((11, 3, 19), (-7, -9, 23))]:
        x1, y1 = F(v[0], v[2]), F(v[1], v[2])
        x2, y2 = F(w[0], w[2]), F(w[1], w[2])
        intercept = x1 + (x2 - x1)*(-y1)/(y2 - y1)
        result = c.crossing(v, w)
        c.require(result == (1 if y1 < 0 else -1, c.sign(intercept)),
                  'integer crossing disagrees with Fraction intersection')
    tests.append({'test': 'crossing formula with unequal denominators',
                  'result': 'PASS', 'cases': 3})

    malformed = copy.deepcopy(ad)
    malformed['states'][0], malformed['states'][1] = malformed['states'][1], malformed['states'][0]
    tests.append(reject('permuted finite state list', lambda: c.validate_data(data, malformed),
                        'incomplete or misordered'))
    broken = copy.deepcopy(ad)
    broken['adjugate'][0][0] += 1
    tests.append(reject('perturbed adjugate coefficient', lambda: c.verify_adjugate(gauged, broken),
                        'adjugate polynomial identity failed'))

    # The critical adversarial example: an extra common polynomial factor
    # preserves the entire matrix adjugate identity, but is not the determinant.
    inflated = copy.deepcopy(ad)
    inflated['den'] = multiply_coefficients(ad['den'], [1, 0, 1])
    inflated['adjugate'] = [multiply_coefficients(entry, [1, 0, 1])
                           for entry in ad['adjugate']]
    c.verify_adjugate(gauged, inflated)
    tests.append(reject('extraneous common factor (1+q), despite passing adjugate identity',
                        lambda: c.verify_genuine_determinant(raw, multiply_coefficients(p, [1, 1])),
                        'genuine determinant identity failed'))
    wrong_p = p[:]
    wrong_p[17] += 1
    tests.append(reject('changed interior polynomial coefficient',
                        lambda: c.verify_genuine_determinant(raw, wrong_p),
                        'genuine determinant identity failed'))

    node = next(c.rational_nodes(c.MESH_PER_QUADRANT))
    tests.append(reject('off-circle rational node',
                        lambda: c.verify_node_on_circle(node[0] + 1, node[1], node[2]),
                        'off circle'))
    tests.append(reject('node below modulus threshold',
                        lambda: c.verify_node_value((1, 1, 1000)),
                        'modulus threshold failed'))
    tests.append(reject('vertex on ray', lambda: c.verify_node_value((1, 0, 1)),
                        'zero imaginary part'))
    tests.append(reject('edge through zero', lambda: c.crossing((-1, -1, 1), (2, 2, 2)),
                        'edge meets origin'))
    tests.append(reject('insufficient mesh', lambda: c.verify_circle(p, 16),
                        'mesh too coarse'))

    square = [(1, 1, 1), (-1, 1, 1), (-1, -1, 1), (1, -1, 1)]
    c.polygon_winding(square)
    tests.append(reject('reversed contour orientation',
                        lambda: c.polygon_winding(list(reversed(square))),
                        'winding count failed'))
    tests.append(reject('deleted vertex creates origin-crossing closing chord',
                        lambda: c.polygon_winding(square[:-1]),
                        'edge meets origin'))
    output = {'status': 'PASS', 'tests': tests,
              'note': 'All rejection guards are explicit and remain active under python -O.'}
    text = json.dumps(output, indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
