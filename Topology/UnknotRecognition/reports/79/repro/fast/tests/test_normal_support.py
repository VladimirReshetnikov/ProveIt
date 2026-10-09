"""Exact source-support kernels: independent algebra, geometry and forgeries."""

from copy import deepcopy
from fractions import Fraction
from itertools import combinations
import random
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import json_safe
from fastunknot.normal_support import (
    compile_support, compile_normal_support, decode_support,
)
from fastunknot.normal_support_verify import verify_support, verify_normal_support
from fastunknot.normal_surface_geometry import _prepare, _coordinates, NormalOrbitError
from normal_orbit_research.fixtures import (
    layered_torus, boundary_cap, interior_vertex_torus,
)
from tests.test_normal_surface_orbits import relabel


def rational_rank(rows, columns):
    """Dense rational oracle, independent of fraction-free producer arithmetic."""
    matrix = [[Fraction(row.get(i, 0)) for i in columns] for row in rows]
    rank = 0
    for column in range(len(columns)):
        pivot = next((i for i in range(rank, len(matrix)) if matrix[i][column]), None)
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        scale = matrix[rank][column]
        matrix[rank] = [value / scale for value in matrix[rank]]
        for i in range(rank + 1, len(matrix)):
            scale = matrix[i][column]
            matrix[i] = [a - scale * b for a, b in zip(matrix[i], matrix[rank])]
        rank += 1
    return rank


def relation_rows(source):
    """Normal-row-shaped arithmetic identities with at most four unit entries."""
    positive = [i for i, value in enumerate(source) if value]
    candidates = {}
    for left_size, right_size in ((1, 1), (2, 1), (2, 2)):
        for left in combinations(positive, left_size):
            for right in combinations(positive, right_size):
                if set(left) & set(right) or sum(source[i] for i in left) != sum(source[i] for i in right):
                    continue
                row = {i: 1 for i in left}
                row.update({i: -1 for i in right})
                key = tuple(sorted(row.items()))
                negative = tuple((i, -value) for i, value in key)
                candidates[min(key, negative)] = dict(min(key, negative))
    return list(candidates.values())


def algebra_fixture():
    source = [2, 3, 4, 5, 6, 7, 0]
    return {'matching': relation_rows(source)}, {'rows': [source]}


class NormalSupportTests(unittest.TestCase):
    def test_layered_meridians_nullity_one_and_minimum_bits(self):
        for size in (1, 2, 4, 8, 16, 32, 64, 128):
            tri, coordinates = layered_torus(size)
            proof = compile_normal_support(tri, coordinates)
            self.assertEqual(proof['nullity'], 1)
            flat = sum(coordinates, [])
            self.assertEqual(flat[proof['selected'][0]], 1)
            self.assertTrue(verify_normal_support(tri, coordinates, proof))
            prepared = _prepare(tri, lambda: None)
            analysed = _coordinates(prepared, coordinates, lambda: None)
            weight = [flat[i] for i in proof['selected']]
            self.assertEqual(decode_support(analysed, proof, weight), flat)

    def test_empty_space_and_free_columns(self):
        tri, coordinates = layered_torus(3)
        empty = [[0] * 7 for _ in coordinates]
        proof = compile_normal_support(tri, empty)
        self.assertEqual((proof['rank'], proof['nullity']), (0, 0))
        self.assertEqual((proof['support'], proof['selected'], proof['numerators']), ([], [], []))
        self.assertTrue(verify_normal_support(tri, empty, proof))
        self.assertEqual(decode_support({'rows': empty}, proof, []), [0] * 21)
        prepared, analysed = {'matching': []}, {'rows': [[1, 2, 0, 4, 0, 0, 0]]}
        proof = compile_support(prepared, analysed)
        self.assertEqual((proof['rank'], proof['nullity']), (0, 3))
        self.assertTrue(verify_support(prepared, analysed, proof))
        self.assertEqual(decode_support(analysed, proof, [1, 2, 4]), analysed['rows'][0])

    def test_disjoint_vertex_links_mixed_surface_and_boundary_caps(self):
        tri, basis = interior_vertex_torus()
        for coefficients in ((1, 0, 0), (1, 2, 0), (3, 2, 1), (2, 0, 5)):
            coordinates = [[sum(c * basis[name][t][i] for c, name in
                                zip(coefficients, ('sphere', 'boundary_disk', 'mobius')))
                            for i in range(7)] for t in range(4)]
            proof = compile_normal_support(tri, coordinates)
            self.assertTrue(verify_normal_support(tri, coordinates, proof))
            flat = sum(coordinates, [])
            self.assertEqual(decode_support({'rows': coordinates}, proof,
                [flat[i] for i in proof['selected']]), flat)
        tri, coordinates = layered_torus(5)
        for _ in range(3):
            tri, coordinates = boundary_cap(tri, coordinates)
            proof = compile_normal_support(tri, coordinates)
            self.assertEqual(proof['nullity'], 1)
            self.assertTrue(verify_normal_support(tri, coordinates, proof))

    def test_support_reuse_huge_scaling_and_hex_transport(self):
        tri, coordinates = layered_torus(9)
        proof = compile_normal_support(tri, coordinates)
        scale = (1 << 5000) + 1
        large = [[scale * value for value in row] for row in coordinates]
        self.assertTrue(verify_normal_support(tri, json_safe(large), proof))
        flat = sum(large, [])
        weight = json_safe([flat[i] for i in proof['selected']])
        self.assertEqual(decode_support({'rows': large}, proof, weight), flat)

        def hexadecimal(value):
            if type(value) is int:
                return hex(value)
            if type(value) is list:
                return [hexadecimal(item) for item in value]
            if type(value) is dict:
                return {key: hexadecimal(item) for key, item in value.items()}
            return value

        encoded = hexadecimal(proof)
        self.assertTrue(verify_normal_support(tri, large, encoded))
        self.assertEqual(decode_support({'rows': large}, encoded, weight), flat)
        changed = deepcopy(coordinates)
        changed[0][2] = 1
        self.assertFalse(verify_normal_support(tri, changed, proof))

    def test_random_relabellings(self):
        rng = random.Random(261009231)
        tri, coordinates = layered_torus(8)
        for _ in range(24):
            changed, vector = relabel(tri, coordinates, rng)
            proof = compile_normal_support(changed, vector)
            self.assertEqual(proof['nullity'], 1)
            self.assertTrue(verify_normal_support(changed, vector, proof))

    def test_minimum_bit_matroid_basis_against_exhaustive_oracle(self):
        rng = random.Random(261009232)
        for _ in range(100):
            source = rng.choice(([1, 1, 2, 3, 5, 8, 13], [2, 3, 4, 5, 6, 7, 0],
                                 [1, 2, 2, 3, 3, 4, 5], [1, 1, 1, 1, 0, 0, 0]))
            source = rng.sample(source, len(source))
            equations = relation_rows(source)
            rng.shuffle(equations)
            equations = equations[:rng.randrange(len(equations) + 1)]
            prepared, analysed = {'matching': equations}, {'rows': [source]}
            proof = compile_support(prepared, analysed)
            self.assertTrue(verify_support(prepared, analysed, proof))
            support = proof['support']
            rank = rational_rank(equations, support)
            self.assertEqual(proof['rank'], rank)
            best = min(sum(source[i].bit_length() for i in support if i not in pivots)
                       for pivots in combinations(support, rank)
                       if rational_rank(equations, pivots) == rank)
            self.assertEqual(sum(source[i].bit_length() for i in proof['selected']), best)

    def test_nonintegral_decoder_and_composite_moduli(self):
        prepared, analysed = algebra_fixture()
        proof = compile_support(prepared, analysed)
        self.assertEqual(proof['nullity'], 1)
        self.assertGreater(proof['denominator'], 1)
        self.assertTrue(verify_support(prepared, analysed, proof))
        with self.assertRaises(ValueError):
            decode_support(analysed, proof, [1])
        with self.assertRaises(ValueError):
            decode_support(analysed, proof, [-proof['denominator']])
        composite = deepcopy(proof)
        composite['modulus'] = 4
        self.assertTrue(verify_support(prepared, analysed, composite))
        nonunit = deepcopy(proof)
        nonunit['modulus'] = 6
        self.assertFalse(verify_support(prepared, analysed, nonunit))

    def test_forgeries_and_strict_types(self):
        prepared, analysed = algebra_fixture()
        proof = compile_support(prepared, analysed)
        mutations = []
        for field, value in (('rank', True), ('nullity', 2), ('denominator', 0),
                             ('modulus', 1), ('selected', [100]), ('pivot_rows', [-1] * proof['rank']),
                             ('support', [True] + proof['support'][1:]),
                             ('pivots', proof['pivots'][:-1]), ('numerators', [])):
            changed = deepcopy(proof)
            changed[field] = value
            mutations.append(changed)
        for invalid in (True, 1.0, '1', None, '0xno'):
            changed = deepcopy(proof)
            changed['numerators'][0][0] = invalid
            mutations.append(changed)
        changed = deepcopy(proof)
        changed['numerators'][0][0] += 1
        mutations.append(changed)
        changed = deepcopy(proof)
        changed['denominator'] += 1
        mutations.append(changed)
        changed = deepcopy(proof)
        changed['unused'] = 1
        mutations.append(changed)
        changed = deepcopy(proof)
        changed['pivot_rows'][0] = changed['pivot_rows'][1]
        mutations.append(changed)
        for changed in mutations:
            self.assertFalse(verify_support(prepared, analysed, changed), changed)

    def test_independent_replay_and_cancellation(self):
        tri, coordinates = layered_torus(12)
        proof = compile_normal_support(tri, coordinates)
        with patch('fastunknot.normal_support.compile_support', side_effect=AssertionError), \
             patch('fastunknot.normal_support._fraction_free', side_effect=AssertionError), \
             patch('fastunknot.normal_support.decode_support', side_effect=AssertionError):
            self.assertTrue(verify_normal_support(tri, coordinates, proof))
        for error in (RuntimeError, ValueError, NormalOrbitError):
            count = [0]

            def cancel():
                count[0] += 1
                if count[0] == 60:
                    raise error('external cancellation')

            with self.assertRaises(error):
                verify_normal_support(tri, coordinates, proof, check=cancel)
        prepared = _prepare(tri, lambda: None)
        analysed = _coordinates(prepared, coordinates, lambda: None)
        for operation in (lambda callback: compile_support(prepared, analysed, callback),
                          lambda callback: verify_support(prepared, analysed, proof, callback),
                          lambda callback: decode_support(analysed, proof, [1], callback)):
            count = [0]

            def cancel_later():
                count[0] += 1
                if count[0] == 8:
                    raise ValueError('late cancellation')

            with self.assertRaisesRegex(ValueError, 'late cancellation'):
                operation(cancel_later)


if __name__ == '__main__':
    unittest.main()
