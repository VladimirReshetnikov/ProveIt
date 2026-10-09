"""Exact cone duals, independent sector replay, and exhaustive small oracles."""

from copy import deepcopy
from fractions import Fraction
from itertools import combinations, product
import json
from math import gcd
import random
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from fastunknot.exact_lp import solve_nonnegative_kernel
from fastunknot.integer_codec import json_safe
from fastunknot.normal_euler import decide_sector_euler, _euler_model
from fastunknot.normal_euler_verify import verify_sector_euler_certificate, _reference_model
from fastunknot.normal_sector import build_sector_kernel, sector_rays, _nullspace
from fastunknot.normal_surface_geometry import _coordinates
from normal_orbit_research.fixtures import layered_torus, interior_vertex_torus, boundary_cap


def fraction(pair):
    def integer(x):
        return int(x, 16) if isinstance(x, str) else x
    return Fraction(integer(pair[0]), integer(pair[1]))


def exhaustive_positive(matrix, objective):
    n = len(objective)
    for size in range(1, n+1):
        for selected in combinations(range(n), size):
            null = _nullspace([[row[j] for j in selected] for row in matrix], size)
            if len(null) != 1:
                continue
            vector = null[0]
            if all(x < 0 for x in vector):
                vector = [-x for x in vector]
            if all(x > 0 for x in vector) and sum(objective[j]*x
                                                 for j, x in zip(selected, vector)) > 0:
                return True
    return False


class ExactKernelLPTests(unittest.TestCase):
    def assert_replay(self, matrix, objective, result):
        if result['status'] == 'POSITIVE':
            x = list(map(fraction, result['x']))
            self.assertTrue(all(value >= 0 for value in x))
            self.assertEqual(sum(x), 1)
            self.assertTrue(all(sum(a*b for a, b in zip(row, x)) == 0 for row in matrix))
            value = sum(a*b for a, b in zip(objective, x))
            self.assertGreater(value, 0)
            self.assertEqual(value, fraction(result['objective']))
            primitive = result['primitive_x']
            self.assertEqual([Fraction(a, sum(primitive)) for a in primitive], x)
            common = 0
            for a in primitive:
                common = gcd(common, a)
            self.assertEqual(common, 1)
            active = [j for j, value in enumerate(x) if value]
            self.assertEqual(len(_nullspace([[row[j] for j in active]
                                             for row in matrix], len(active))), 1)
        else:
            self.assertEqual(result['status'], 'NONPOSITIVE')
            y = list(map(fraction, result['y']))
            self.assertEqual(len(y), len(matrix))
            self.assertTrue(all(sum(row[j]*value for row, value in zip(matrix, y)) >= c
                                for j, c in enumerate(objective)))

    def test_exhaustive_support_oracle_on_degenerate_random_cones(self):
        rng = random.Random(261009483)
        for _ in range(240):
            n, m = rng.randrange(1, 6), rng.randrange(5)
            matrix = [[rng.randrange(-3, 4) for _ in range(n)] for _ in range(m)]
            objective = [rng.randrange(-4, 5) for _ in range(n)]
            result = solve_nonnegative_kernel(matrix, objective)
            self.assert_replay(matrix, objective, result)
            self.assertEqual(result['status'] == 'POSITIVE', exhaustive_positive(matrix, objective))

    def test_zero_width_redundant_equations_and_fractional_input(self):
        for matrix, objective in (([], []), ([[], []], []), ([], [0, -1]),
                                  ([[0, 0], [1, -2], [2, -4]], [Fraction(-1, 2), 0]),
                                  ([[Fraction(1, 2), -1]], [1, 0])):
            result = solve_nonnegative_kernel(matrix, objective)
            self.assert_replay(matrix, objective, result)
        self.assertEqual(solve_nonnegative_kernel([[[1, 2], -1]], [1, 0])['primitive_x'], [2, 1])

    def test_binary_magnitude_and_exact_json_transport(self):
        huge = 1 << 20000
        matrix, objective = [[1, -huge]], [1, 0]
        result = solve_nonnegative_kernel(matrix, objective)
        self.assertEqual(result['primitive_x'], [huge, 1])
        self.assert_replay(matrix, objective, result)
        transported = json.loads(json.dumps(json_safe(result)))
        self.assertEqual(list(map(fraction, transported['x'])), list(map(fraction, result['x'])))
        result = solve_nonnegative_kernel([[huge, -1]], [1, -1])
        self.assert_replay([[huge, -1]], [1, -1], result)
        self.assertEqual(list(map(fraction, json.loads(json.dumps(json_safe(result)))['y'])),
                         list(map(fraction, result['y'])))

    def test_caps_validation_immutability_and_cancellation(self):
        matrix, objective = [[1, -1]], [1, 0]
        original = deepcopy((matrix, objective))
        complete = solve_nonnegative_kernel(matrix, objective)
        cap = complete['stats']['pivots']
        self.assertEqual(solve_nonnegative_kernel(matrix, objective, max_pivots=cap), complete)
        partial = solve_nonnegative_kernel(matrix, objective, max_pivots=cap-1)
        self.assertEqual(partial['status'], 'INCONCLUSIVE')
        self.assertNotIn('x', partial)
        self.assertNotIn('y', partial)
        for bad_matrix, bad_objective in (([[1]], [1, 2]), ([[True]], [1]),
                                          ([[1.0]], [1]), ([[[1, 0]]], [1]),
                                          ([[1]], [False])):
            with self.assertRaises(ValueError):
                solve_nonnegative_kernel(bad_matrix, bad_objective)
        for cap in (-1, True, 2.0):
            with self.assertRaises(ValueError):
                solve_nonnegative_kernel(matrix, objective, max_pivots=cap)
        calls = [0]
        def count():
            calls[0] += 1
        solve_nonnegative_kernel(matrix, objective, check=count)
        for stop in (1, calls[0]//2, calls[0]):
            current = [0]
            def cancel():
                current[0] += 1
                if current[0] == stop:
                    raise RuntimeError('cancelled')
            with self.assertRaisesRegex(RuntimeError, 'cancelled'):
                solve_nonnegative_kernel(matrix, objective, check=cancel)
        self.assertEqual((matrix, objective), original)


class SectorEulerTests(unittest.TestCase):
    def test_all_small_layered_sectors_against_q_ray_enumeration(self):
        for n in range(1, 5):
            raw, meridian = layered_torus(n)
            for choices in product(range(-1, 3), repeat=n):
                support = [(t, q) for t, q in enumerate(choices) if q >= 0]
                kernel = build_sector_kernel(raw, support)
                expected = any(_coordinates(kernel.prepared, rows, lambda: None)
                               ['euler_characteristic'] > 0
                               for rows in sector_rays(kernel, phase='quadrilateral'))
                for strategy in ('anchors', 'envelope'):
                    result = decide_sector_euler(raw, support, strategy=strategy)
                    self.assertEqual(result['status'] == 'POSITIVE_EULER', expected)
                    self.assertTrue(verify_sector_euler_certificate(raw, result['certificate']))
                matrix, linear, groups, potentials, weights = _reference_model(
                    kernel.prepared, kernel.support, lambda: None)
                self.assertEqual(matrix, kernel.cycle_rows)
                self.assertEqual((linear, weights), _euler_model(kernel))
                self.assertEqual(groups, kernel.groups)
                self.assertEqual(potentials, kernel.potentials)

    def test_interior_and_multiple_boundary_vertex_link_weights(self):
        rng = random.Random(261009492)
        interior, _ = interior_vertex_torus()
        raw, meridian = layered_torus(2)
        capped, _ = boundary_cap(raw, meridian)
        for raw in (interior, capped):
            n = len(raw['tetrahedra'])
            for _ in range(48):
                support = [(t, q) for t in range(n) if (q := rng.randrange(-1, 3)) >= 0]
                kernel = build_sector_kernel(raw, support)
                expected = any(_coordinates(kernel.prepared, rows, lambda: None)
                               ['euler_characteristic'] > 0
                               for rows in sector_rays(kernel, phase='quadrilateral'))
                result = decide_sector_euler(raw, support)
                self.assertEqual(result['status'] == 'POSITIVE_EULER', expected)
                self.assertTrue(verify_sector_euler_certificate(raw, result['certificate']))

    def test_foreign_sources_malformed_fields_and_incomplete_anchor_cover(self):
        raw, _ = layered_torus(3)
        positive = decide_sector_euler(raw, [(t, 2) for t in range(3)])['certificate']
        negative = decide_sector_euler(raw, [(t, 0) for t in range(3)])['certificate']
        foreign, _ = layered_torus(2)
        for proof in (positive, negative):
            self.assertFalse(verify_sector_euler_certificate(foreign, proof))
            for field, value in (('source_sha256', 'wrong'), ('status', 'UNKNOT'),
                                  ('allowed_types', [[0, True]])):
                bad = deepcopy(proof)
                bad[field] = value
                self.assertFalse(verify_sector_euler_certificate(raw, bad))
        for field, value in (('euler_characteristic', True), ('euler_characteristic', 2),
                              ('quadrilaterals', [0, 0, 0])):
            bad = deepcopy(positive)
            bad[field] = value
            self.assertFalse(verify_sector_euler_certificate(raw, bad))
        bad = deepcopy(positive)
        bad['coordinates'][0][0] += 1
        self.assertFalse(verify_sector_euler_certificate(raw, bad))
        bad = deepcopy(negative)
        bad['duals'].pop()
        self.assertFalse(verify_sector_euler_certificate(raw, bad))
        bad = deepcopy(negative)
        bad['duals'][-1] = bad['duals'][0]
        self.assertFalse(verify_sector_euler_certificate(raw, bad))
        for value in ([1, 0], [True, 1], [1.0, 1]):
            bad = deepcopy(negative)
            bad['duals'][0]['multipliers'][0] = value
            self.assertFalse(verify_sector_euler_certificate(raw, bad))
        bad = deepcopy(negative)
        for record in bad['duals']:
            record['multipliers'] = [[0, 1] for _ in record['multipliers']]
        self.assertFalse(verify_sector_euler_certificate(raw, bad))

    def test_replay_independence_and_shared_pivot_anchor_caps(self):
        raw, _ = layered_torus(4)
        support = [(t, 0) for t in range(4)]
        result = decide_sector_euler(raw, support)
        proof = result['certificate']
        with patch('fastunknot.normal_euler._euler_model', side_effect=AssertionError), \
             patch('fastunknot.normal_sector.build_sector_kernel', side_effect=AssertionError), \
             patch('fastunknot.exact_lp.solve_nonnegative_kernel', side_effect=AssertionError):
            self.assertTrue(verify_sector_euler_certificate(raw, proof))
        for key, maximum in (('max_pivots', result['stats']['lp_pivots']),
                              ('max_anchors', result['stats']['anchors_tested'])):
            self.assertEqual(decide_sector_euler(raw, support, **{key: maximum}), result)
            partial = decide_sector_euler(raw, support, **{key: maximum-1})
            self.assertEqual(partial['status'], 'INCONCLUSIVE')
            self.assertNotIn('certificate', partial)
        calls = [0]
        def count():
            calls[0] += 1
        verify_sector_euler_certificate(raw, proof, check=count)
        for stop in (1, calls[0]//2, calls[0]):
            current = [0]
            def cancel():
                current[0] += 1
                if current[0] == stop:
                    raise ValueError('cancelled')
            with self.assertRaisesRegex(ValueError, 'cancelled'):
                verify_sector_euler_certificate(raw, proof, check=cancel)

    def test_envelope_dual_replay_mutations_and_dominance_reuse(self):
        raw, _ = layered_torus(4)
        support = [(t, 0) for t in range(4)]
        anchor = decide_sector_euler(raw, support)
        self.assertGreater(anchor['stats']['reused_anchors'], 0)
        self.assertLess(anchor['stats']['lp_calls'], anchor['stats']['anchors_tested'])
        result = decide_sector_euler(raw, support, strategy='envelope', max_anchors=0)
        proof = result['certificate']
        self.assertEqual(proof['proof_kind'], 'envelope')
        self.assertEqual(result['stats']['anchors_tested'], 0)
        self.assertEqual(result['stats']['lp_calls'], 1)
        with patch('fastunknot.normal_euler._euler_model', side_effect=AssertionError), \
             patch('fastunknot.normal_sector.build_sector_kernel', side_effect=AssertionError), \
             patch('fastunknot.exact_lp.solve_nonnegative_kernel', side_effect=AssertionError):
            self.assertTrue(verify_sector_euler_certificate(raw, proof))
        for field, value in (('proof_kind', 'anchors'), ('multipliers', [])):
            bad = deepcopy(proof)
            bad[field] = value
            self.assertFalse(verify_sector_euler_certificate(raw, bad))
        bad = deepcopy(proof)
        bad['multipliers'] = [[0, 1] for _ in bad['multipliers']]
        self.assertFalse(verify_sector_euler_certificate(raw, bad))
        for bad_strategy in ('unknown', True, None):
            with self.assertRaises(ValueError):
                decide_sector_euler(raw, support, strategy=bad_strategy)

    def test_positive_abstract_envelope_is_not_a_positive_euler_witness(self):
        # C q=0 forces q=(t,t).  Both anchor forms have value -t, but their
        # componentwise envelope (1,1) has value 2t.  This deliberately
        # abstract control tests the fallback controller, not a triangulation.
        kernel = SimpleNamespace(support=((0, 0), (1, 0)), cycle_rows=((1, -1),),
            groups=((0, 1),), potentials={0: (0, 0), 1: (3, -3)}, stats={})
        def forbidden(*args):
            raise AssertionError('a positive envelope must not be lifted as a witness')
        kernel.lift = forbidden
        self.assertEqual(solve_nonnegative_kernel([[1, -1]], [1, 1])['status'], 'POSITIVE')
        for objective in ([1, -2], [-2, 1]):
            self.assertEqual(solve_nonnegative_kernel([[1, -1]], objective)['status'], 'NONPOSITIVE')
        with patch('fastunknot.normal_euler.build_sector_kernel', return_value=kernel), \
             patch('fastunknot.normal_euler._euler_model', return_value=((1, -2), (1,))):
            answer = decide_sector_euler({}, [], strategy='envelope')
        self.assertEqual(answer['status'], 'NO_POSITIVE_EULER')
        self.assertEqual(answer['certificate']['proof_kind'], 'anchors')
        self.assertEqual(answer['stats']['envelope_calls'], 1)
        self.assertEqual(answer['stats']['anchors_tested'], 2)
        self.assertEqual(answer['stats']['lp_calls'], 3)


if __name__ == '__main__':
    unittest.main()
