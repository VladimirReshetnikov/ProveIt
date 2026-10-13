"""Exact primal/dual replay, independent small LP oracle, and shared budgets."""
from copy import deepcopy
from fractions import Fraction as Q
from itertools import combinations, product
import json
from math import gcd
from random import Random
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from fastunknot.exact_lp import solve_nonnegative_kernel
from fastunknot.integer_codec import encoded_integer, json_safe
from fastunknot.normal_euler import decide_sector_euler
from fastunknot.normal_euler_verify import verify_sector_euler_certificate
from fastunknot.normal_sector import build_sector_kernel, sector_rays, SearchLimit
from fastunknot.normal_surface_geometry import _coordinates, NormalOrbitError
from normal_orbit_research.fixtures import layered_torus, boundary_cap, interior_vertex_torus


def rational(pair):
    return Q(*(encoded_integer(x) for x in pair))


def unique_solution(matrix, rhs, width):
    """Independent reverse-column Gauss-Jordan solver for the tiny oracle."""
    rows = [[Q(x) for x in row]+[Q(value)] for row, value in zip(matrix, rhs)]
    pivots = []
    for column in reversed(range(width)):
        candidates = [i for i in range(len(pivots), len(rows)) if rows[i][column]]
        if not candidates:
            continue
        index = len(pivots)
        chosen = candidates[-1]
        rows[index], rows[chosen] = rows[chosen], rows[index]
        divisor = rows[index][column]
        rows[index] = [x/divisor for x in rows[index]]
        for i in range(len(rows)):
            if i != index:
                factor = rows[i][column]
                rows[i] = [a-factor*b for a, b in zip(rows[i], rows[index])]
        pivots.append(column)
    if len(pivots) != width or any(not any(row[:-1]) and row[-1] for row in rows):
        return None
    answer = [Q(0)]*width
    for i, column in enumerate(pivots):
        answer[column] = rows[i][-1]
    return answer


def exhaustive_positive(matrix, objective):
    """Enumerate normalized support vertices independently of the producer."""
    for size in range(1, len(objective)+1):
        for selected in combinations(range(len(objective)), size):
            rows = [[row[j] for j in selected] for row in matrix]+[[1]*size]
            vector = unique_solution(rows, [0]*len(matrix)+[1], size)
            if (vector is not None and all(x >= 0 for x in vector)
                    and sum(objective[j]*x for j, x in zip(selected, vector)) > 0):
                return True
    return False


class ExactKernelLPTests(unittest.TestCase):
    def assert_replay(self, matrix, objective, result):
        if result['status'] == 'POSITIVE':
            x = list(map(rational, result['x']))
            self.assertTrue(all(value >= 0 for value in x))
            self.assertEqual(sum(x), 1)
            self.assertTrue(all(sum(a*b for a, b in zip(row, x)) == 0 for row in matrix))
            value = sum(a*b for a, b in zip(objective, x))
            self.assertGreater(value, 0)
            self.assertEqual(value, rational(result['objective']))
            primitive = list(map(encoded_integer, result['primitive_x']))
            self.assertEqual([Q(a, sum(primitive)) for a in primitive], x)
            common = 0
            for a in primitive:
                common = gcd(common, a)
            self.assertEqual(common, 1)
            active = [j for j, value in enumerate(x) if value]
            restricted = [[row[j] for j in active] for row in matrix]+[[1]*len(active)]
            self.assertEqual(unique_solution(restricted, [0]*len(matrix)+[1], len(active)),
                             [x[j] for j in active])
        else:
            self.assertEqual(result['status'], 'NONPOSITIVE')
            y = list(map(rational, result['y']))
            self.assertEqual(len(y), len(matrix))
            self.assertTrue(all(sum(row[j]*value for row, value in zip(matrix, y)) >= c
                                for j, c in enumerate(objective)))

    def test_independent_support_oracle_on_degenerate_random_cones(self):
        rng = Random(261009483)
        for _ in range(240):
            n, m = rng.randrange(1, 6), rng.randrange(5)
            matrix = [[rng.randrange(-3, 4) for _ in range(n)] for _ in range(m)]
            objective = [rng.randrange(-4, 5) for _ in range(n)]
            result = solve_nonnegative_kernel(matrix, objective)
            self.assert_replay(matrix, objective, result)
            self.assertEqual(result['status'] == 'POSITIVE', exhaustive_positive(matrix, objective))
            unreduced = solve_nonnegative_kernel(matrix, objective, reduce_rows=False)
            self.assert_replay(matrix, objective, unreduced)
            self.assertEqual(result['status'], unreduced['status'])
            self.assertLessEqual(result['stats']['retained_equations'], min(n, m))
            self.assertEqual(unreduced['equation_rows'], list(range(m)))

    def test_original_row_selection_lifts_duals_and_preserves_dependent_constraints(self):
        matrix = [[0, 0, 0], [Q(1, 2), -1, 0], [1, -2, 0],
                  [0, 1, -1], [Q(3, 2), -1, -2], [-2, 4, 0]]
        for objective in ([1, 0, 0], [-1, 0, 0], [0, 1, -1]):
            result = solve_nonnegative_kernel(matrix, objective)
            self.assert_replay(matrix, objective, result)
            self.assertEqual(result['equation_rows'], [1, 3])
            self.assertEqual(result['stats']['equations'], 6)
            self.assertEqual(result['stats']['retained_equations'], 2)
            self.assertEqual(result['stats']['tableau_rows'], 5)
            self.assertEqual(result['status'] == 'POSITIVE', exhaustive_positive(matrix, objective))
            if result['status'] == 'NONPOSITIVE':
                self.assertTrue(all(result['y'][i] == [0, 1] for i in (0, 2, 4, 5)))
        # Pivot columns need not arrive in sorted order. The later row still
        # has to be eliminated against every previously selected pivot.
        permuted = [[0, 0, 1], [1, 0, 2], [2, 0, 4], [0, 1, 3], [1, 1, 5]]
        result = solve_nonnegative_kernel(permuted, [1, 1, 1])
        self.assertEqual(result['equation_rows'], [0, 1, 3])
        self.assert_replay(permuted, [1, 1, 1], result)

    def test_row_reduction_validation_zero_rows_and_pivot_allowance(self):
        for bad in (None, 0, 1, 'true', [], {}):
            with self.assertRaises(ValueError):
                solve_nonnegative_kernel([], [1], reduce_rows=bad)
        result = solve_nonnegative_kernel([[0, 0]]*40, [-1, 0], max_pivots=0)
        self.assertEqual(result['status'], 'NONPOSITIVE')
        self.assertEqual(result['equation_rows'], [])
        self.assertEqual(result['y'], [[0, 1]]*40)
        self.assertEqual(result['stats']['tableau_rows'], 1)
        matrix, objective = [[0, 0], [1, -1], [2, -2]], [1, 0]
        full = solve_nonnegative_kernel(matrix, objective)
        capped = solve_nonnegative_kernel(matrix, objective, max_pivots=full['stats']['pivots']-1)
        self.assertEqual(capped['status'], 'INCONCLUSIVE')
        self.assertEqual(capped['equation_rows'], [1])
        self.assertNotIn('x', capped)
        self.assertNotIn('y', capped)

    def test_zero_width_redundancy_fractional_and_large_binary_inputs(self):
        huge = 1 << 20000
        for matrix, objective in (([], []), ([[], []], []), ([], [0, -1]),
                                  ([[0, 0], [1, -2], [2, -4]], [Q(-1, 2), 0]),
                                  ([[Q(1, 2), -1]], [1, 0]),
                                  ([[1, -huge]], [1, 0]), ([[huge, -1]], [1, -1])):
            result = solve_nonnegative_kernel(matrix, objective)
            self.assert_replay(matrix, objective, result)
            self.assert_replay(matrix, objective, json.loads(json.dumps(json_safe(result))))
        self.assertEqual(solve_nonnegative_kernel([[[1, 2], -1]], [1, 0])['primitive_x'], [2, 1])
        self.assertEqual(solve_nonnegative_kernel([[1, '-0x10']], [1, 0])['primitive_x'], [16, 1])

    def test_caps_strict_validation_immutability_and_all_callback_polls(self):
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
                                          ([[[1, -1]]], [1]), ([[[1, True]]], [1]),
                                          ([[1]], [False]), ({}, [1]), ([[1]], {1})):
            with self.assertRaises(ValueError):
                solve_nonnegative_kernel(bad_matrix, bad_objective)
        for cap in (-1, True, 2.0):
            with self.assertRaises(ValueError):
                solve_nonnegative_kernel(matrix, objective, max_pivots=cap)
        calls = [0]
        def count():
            calls[0] += 1
        solve_nonnegative_kernel(matrix, objective, check=count)
        for stop in range(1, calls[0]+1):
            current = [0]
            error = ValueError('caller cancellation')
            def cancel():
                current[0] += 1
                if current[0] == stop:
                    raise error
            with self.assertRaises(ValueError) as raised:
                solve_nonnegative_kernel(matrix, objective, check=cancel)
            self.assertIs(raised.exception, error)
        self.assertEqual((matrix, objective), original)


class SectorEulerProducerTests(unittest.TestCase):
    def test_positive_envelope_point_checks_actual_euler_before_any_anchor(self):
        raw, rows = layered_torus(1)
        allowed = [(t, q) for t, row in enumerate(rows) for q in range(3) if row[4+q]]
        result = decide_sector_euler(raw, allowed, strategy='envelope', max_anchors=0)
        self.assertEqual(result['status'], 'POSITIVE_EULER')
        self.assertEqual(result['stats']['anchors_tested'], 0)
        self.assertEqual(result['stats']['lp_calls'], 1)
        self.assertTrue(verify_sector_euler_certificate(raw, result['certificate']))

    def test_small_layered_sectors_against_complete_q_ray_enumeration(self):
        for n in range(1, 4):
            raw, _ = layered_torus(n)
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

    def test_interior_and_multiple_boundary_vertex_link_weights(self):
        rng = Random(261009492)
        interior, _ = interior_vertex_torus()
        raw, meridian = layered_torus(2)
        capped, _ = boundary_cap(raw, meridian)
        for raw in (interior, capped):
            for _ in range(24):
                support = [(t, q) for t in range(len(raw['tetrahedra']))
                           if (q := rng.randrange(-1, 3)) >= 0]
                kernel = build_sector_kernel(raw, support)
                expected = any(_coordinates(kernel.prepared, rows, lambda: None)
                               ['euler_characteristic'] > 0
                               for rows in sector_rays(kernel, phase='quadrilateral'))
                result = decide_sector_euler(raw, support)
                self.assertEqual(result['status'] == 'POSITIVE_EULER', expected)
                self.assertTrue(verify_sector_euler_certificate(raw, result['certificate']))

    def test_shared_caps_dual_reuse_and_callback_identity(self):
        raw, _ = layered_torus(4)
        support = [(t, 0) for t in range(4)]
        result = decide_sector_euler(raw, support)
        self.assertGreater(result['stats']['reused_anchors'], 0)
        for key, maximum in (('max_pivots', result['stats']['lp_pivots']),
                              ('max_anchors', result['stats']['anchors_tested'])):
            self.assertEqual(decide_sector_euler(raw, support, **{key: maximum}), result)
            partial = decide_sector_euler(raw, support, **{key: maximum-1})
            self.assertEqual(partial['status'], 'INCONCLUSIVE')
            self.assertNotIn('certificate', partial)
            for value in (True, -1, 0.5):
                with self.assertRaises(ValueError):
                    decide_sector_euler(raw, support, **{key: value})
        envelope = decide_sector_euler(raw, support, strategy='envelope', max_anchors=0)
        self.assertEqual(envelope['status'], 'NO_POSITIVE_EULER')
        self.assertEqual(envelope['stats']['anchors_tested'], 0)
        self.assertEqual(envelope['stats']['lp_calls'], 1)
        self.assertEqual(envelope['certificate']['proof_kind'], 'envelope')
        for strategy in (None, True, 'wrong'):
            with self.assertRaises(ValueError):
                decide_sector_euler(raw, support, strategy=strategy)
        calls = [0]
        def count():
            calls[0] += 1
        decide_sector_euler(raw, support, check=count)
        for error_type in (ValueError, NormalOrbitError, SearchLimit):
            for stop in (1, calls[0]//2, calls[0]):
                current = [0]
                error = error_type('caller cancellation')
                def cancel():
                    current[0] += 1
                    if current[0] == stop:
                        raise error
                with self.assertRaises(error_type) as raised:
                    decide_sector_euler(raw, support, check=cancel)
                self.assertIs(raised.exception, error)

    def test_positive_abstract_envelope_requires_anchor_fallback(self):
        # On q=(t,t), both anchor objectives are -t while their coordinatewise
        # envelope is 2t. The envelope point cannot authenticate positivity.
        kernel = SimpleNamespace(support=((0, 0), (1, 0)), cycle_rows=((1, -1),),
            groups=((0, 1),), potentials={0: (0, 0), 1: (3, -3)}, stats={})
        kernel.lift = lambda *args: self.fail('positive envelope must not be lifted')
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
