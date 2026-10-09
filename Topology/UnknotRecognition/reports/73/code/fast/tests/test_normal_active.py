"""Adversarial arithmetic and geometric tests for certified active-face search."""

from copy import deepcopy
from fractions import Fraction
import json
from pathlib import Path
import random
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from fastunknot.exact_lp import solve_nonnegative_kernel
from fastunknot.integer_codec import json_safe
from fastunknot.normal_active import (
    active_positive_cone, search_admissible_positive_cone,
    search_active_normal_positive, _normal_model, _rank,
)
from fastunknot.normal_active_verify import (
    verify_active_cone_certificate, verify_active_search_certificate,
    verify_active_normal_certificate,
)


def solid_torus():
    return {'tetrahedra': [[
        {'tetrahedron': 0, 'permutation': [1, 2, 3, 0]},
        {'tetrahedron': 0, 'permutation': [3, 0, 1, 2]}, None, None,
    ]]}


def capped_torus():
    result = solid_torus()
    result['tetrahedra'][0][2] = {'tetrahedron': 1, 'permutation': [0, 1, 3, 2]}
    result['tetrahedra'].append([
        None, None, None, {'tetrahedron': 0, 'permutation': [0, 1, 3, 2]},
    ])
    return result


class ActiveConeTests(unittest.TestCase):
    def test_one_lifted_query_finds_all_active_coordinates(self):
        matrix, objective = [[1, 0, 0]], [0, 1, -17]
        with patch('fastunknot.normal_active.solve_nonnegative_kernel',
                   wraps=solve_nonnegative_kernel) as solver:
            result = active_positive_cone(matrix, objective)
        self.assertEqual(solver.call_count, 1)
        self.assertEqual(result['active'], [1, 2])
        self.assertEqual(result['stats']['lp_calls'], 1)
        self.assertTrue(verify_active_cone_certificate(matrix, objective, result['certificate']))
        # A negative-Euler direction can still be active on positive-Euler points.
        self.assertGreater(Fraction(*result['x'][2]), 0)

    def test_projected_negative_duals_include_zero_cone_and_empty_width(self):
        cases = [([[1, -1]], [1, -2]), ([[1, 0], [0, 1]], [1, 1]),
                 ([[]], []), ([], [0, -1])]
        for matrix, objective in cases:
            with self.subTest(matrix=matrix, objective=objective):
                result = active_positive_cone(matrix, objective)
                self.assertEqual(result['status'], 'NONPOSITIVE')
                self.assertTrue(verify_active_cone_certificate(
                    matrix, objective, result['certificate']))

    def test_support_agrees_with_individual_coordinate_oracles(self):
        rng = random.Random(20261009)
        for case in range(16):
            width = 2+case % 3
            matrix = [[rng.randrange(-2, 3) for _ in range(width)]
                      for _ in range(case % 3)]
            objective = [rng.randrange(-2, 3) for _ in range(width)]
            result = active_positive_cone(matrix, objective, max_pivots=None)
            ordinary = solve_nonnegative_kernel(matrix, objective)
            self.assertEqual(result['status'] == 'ACTIVE_POSITIVE',
                             ordinary['status'] == 'POSITIVE')
            self.assertTrue(verify_active_cone_certificate(matrix, objective, result['certificate']))
            if result['status'] == 'ACTIVE_POSITIVE':
                expected = []
                for j in range(width):
                    target = [int(k == j) for k in range(width)]
                    if solve_nonnegative_kernel(matrix, target)['status'] == 'POSITIVE':
                        expected.append(j)
                self.assertEqual(result['active'], expected)

    def test_rational_source_and_hex_certificate_transport(self):
        matrix = [[[1, 3], [-2, 5], 0]]
        objective = [1, 1, 0]
        result = active_positive_cone(matrix, objective)
        proof = deepcopy(result['certificate'])
        for field in ('x', 'y'):
            proof[field] = [[hex(n), hex(d)] for n, d in proof[field]]
        self.assertTrue(verify_active_cone_certificate(matrix, objective, proof))
        self.assertTrue(verify_active_cone_certificate(matrix, objective,
                        json.loads(json.dumps(json_safe(result['certificate'])))))

    def test_incomplete_support_and_bad_duals_are_rejected(self):
        a, c = [[1, 0, 0]], [0, 1, 0]
        original = active_positive_cone(a, c)['certificate']
        changes = []
        bad = deepcopy(original); bad['x'][2] = [0, 1]; changes.append(bad)
        bad = deepcopy(original); bad['y'] = [[0, 1]]; changes.append(bad)
        bad = deepcopy(original); bad['x'][1] = [-1, 1]; changes.append(bad)
        bad = deepcopy(original); bad['y'][0][1] = 0; changes.append(bad)
        bad = deepcopy(original); bad['x'][0][0] = True; changes.append(bad)
        bad = deepcopy(original); bad['x'].pop(); changes.append(bad)
        for proof in changes:
            self.assertFalse(verify_active_cone_certificate(a, c, proof))
        self.assertFalse(verify_active_cone_certificate([], [1], dict(
            schema='active-positive-cone-v1', status='NONPOSITIVE', y=[])))

    def test_invalid_inputs_and_caps_never_return_a_negative_claim(self):
        self.assertEqual(active_positive_cone([], [1], max_pivots=0)['status'],
                         'INCONCLUSIVE')
        for matrix, objective in [([[1]], [1, 2]), ([[True]], [1]),
                                  ([[[1, 0]]], [1]), ('bad', [1])]:
            with self.assertRaises(ValueError):
                active_positive_cone(matrix, objective)
        for bad in (-1, True, 1.5):
            with self.assertRaises(ValueError):
                active_positive_cone([], [1], max_pivots=bad)

    def test_callback_errors_are_not_malformed_certificate_results(self):
        class Stop:
            def __bool__(self):
                return False
            def __call__(self):
                raise ValueError('active cancellation')
        proof = active_positive_cone([], [1])['certificate']
        with self.assertRaisesRegex(ValueError, 'active cancellation'):
            verify_active_cone_certificate([], [1], proof, check=Stop())
        with self.assertRaisesRegex(ValueError, 'active cancellation'):
            active_positive_cone([], [1], check=Stop())


class ActiveSearchTests(unittest.TestCase):
    def test_positive_support_is_not_a_surface_or_admissibility_claim(self):
        a, c, groups = [[1, -1]], [1, 1], [[0, 1]]
        relaxed = active_positive_cone(a, c)
        self.assertEqual(relaxed['status'], 'ACTIVE_POSITIVE')
        self.assertEqual(relaxed['active'], [0, 1])
        result = search_admissible_positive_cone(a, c, groups)
        self.assertEqual(result['status'], 'NO_ADMISSIBLE_POSITIVE')
        self.assertEqual(result['stats']['nodes'], 3)
        self.assertEqual(result['stats']['root_ambiguity_rank'], 1)
        self.assertTrue(verify_active_search_certificate(a, c, groups, result['certificate']))

    def test_forced_zero_cleanup_after_a_binary_restriction(self):
        a, c, groups = [[1, -1, 0]], [1, 0, 1], [[0, 1]]
        result = search_admissible_positive_cone(a, c, groups, precheck=False)
        self.assertEqual(result['status'], 'ADMISSIBLE_POSITIVE')
        self.assertEqual(result['vector'], [0, 0, 1])
        self.assertEqual(result['stats']['removed_zero_coordinates'], 1)
        self.assertEqual(result['stats']['root_dimension'], 2)
        self.assertEqual(result['stats']['root_ambiguity_rank'], 1)
        self.assertTrue(verify_active_search_certificate(a, c, groups, result['certificate']))

    def test_missing_or_unrelated_branch_does_not_cover_compatibility(self):
        a, c, groups = [[1, -1, 0, 0], [0, 0, 1, -1]], [1, 1, 1, 1], [[0, 1], [2, 3]]
        original = search_admissible_positive_cone(a, c, groups)['certificate']
        self.assertTrue(verify_active_search_certificate(a, c, groups, original))
        mutations = []
        bad = deepcopy(original); bad['tree']['children'].pop(); mutations.append(bad)
        bad = deepcopy(original); bad['tree']['pair'] = [0, 2]; mutations.append(bad)
        bad = deepcopy(original); bad['tree']['pair'] = [0, 0]; mutations.append(bad)
        bad = deepcopy(original); bad['tree']['active_certificate']['x'][0] = [0, 1]; mutations.append(bad)
        bad = deepcopy(original); bad['tree']['children'][0] = bad['tree']; mutations.append(bad)
        for proof in mutations:
            self.assertFalse(verify_active_search_certificate(a, c, groups, proof))

    def test_zero_caps_and_invalid_conflict_groups(self):
        for options in ({'max_nodes': 0}, {'max_pivots': 0}, {'max_branch_depth': 0}):
            result = search_admissible_positive_cone([], [1, 1], [[0, 1]],
                                                      precheck=False, **options)
            self.assertEqual(result['status'], 'INCONCLUSIVE')
            self.assertNotIn('certificate', result)
        for groups in ([[0, 0]], [[0, True]], [[0, 2]], 'bad'):
            with self.assertRaises(ValueError):
                search_admissible_positive_cone([], [1, 1], groups)

    def test_negative_certificate_replay_imports_no_solver(self):
        a, c, groups = [[1, -1]], [1, 1], [[0, 1]]
        proof = search_admissible_positive_cone(a, c, groups)['certificate']
        with patch('fastunknot.normal_active.solve_nonnegative_kernel',
                   side_effect=AssertionError('verifier invoked producer')):
            self.assertTrue(verify_active_search_certificate(a, c, groups, proof))


class ActiveNormalTests(unittest.TestCase):
    def test_complete_negative_normal_anchor_coverage(self):
        path = Path(__file__).with_name('fixtures')/'active_trefoil_negative.json'
        fixture = json.loads(path.read_text())
        tri, proof = fixture['triangulation'], fixture['certificate']
        self.assertTrue(verify_active_normal_certificate(tri, proof))
        self.assertEqual(len(proof['anchor_trees']), 20)
        changed = deepcopy(proof); changed['anchor_trees'].pop()
        self.assertFalse(verify_active_normal_certificate(tri, changed))
        changed = deepcopy(proof); changed['anchor_trees'][1] = changed['anchor_trees'][0]
        self.assertFalse(verify_active_normal_certificate(tri, changed))
        changed = deepcopy(proof)
        changed['anchor_trees'][0]['proof']['tree']['dual'][0][1] = 0
        self.assertFalse(verify_active_normal_certificate(tri, changed))

    def test_genuine_solid_torus_search_and_geometric_replay(self):
        tri = solid_torus()
        result = search_active_normal_positive(tri)
        self.assertEqual(result['status'], 'POSITIVE_EULER')
        self.assertEqual(result['coordinates'], [[1, 1, 0, 0, 0, 0, 1]])
        self.assertTrue(verify_active_normal_certificate(tri, result['certificate']))
        from fastunknot.normal_disk_kernel import normal_compressing_disk_count
        self.assertEqual(normal_compressing_disk_count(tri, result['coordinates'])
                         ['compressing_disk_components'], 1)

    def test_source_and_anchor_binding(self):
        tri = solid_torus()
        original = search_active_normal_positive(tri)['certificate']
        bad = deepcopy(original); bad['source_sha256'] = '0'*64
        self.assertFalse(verify_active_normal_certificate(tri, bad))
        bad = deepcopy(original); bad['anchors'] = [0]
        self.assertFalse(verify_active_normal_certificate(tri, bad))
        bad = deepcopy(original); bad['coordinates'][0][6] += 1
        self.assertFalse(verify_active_normal_certificate(tri, bad))
        self.assertFalse(verify_active_normal_certificate(capped_torus(), original))

    def test_universal_all_quad_vector_and_local_tetrahedral_directions(self):
        tri = capped_torus()
        prepared, a, c, groups = _normal_model(tri, lambda: None)
        width = len(c)
        r = [int(j % 7 >= 4) for j in range(width)]
        self.assertTrue(all(sum(v*w for v, w in zip(row, r)) == 0 for row in a))
        # Both anchors are in tetrahedron 0 or tetrahedron 1 depending on group;
        # the local relation itself holds before any anchor is selected.
        directions = []
        for t in range(2):
            w = [0]*width
            w[7*t:7*t+7] = [1, 1, 1, 1, -1, -1, -1]
            self.assertTrue(all(sum(v*z for v, z in zip(row, w)) == 0 for row in a))
            self.assertTrue(all(v+z >= 0 for v, z in zip(r, w)))
            directions.append([w[7*k+4+q] for k in range(2) for q in range(3)])
        self.assertEqual(_rank(directions, 6, lambda: None), 2)

    def test_normal_caps_and_callback_propagation(self):
        tri = solid_torus()
        self.assertEqual(search_active_normal_positive(tri, max_nodes=0)['status'],
                         'INCONCLUSIVE')
        proof = search_active_normal_positive(tri)['certificate']
        def stop():
            raise ValueError('normal active cancellation')
        with self.assertRaisesRegex(ValueError, 'normal active cancellation'):
            verify_active_normal_certificate(tri, proof, check=stop)


if __name__ == '__main__':
    unittest.main()
