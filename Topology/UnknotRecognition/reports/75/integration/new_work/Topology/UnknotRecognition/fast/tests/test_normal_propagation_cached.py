"""Exact cache soundness, policy preservation, and LP-call separation."""

from copy import deepcopy
from itertools import product
from pathlib import Path
import importlib.util
import json
import unittest
from unittest.mock import patch

from fastunknot.normal_propagation import search_positive_euler as baseline
from fastunknot.normal_propagation_cached import PositiveWitnessCache, search_positive_euler
from fastunknot.normal_propagation_verify import verify_normal_propagation_certificate
from lp_cache_research.synthetic_family import run as synthetic_run
from normal_orbit_research.fixtures import layered_torus, boundary_cap
from tests.test_normal_propagation import branching_torus, finite_trefoil


class PositiveWitnessCacheTests(unittest.TestCase):
    def test_exact_validation_and_input_immutability(self):
        matrix, objective = [[1, -1, 0]], [1, 0, 0]
        cache = PositiveWitnessCache(matrix, objective)
        vector = [2, 2, 0]
        cache.add(vector)
        matrix[0][0] = 999
        objective[0] = -1
        vector[0] = 0
        self.assertEqual(cache.entries, ((3, (2, 2, 0)),))
        self.assertTrue(cache.covers(3))
        self.assertFalse(cache.covers(5))
        for bad in ([1, 0, 0], [0, 0, 1], [-1, -1, 0], [True, 1, 0], [1, 1]):
            with self.assertRaises(ValueError):
                cache.add(bad)
        for mask in (-1, True, 8):
            with self.assertRaises(ValueError):
                cache.covers(mask)
        for value in (-1, True, 1.5):
            with self.assertRaises(ValueError):
                PositiveWitnessCache([], [1], capacity=value)

    def test_minimal_support_antichain_preserves_every_zero_query(self):
        cache = PositiveWitnessCache([], [1]*4, capacity=None)
        supplied = []
        vectors = ([1,1,1,0], [1,1,0,0], [2,2,0,1], [0,1,0,0],
                   [1,0,1,0], [1,0,0,0], [0,0,1,1], [0,0,0,1])
        for vector in vectors:
            supplied.append(vector)
            cache.add(vector)
            supports = [mask for mask, _ in cache.entries]
            self.assertTrue(all(a & b != a for a in supports for b in supports if a != b))
            for bits in product((0, 1), repeat=4):
                mask = sum(b << j for j, b in enumerate(bits))
                expected = any(all(not x or bits[j] for j, x in enumerate(v)) for v in supplied)
                self.assertEqual(cache.covers(mask), expected)

    def test_anchor_and_sibling_restrictions_must_all_hold(self):
        cache = PositiveWitnessCache([], [1,1,1,1])
        cache.add([1,0,1,0])
        # A zero in the tested coordinate is insufficient if an anchor or a
        # sibling's branch has forbidden another coordinate in the support.
        self.assertTrue(cache.covers(0b0101))
        self.assertFalse(cache.covers(0b0100))
        self.assertFalse(cache.covers(0b0001))
        cache.add([0,0,1,0])
        self.assertTrue(cache.covers(0b0100))
        self.assertFalse(cache.covers(0b0001))

    def test_finite_capacity_only_evicts_evidence(self):
        cache = PositiveWitnessCache([], [1,1,1], capacity=1)
        cache.add([1,0,0])
        cache.add([0,1,0])
        self.assertFalse(cache.covers(1))
        self.assertTrue(cache.covers(2))
        self.assertEqual(cache.stats()['cache_evictions'], 1)
        disabled = PositiveWitnessCache([], [1], capacity=0)
        self.assertEqual(disabled.add([3]), 1)
        self.assertFalse(disabled.covers(1))
        self.assertFalse(disabled.entries)


class CachedPropagationTests(unittest.TestCase):
    def assert_equivalent(self, raw, options=None):
        options = {} if options is None else options
        old = baseline(raw, **options)
        new = search_positive_euler(raw, **options)
        self.assertEqual(old['status'], new['status'])
        self.assertEqual(old.get('certificate'), new.get('certificate'))
        self.assertEqual(old.get('coordinates'), new.get('coordinates'))
        if 'certificate' in new:
            self.assertTrue(verify_normal_propagation_certificate(raw, new['certificate']))
        for key in ('nodes', 'branches', 'propagations', 'anchors_started',
                    'anchors_completed', 'maximum_branch_depth', 'branched_tetrahedra'):
            self.assertEqual(old['stats'][key], new['stats'][key], key)
        self.assertLessEqual(new['stats']['lp_calls'], old['stats']['lp_calls'])
        self.assertLessEqual(new['stats']['lp_pivots'], old['stats']['lp_pivots'])
        skipped = new['stats']['witness_local_hits'] + new['stats']['witness_antichain_hits']
        self.assertEqual(old['stats']['lp_calls'] - new['stats']['lp_calls'], skipped)
        return old, new

    def test_layered_family_and_actual_branching_certificate_equality(self):
        for t in range(1, 6):
            with self.subTest(tetrahedra=t):
                self.assert_equivalent(layered_torus(t)[0])
        old, new = self.assert_equivalent(branching_torus())
        self.assertGreater(new['stats']['branches'], 0)
        self.assertLess(new['stats']['lp_calls'], old['stats']['lp_calls'])
        self.assertGreater(new['stats']['witness_antichain_hits'], 0)

    def test_complete_negative_certificate_and_verifier_independence(self):
        raw = finite_trefoil()
        old, new = self.assert_equivalent(raw)
        self.assertEqual(new['status'], 'NO_POSITIVE_EULER')
        with patch('fastunknot.normal_propagation_cached.solve_nonnegative_kernel',
                   side_effect=AssertionError), \
             patch('fastunknot.exact_lp.solve_nonnegative_kernel', side_effect=AssertionError):
            self.assertTrue(verify_normal_propagation_certificate(raw, new['certificate']))

    def test_multiple_vertices_and_branch_restrictions(self):
        self.assert_equivalent(boundary_cap(*layered_torus(2))[0])
        raw = branching_torus()
        for options in (dict(max_branch_depth=0), dict(allowed_branch_tetrahedra=[]),
                        dict(allowed_branch_tetrahedra=[1])):
            self.assert_equivalent(raw, options)

    def test_cache_capacity_changes_performance_only(self):
        raw = branching_torus()
        reference = baseline(raw)
        for capacity in (0, 1, 2, None):
            new = search_positive_euler(raw, max_cached_witnesses=capacity)
            self.assertEqual(reference['certificate'], new['certificate'])
            self.assertLessEqual(new['stats']['lp_calls'], reference['stats']['lp_calls'])
            if capacity is not None:
                self.assertLessEqual(new['stats']['cache_max_entries'], capacity)

    def test_resource_exhaustion_and_invalid_cache_limits(self):
        raw = branching_torus()
        for options in (dict(max_nodes=0), dict(max_pivots=0), dict(max_pivots=10)):
            new = search_positive_euler(raw, **options)
            self.assertEqual(new['status'], 'INCONCLUSIVE')
            self.assertNotIn('certificate', new)
            if 'max_pivots' in options:
                self.assertLessEqual(new['stats']['lp_pivots'], options['max_pivots'])
        for value in (-1, True, 0.5):
            with self.assertRaises(ValueError):
                search_positive_euler(raw, max_cached_witnesses=value)

    def test_checked_cache_rejects_corrupted_lp_witness(self):
        raw = layered_torus(2)[0]
        from fastunknot.exact_lp import solve_nonnegative_kernel

        def corrupt(matrix, objective, **options):
            result = solve_nonnegative_kernel(matrix, objective, **options)
            if result['status'] == 'POSITIVE':
                result = deepcopy(result)
                result['primitive_x'] = [0]*len(result['primitive_x'])
            return result

        with patch('fastunknot.normal_propagation_cached.solve_nonnegative_kernel', corrupt):
            with self.assertRaises(ValueError):
                search_positive_euler(raw)

    def test_algebraic_family_has_quadratic_to_linear_lp_separation(self):
        for r in range(1, 5):
            old = synthetic_run(r, cached=False)
            for capacity in (0, 256):
                new = synthetic_run(r, cached=True, capacity=capacity)
                self.assertEqual(old['status'], 'POSITIVE_EULER')
                self.assertEqual(old['certificate'], new['certificate'])
                self.assertEqual(old['stats']['propagations'], r)
                self.assertEqual(old['stats']['lp_calls'], 3*r*r+2*r+1)
                self.assertEqual(new['stats']['lp_calls'], 2*r+1)
                self.assertEqual(new['stats']['witness_local_hits'], 3*r*r)

    @unittest.skipUnless(importlib.util.find_spec('regina'), 'optional native topology check')
    def test_native_and_frozen_figure_eight_provenance(self):
        import regina
        from normal_orbit_research.fixtures import export_triangulation, regina_triangulation
        path = Path(__file__).resolve().parents[1] / 'lp_cache_research/triangulations.json'
        fixtures = json.loads(path.read_text())
        native = regina.Example3.figureEight()
        native.idealToFinite()
        native.simplify()
        for name in ('figure_eight_native', 'frozen_figure-eight',
                     'frozen_figure-eight-relabeled'):
            saved = fixtures[name]
            tri = regina_triangulation(saved['triangulation'])
            self.assertEqual(tri.isoSig(), saved['iso_sig'])
            self.assertTrue(tri.isValid())
            self.assertTrue(tri.isOrientable())
            self.assertFalse(tri.isIdeal())
            self.assertEqual(tri.countBoundaryComponents(), 1)
            self.assertEqual(tri.boundaryComponent(0).eulerChar(), 0)
        # Simplification can choose a different finite triangulation depending
        # on Regina's process history or version. Freeze each actual source;
        # do not require fresh and saved triangulations to be isomorphic.
        self.assertTrue(native.isValid())
        self.assertTrue(native.isOrientable())
        self.assertFalse(native.isIdeal())
        self.assertEqual(native.countBoundaryComponents(), 1)
        self.assertEqual(native.boundaryComponent(0).eulerChar(), 0)
        self.assertFalse(native.isSolidTorus())
        raw = export_triangulation(native)
        roundtrip = regina_triangulation(raw)
        self.assertEqual(roundtrip.isoSig(), native.isoSig())
        self.assertEqual(export_triangulation(roundtrip), raw)


if __name__ == '__main__':
    unittest.main()
