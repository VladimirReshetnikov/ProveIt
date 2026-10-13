"""Uniform conflict learning, complete negative coverage, and shared caps."""
from copy import deepcopy
import unittest
from unittest.mock import patch

from fastunknot.normal_crushing import crush_normal_ray
from fastunknot.normal_crushing_verify import verify_normal_crushing
from fastunknot.normal_euler_transversal import search_euler_transversal
from fastunknot.normal_euler_tree import _EulerMaskOracle
from fastunknot.normal_euler_tree_verify import verify_euler_branch_tree
from fastunknot.normal_sector import SearchLimit
from fastunknot.normal_surface_geometry import _prepare, _coordinates
from fastunknot.positive_ray import extract_positive_ray
from normal_orbit_research.fixtures import layered_torus, boundary_cap


class EulerTransversalSearchTests(unittest.TestCase):
    def setUp(self):
        self.source = layered_torus(2)[0]
        self.binary = [(0, 0), (1, 0), (1, 2)]
        self.anchors = [(0, 1), (1, 0), (1, 1), (1, 2)]

    def test_learned_singleton_refutes_empty_candidate_and_covers_all_children(self):
        result = search_euler_transversal(self.source, self.binary)
        self.assertEqual(result['status'], 'NO_POSITIVE_EULER')
        self.assertEqual(result['resolving_set'], [1])
        stats = result['stats']
        self.assertEqual(stats['transversal_restarts'], 1)
        self.assertEqual(stats['transversal_candidates'], 2)
        self.assertEqual(stats['hitting_subsets_tested'], 2)
        self.assertEqual(stats['nodes_attempted'], 4)
        self.assertEqual(stats['kernel_preparations'], 1)
        self.assertTrue(verify_euler_branch_tree(self.source, result['certificate']))
        nodes = result['certificate']['nodes']
        self.assertEqual(nodes[0], dict(kind='split', tetrahedron=1))
        self.assertEqual([n['certificate']['allowed_types'] for n in nodes[1:]],
                         [[[0, 0], [1, 0]], [[0, 0], [1, 2]]])
        bad = deepcopy(result['certificate'])
        bad['nodes'].pop()
        self.assertFalse(verify_euler_branch_tree(self.source, bad))

    def test_real_positive_output_after_restarts_is_canonical_and_crushable(self):
        result = search_euler_transversal(self.source)
        self.assertEqual(result['status'], 'POSITIVE_EULER')
        self.assertGreater(result['stats']['transversal_restarts'], 0)
        self.assertNotIn('certificate', result)
        analysed = _coordinates(_prepare(self.source, lambda: None), result['coordinates'], lambda: None)
        self.assertEqual(analysed['euler_characteristic'], result['euler_characteristic'])
        ray = extract_positive_ray(self.source, result['coordinates'])
        packet = crush_normal_ray(self.source, ray['coordinates'])['certificate']
        self.assertTrue(verify_normal_crushing(self.source, packet))

    def test_anchor_and_envelope_modes_on_positive_and_empty_sources(self):
        for source in (layered_torus(1)[0], boundary_cap(*layered_torus(1))[0]):
            for strategy in ('anchors', 'envelope'):
                result = search_euler_transversal(source, strategy=strategy)
                self.assertEqual(result['status'], 'POSITIVE_EULER')
                self.assertGreater(result['euler_characteristic'], 0)
        for strategy in ('anchors', 'envelope'):
            result = search_euler_transversal(self.source, [], strategy=strategy)
            self.assertEqual(result['status'], 'NO_POSITIVE_EULER')
            self.assertEqual(result['resolving_set'], [])
            self.assertTrue(verify_euler_branch_tree(self.source, result['certificate']))

    def test_every_cap_is_global_across_candidate_restarts(self):
        full = search_euler_transversal(self.source, self.anchors)
        self.assertEqual(full['status'], 'NO_POSITIVE_EULER')
        mappings = [('max_nodes', 'nodes_attempted'), ('max_pivots', 'lp_pivots'),
                    ('max_anchors', 'anchors_tested'),
                    ('max_hitting_subsets', 'hitting_subsets_tested')]
        for option, stat in mappings:
            cap = full['stats'][stat]-1
            result = search_euler_transversal(self.source, self.anchors, **{option: cap})
            self.assertEqual(result['status'], 'INCONCLUSIVE', option)
            self.assertEqual(result['stats'][stat], cap, option)
            self.assertNotIn('certificate', result)
        exact = {option: full['stats'][stat] for option, stat in mappings}
        self.assertEqual(search_euler_transversal(self.source, self.anchors, **exact), full)
        for option, stat in mappings:
            result = search_euler_transversal(self.source, self.anchors, **{option: 0})
            self.assertEqual(result['status'], 'INCONCLUSIVE', option)
            self.assertEqual(result['stats'][stat], 0, option)
            self.assertNotIn('certificate', result)

    def test_hitting_cap_charges_subsets_rejected_without_oracle_calls(self):
        full = search_euler_transversal(self.source)
        self.assertGreater(full['stats']['hitting_subsets_tested'], full['stats']['transversal_candidates'])
        cap = full['stats']['hitting_subsets_tested']-1
        result = search_euler_transversal(self.source, max_hitting_subsets=cap)
        self.assertEqual(result['status'], 'INCONCLUSIVE')
        self.assertEqual(result['stats']['hitting_subsets_tested'], cap)
        self.assertEqual(result['reason'], 'shared hitting-subset allowance exhausted')
        self.assertLess(result['stats']['transversal_candidates'], full['stats']['transversal_candidates'])

    def test_cancellation_identity_during_source_oracle_and_subset_filter(self):
        for error in (SearchLimit('caller'), RuntimeError('caller'), ValueError('caller')):
            def stop():
                raise error
            with self.assertRaises(type(error)) as seen:
                search_euler_transversal(self.source, check=stop)
            self.assertIs(seen.exception, error)
            with patch.object(_EulerMaskOracle, 'attempt', side_effect=error):
                with self.assertRaises(type(error)) as seen:
                    search_euler_transversal(self.source)
            self.assertIs(seen.exception, error)
        calls = 0
        error = SearchLimit('subset callback')
        def subset_check():
            nonlocal calls
            calls += 1
            if calls > 1:
                raise error
        # Isolate the post-validation scheduling callbacks, before any LP.
        with patch('fastunknot.normal_euler_transversal._prepare', return_value=_prepare(self.source, lambda: None)):
            with self.assertRaises(SearchLimit) as seen:
                search_euler_transversal(self.source, self.binary, check=subset_check)
        self.assertIs(seen.exception, error)

    def test_strict_caps_masks_and_strategy(self):
        for option in ('max_nodes', 'max_pivots', 'max_anchors', 'max_hitting_subsets'):
            for value in (-1, True, 1.0, '2'):
                with self.assertRaises(ValueError):
                    search_euler_transversal(self.source, **{option: value})
        for mask in ([[0, True]], [[1, 0], [0, 0]], [[0, 0], [0, 0]], [[2, 0]]):
            with self.assertRaises(ValueError):
                search_euler_transversal(self.source, mask)
        with self.assertRaises(ValueError):
            search_euler_transversal(self.source, strategy='wrong')

    def test_shared_oracle_retains_at_most_256_duals(self):
        prepared = _prepare(self.source, lambda: None)
        from fastunknot.normal_euler_tree import _euler_search_stats
        oracle = _EulerMaskOracle(self.source, prepared, strategy='anchors', model='source',
                                  max_pivots=None, max_anchors=None, check=lambda: None,
                                  stats=_euler_search_stats())
        oracle.attempt(tuple(self.anchors))
        self.assertLessEqual(len(oracle.source_cache), 256)
        self.assertEqual(oracle.stats['kernel_preparations'], 1)
        oracle.attempt(tuple(self.binary))
        self.assertEqual(oracle.stats['kernel_preparations'], 1)
        self.assertLessEqual(len(oracle.source_cache), 256)


if __name__ == '__main__':
    unittest.main()
