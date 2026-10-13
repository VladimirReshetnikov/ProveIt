"""Conflict-directed candidate coverage, bounded forgetting, and native replay."""
from itertools import combinations
from random import Random
import unittest
from unittest.mock import patch

from fastunknot.normal_euler_transversal import search_euler_transversal, _conflict_candidates, _subset_candidates
from fastunknot.normal_euler_tree_verify import verify_euler_branch_tree
from fastunknot.normal_surface_geometry import _prepare, _coordinates
from fastunknot.normal_crushing import crush_normal_ray
from fastunknot.normal_crushing_verify import verify_normal_crushing
from fastunknot.positive_ray import extract_positive_ray
from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_search import recognize_by_crushing, verify_crushing_recognition
from fastunknot.normal_crushing_chain import verify_crushing_chain
from normal_orbit_research.fixtures import layered_torus


def minimum_hitting_size(n, edges):
    for size in range(n+1):
        for candidate in combinations(range(n), size):
            if all(set(candidate).intersection(edge) for edge in edges):
                return size
    raise AssertionError('nonempty hyperedges must have a transversal')


def adaptive_hitting(n, edges, *, capacity=256, method=_conflict_candidates):
    """Exact abstract separation independent of any Euler LP."""
    cache, stats, proposals = [], dict(hitting_subsets_tested=0), []
    for candidate in method(tuple(range(n)), cache, stats, None, lambda: None):
        assert candidate is not None
        proposals.append(candidate)
        missed = next((e for e in edges if not set(candidate).intersection(e)), None)
        if missed is None:
            return candidate, stats, proposals
        cache.append(frozenset(missed))
        if len(cache) > capacity:
            del cache[0]
    raise AssertionError('candidate search lost every transversal')


class ConflictCandidateTests(unittest.TestCase):
    def test_partition_and_forgetting_preserve_minimum_transversal(self):
        rng = Random(2026101302)
        cases = [(0, []), (5, [{1}, {3}]), (5, [{0, 1}, {1, 2}, {2, 3}, {3, 4}])]
        for _ in range(36):
            n = rng.randrange(2, 7)
            edges = [set(rng.sample(range(n), rng.randrange(1, min(n, 3)+1)))
                     for _ in range(rng.randrange(1, 9))]
            cases.append((n, edges))
        for n, edges in cases:
            h = minimum_hitting_size(n, edges)
            delta = max((len(edge) for edge in edges), default=1)
            bound = sum(sum(delta**j for j in range(k+1)) for k in range(h+1))
            for capacity in (1, 2, 256):
                with self.subTest(n=n, edges=edges, capacity=capacity):
                    candidate, stats, _ = adaptive_hitting(n, edges, capacity=capacity)
                    self.assertEqual(len(candidate), h)
                    self.assertTrue(all(set(candidate).intersection(edge) for edge in edges))
                    self.assertLessEqual(stats['hitting_subsets_tested'], bound)

    def test_singleton_skips_irrelevant_tetrahedra(self):
        old = adaptive_hitting(1000, [{999}], method=_subset_candidates)
        new = adaptive_hitting(1000, [{999}])
        self.assertEqual(old[0], new[0])
        self.assertEqual(old[1]['hitting_subsets_tested'], 1001)
        self.assertEqual(new[1]['hitting_subsets_tested'], 3)
        self.assertEqual(old[2], new[2])

    def test_all_two_tetrahedron_masks_agree_and_replay(self):
        source = layered_torus(2)[0]
        prepared = _prepare(source, lambda: None)
        for bits in range(64):
            mask = [(j//3, j%3) for j in range(6) if bits & (1 << j)]
            for strategy in ('envelope', 'anchors'):
                old = search_euler_transversal(source, mask, strategy=strategy)
                new = search_euler_transversal(source, mask, strategy=strategy, candidate_policy='conflicts')
                self.assertEqual(new['status'], old['status'], (bits, strategy))
                if new['status'] == 'NO_POSITIVE_EULER':
                    self.assertTrue(verify_euler_branch_tree(source, new['certificate']))
                    splits = {node['tetrahedron'] for node in new['certificate']['nodes'] if node['kind'] == 'split'}
                    self.assertTrue(splits <= set(new['resolving_set']))
                    self.assertEqual(len(new['resolving_set']), len(old['resolving_set']))
                else:
                    actual = _coordinates(prepared, new['coordinates'], lambda: None)
                    self.assertEqual(actual['euler_characteristic'], new['euler_characteristic'])
                    self.assertGreater(actual['euler_characteristic'], 0)

    def test_cache_eviction_preserves_positive_geometry(self):
        source = layered_torus(2)[0]
        with patch('fastunknot.normal_euler_transversal._CONFLICT_CACHE_LIMIT', 1):
            result = search_euler_transversal(source, candidate_policy='conflicts')
        self.assertEqual(result['status'], 'POSITIVE_EULER')
        self.assertEqual(result['stats']['peak_cached_conflicts'], 1)
        self.assertGreater(result['stats']['conflict_cache_evictions'], 0)
        ray = extract_positive_ray(source, result['coordinates'])
        packet = crush_normal_ray(source, ray['coordinates'])['certificate']
        self.assertTrue(verify_normal_crushing(source, packet))

    def test_caps_are_shared_across_depths_and_candidates(self):
        source = layered_torus(2)[0]
        mask = [(0, 1), (1, 0), (1, 1), (1, 2)]
        config = dict(candidate_policy='conflicts', strategy='anchors')
        full = search_euler_transversal(source, mask, **config)
        self.assertEqual(full['status'], 'NO_POSITIVE_EULER')
        mappings = [('max_nodes', 'nodes_attempted'), ('max_pivots', 'lp_pivots'),
                    ('max_anchors', 'anchors_tested'), ('max_hitting_subsets', 'hitting_subsets_tested')]
        for option, field in mappings:
            for cap in (0, full['stats'][field]-1):
                result = search_euler_transversal(source, mask, **config, **{option: cap})
                self.assertEqual(result['status'], 'INCONCLUSIVE', (option, cap))
                self.assertEqual(result['stats'][field], cap)
                self.assertNotIn('certificate', result)
        exact = {option: full['stats'][field] for option, field in mappings}
        self.assertEqual(search_euler_transversal(source, mask, **config, **exact), full)

    def test_fallback_caps_remain_global(self):
        source = layered_torus(2)[0]
        mask = [(0, 0), (1, 0), (1, 2)]
        config = dict(candidate_policy='conflicts', lp_fast_path_pivots=0)
        full = search_euler_transversal(source, mask, **config)
        self.assertEqual(full['status'], 'NO_POSITIVE_EULER')
        self.assertTrue(verify_euler_branch_tree(source, full['certificate']))
        for option, field in (('max_ellipsoid_iterations', 'lp_ellipsoid_iterations'),
                              ('max_feasibility_calls', 'lp_feasibility_calls')):
            cap = full['stats'][field]-1
            result = search_euler_transversal(source, mask, **config, **{option: cap})
            self.assertEqual(result['status'], 'INCONCLUSIVE')
            self.assertEqual(result['stats'][field], cap)
            self.assertNotIn('certificate', result)

    def test_callback_identity_and_strict_policy(self):
        source = layered_torus(2)[0]
        class CallerStop(BaseException):
            pass
        for kind in (ValueError, RuntimeError, CallerStop):
            error = kind('candidate filter cancellation')
            def stop(*args, **kwargs):
                raise error
            with patch('fastunknot.normal_euler_transversal._missed_conflict', stop):
                with self.assertRaises(kind) as caught:
                    search_euler_transversal(source, candidate_policy='conflicts')
            self.assertIs(caught.exception, error)
        for bad in (True, None, 'unknown', [], 0):
            with self.assertRaises(ValueError):
                search_euler_transversal(source, candidate_policy=bad)
            with self.assertRaises(ValueError):
                recognize_by_crushing(Diagram.from_pd([]), transversal_candidate_policy=bad)

    def test_diagram_replay_and_shared_successor_states(self):
        circle = Diagram.from_pd([])
        config = dict(sector_method='transversal', transversal_candidate_policy='conflicts', reduce_vertices=False)
        def reduction_first(source, **kwargs):
            allowed = [[t, 2] for t in range(5)] if len(source['tetrahedra']) == 5 else None
            return search_euler_transversal(source, allowed, **kwargs)
        with patch('fastunknot.normal_euler_transversal.search_euler_transversal', reduction_first):
            full = recognize_by_crushing(circle, **config)
            self.assertEqual(full['status'], 'UNKNOT')
            self.assertEqual(full['stats']['crushing_steps'], 3)
            self.assertEqual(full['stats']['hitting_subsets_tested'], 3)
            self.assertTrue(verify_crushing_recognition(circle, full['certificate']))
            for cap in (1, 2):
                result = recognize_by_crushing(circle, **config, max_hitting_subsets=cap)
                self.assertEqual(result['status'], 'INCONCLUSIVE')
                self.assertEqual(result['stats']['crushing_steps'], cap)
                self.assertEqual(result['stats']['hitting_subsets_tested'], cap)
                self.assertTrue(verify_crushing_chain(circle, result['partial_chain']))
        trefoil = Diagram.from_braid(2, [1, 1, 1])
        negative = recognize_by_crushing(trefoil, sector_method='transversal', transversal_candidate_policy='conflicts')
        self.assertEqual(negative['status'], 'KNOTTED')
        self.assertTrue(verify_crushing_recognition(trefoil, negative['certificate']))


if __name__ == '__main__':
    unittest.main()
