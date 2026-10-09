from copy import deepcopy
from itertools import combinations
import unittest
from unittest.mock import patch

from fastunknot.cocycle_transport_verify import verify_cocycle_transport
from fastunknot.normal_cocycle import rank_one_cocycle_seed, CocycleLimit
from fastunknot.pachner_commitments import search_pachner_endpoints
from fastunknot.pachner_commitments_verify import inspect_pachner_endpoint
from fastunknot.pachner_regions import search_pachner_regions
from fastunknot.pachner_cover_search import (
    search_pachner_cover, find_pachner_descent, _build_index,
)
from fastunknot.pachner_cover_verify import (
    inspect_pachner_cover, verify_pachner_cover,
    inspect_pachner_descent, verify_pachner_descent,
)
from commitment_research.fixtures import independent_bipyramids, endpoint_keys
from normal_orbit_research.fixtures import layered_torus
from causal_research.fixtures import descent_gadgets


def _component_count(graph, selected):
    remaining, components = set(selected), 0
    while remaining:
        components += 1
        pending = [remaining.pop()]
        while pending:
            neighbours = set(graph[pending.pop()]) & remaining
            remaining.difference_update(neighbours)
            pending.extend(neighbours)
    return components


class PachnerCoverTests(unittest.TestCase):
    def test_incidence_intersection_equals_literal_cover_oracle(self):
        graph = [{1}, {0, 2}, {1, 3, 4}, {2}, {2}, set()]
        all_subsets = [frozenset(s) for k in range(7)
                       for s in combinations(range(6), k)]
        for radius, components in ((0, 0), (3, 1), (4, 2), (6, 3)):
            stats = dict(regions_indexed=0, region_incidence_entries=0,
                         cover_intersections=0)
            index = _build_index(graph, radius, components, None, stats, lambda: None)
            expected = {s for s in all_subsets if len(s) <= radius
                        and _component_count(graph, s) <= components}
            self.assertEqual(set(map(frozenset, index.regions)), expected)
            for consumed in all_subsets:
                got = index.extend(None, consumed, stats, lambda: None)
                represented = expected if got is None else {
                    frozenset(index.regions[i]) for i in got}
                self.assertEqual(represented, {s for s in expected if consumed <= s})
                split = tuple(sorted(consumed))
                first = index.extend(None, split[::2], stats, lambda: None)
                sequential = index.extend(first, split[1::2], stats, lambda: None)
                self.assertEqual(sequential, got)
        # A disconnected consumed set can have a connected cover.  Rejecting
        # nonconnected prefixes would silently lose this permitted state.
        stats = dict(regions_indexed=0, region_incidence_entries=0,
                     cover_intersections=0)
        index = _build_index(graph, 3, 1, None, stats, lambda: None)
        self.assertTrue(index.extend(None, {0, 2}, stats, lambda: None))

    def test_union_matches_restart_and_naive_on_real_solid_tori(self):
        cases = []
        for n in (2, 3):
            raw, _ = layered_torus(n)
            cases.append((raw, rank_one_cocycle_seed(raw)['heights'], 2, 1, 1))
        fixture = independent_bipyramids(2)
        for radius, components in ((3, 1), (4, 2), (6, 1)):
            cases.append((fixture['triangulation'], fixture['heights'],
                          radius, components, 0))
        for raw, heights, radius, components, upward in cases:
            common = dict(max_region_size=radius, max_components=components,
                          max_upward=upward, max_nodes=None,
                          collect_endpoints=True, seek_disc=False)
            old = search_pachner_regions(raw, heights, method='sleep', **common)
            shared = search_pachner_cover(raw, heights, method='sleep', **common)
            naive = search_pachner_cover(raw, heights, method='naive', **common)
            self.assertEqual(old['status'], 'COMPLETE_BOUNDED_REGIONS')
            self.assertEqual(shared['status'], 'COMPLETE_BOUNDED_COVER_FAMILY')
            self.assertEqual(naive['status'], 'COMPLETE_BOUNDED_COVER_FAMILY')
            keys = endpoint_keys(raw, heights, old['endpoints'])
            self.assertEqual(endpoint_keys(raw, heights, shared['endpoints']), keys)
            self.assertEqual(endpoint_keys(raw, heights, naive['endpoints']), keys)
            self.assertLessEqual(shared['stats']['nodes'], old['stats']['nodes'])
            for proof in shared['endpoints']+naive['endpoints']:
                self.assertTrue(verify_pachner_cover(raw, heights, proof,
                    max_region_size=radius, max_components=components, max_upward=upward))

    def test_independent_moves_share_root_and_overlapping_prefixes(self):
        fixture = independent_bipyramids(4)
        raw, heights = fixture['triangulation'], fixture['heights']
        old = search_pachner_regions(raw, heights, max_region_size=3,
            max_nodes=None, seek_disc=False)
        shared = search_pachner_cover(raw, heights, max_region_size=3, max_nodes=None)
        self.assertEqual(shared['stats']['nodes'], 5)
        self.assertEqual(shared['stats']['unique_endpoints'], 5)
        self.assertEqual(shared['stats']['maximum_consumed_initial'], 3)
        self.assertEqual(shared['stats']['regions_indexed'], old['stats']['regions_started'])
        self.assertEqual(old['stats']['nodes'], old['stats']['regions_started']+4)
        self.assertLess(shared['stats']['work'], old['stats']['work'])

    def test_global_upward_bound_agrees_with_unrestricted_small_search(self):
        raw, _ = layered_torus(3)
        heights = rank_one_cocycle_seed(raw)['heights']
        common = dict(max_upward=1, method='sleep', max_nodes=None, collect_endpoints=True)
        full = search_pachner_endpoints(raw, heights, **common)
        shared = search_pachner_cover(raw, heights, max_region_size=3, **common)
        self.assertEqual(endpoint_keys(raw, heights, full['endpoints']),
                         endpoint_keys(raw, heights, shared['endpoints']))
        self.assertEqual(shared['stats']['maximum_upward'], 1)

    def test_cover_caps_are_fail_closed_and_exact_work_boundary_replays(self):
        fixture = independent_bipyramids(2)
        raw, heights = fixture['triangulation'], fixture['heights']
        for options in (dict(max_nodes=0), dict(max_regions=0), dict(max_regions=1),
                        dict(max_work=0)):
            answer = search_pachner_cover(raw, heights, max_region_size=3, **options)
            self.assertEqual(answer['status'], 'INCONCLUSIVE')
            self.assertNotIn('certificate', answer)
        whole = search_pachner_cover(raw, heights, max_region_size=3, max_nodes=None)
        exact = whole['stats']['work']
        enough = search_pachner_cover(raw, heights, max_region_size=3,
                                     max_nodes=None, max_work=exact)
        short = search_pachner_cover(raw, heights, max_region_size=3,
                                    max_nodes=None, max_work=exact-1)
        self.assertEqual(enough['status'], 'COMPLETE_BOUNDED_COVER_FAMILY')
        self.assertEqual(short['status'], 'INCONCLUSIVE')
        region_cap = whole['stats']['regions_indexed']
        self.assertEqual(search_pachner_cover(raw, heights, max_region_size=3,
            max_nodes=None, max_regions=region_cap)['status'], 'COMPLETE_BOUNDED_COVER_FAMILY')

    def test_input_validation_and_callback_exceptions(self):
        fixture = independent_bipyramids(1)
        raw, heights = fixture['triangulation'], fixture['heights']
        for options in (dict(max_region_size=True), dict(max_components=-1),
                        dict(max_upward=1.5), dict(method='commitments'),
                        dict(max_regions=False), dict(max_nodes=-1),
                        dict(max_cycles=True), dict(seek_disc=1), dict(endpoint=3)):
            with self.assertRaises(ValueError):
                search_pachner_cover(raw, heights, **({'max_region_size': 3} | options))
        def abort():
            raise CocycleLimit('user cancellation')
        with self.assertRaisesRegex(CocycleLimit, 'user cancellation'):
            search_pachner_cover(raw, heights, max_region_size=3, check=abort)
        def abort_endpoint(proof):
            raise CocycleLimit('endpoint cancellation')
        with self.assertRaisesRegex(CocycleLimit, 'endpoint cancellation'):
            search_pachner_cover(raw, heights, max_region_size=3, endpoint=abort_endpoint)
        class FailingTruthValue:
            def __bool__(self):
                raise CocycleLimit('truth conversion cancellation')
        with self.assertRaisesRegex(CocycleLimit, 'truth conversion cancellation'):
            search_pachner_cover(raw, heights, max_region_size=3,
                                  endpoint=lambda proof: FailingTruthValue())
        calls = [0]
        def delayed():
            calls[0] += 1
            if calls[0] == 300:
                raise RuntimeError('delayed cancellation')
        with self.assertRaisesRegex(RuntimeError, 'delayed cancellation'):
            search_pachner_cover(raw, heights, max_region_size=3, check=delayed)

    def test_callbacks_cannot_mutate_search_or_returned_certificate(self):
        fixture = independent_bipyramids(1)
        raw, heights = fixture['triangulation'], fixture['heights']
        saved = deepcopy((raw, heights))
        def mutate_and_select(proof):
            proof['coordinates'].clear()
            proof['active_initial_tetrahedra'].clear()
            return True
        answer = search_pachner_cover(raw, heights, max_region_size=3,
                                      endpoint=mutate_and_select)
        self.assertEqual(answer['status'], 'ENDPOINT_SELECTED')
        self.assertTrue(verify_pachner_cover(raw, heights, answer['certificate'],
                                            max_region_size=3))
        self.assertEqual((raw, heights), saved)

    def test_disc_certificate_is_replayed_without_producers(self):
        fixture = independent_bipyramids(1)
        raw, heights = fixture['triangulation'], fixture['heights']
        answer = search_pachner_cover(raw, heights, max_region_size=3, seek_disc=True)
        self.assertEqual(answer['status'], 'DISC_FOUND')
        with patch('fastunknot.pachner_cover_search.search_pachner_cover',
                   side_effect=AssertionError), \
             patch('fastunknot.cocycle_transport.transport_cocycle', side_effect=AssertionError), \
             patch('fastunknot.pachner23.pachner_23', side_effect=AssertionError), \
             patch('fastunknot.pachner32.pachner_32', side_effect=AssertionError), \
             patch('fastunknot.normal_disk_kernel.normal_compressing_disk_count',
                   side_effect=AssertionError):
            replay = inspect_pachner_cover(raw, heights, answer['certificate'],
                                          max_region_size=3)
            self.assertTrue(replay['contains_compressing_disk'])

    def test_descent_wrapper_and_independent_strictness_checks(self):
        fixture = independent_bipyramids(2)
        raw, heights = fixture['triangulation'], fixture['heights']
        answer = find_pachner_descent(raw, heights, max_upward=0, max_nodes=None)
        self.assertEqual(answer['status'], 'DESCENT_FOUND')
        self.assertEqual(answer['descent']['initial_tetrahedra'], 6)
        self.assertEqual(answer['descent']['final_tetrahedra'], 5)
        self.assertEqual(answer['descent']['upward_moves'], 0)
        proof = answer['certificate']
        with patch('fastunknot.pachner_cover_search.find_pachner_descent',
                   side_effect=AssertionError), \
             patch('fastunknot.pachner_cover_search._advance', side_effect=AssertionError), \
             patch('fastunknot.cocycle_transport.transport_cocycle', side_effect=AssertionError):
            self.assertTrue(verify_pachner_descent(raw, heights, proof, max_upward=0))
        empty = search_pachner_cover(raw, heights, max_region_size=0,
            endpoint=lambda proof: True)['certificate']
        self.assertFalse(verify_pachner_descent(raw, heights, empty, max_upward=0))
        self.assertFalse(verify_pachner_descent(raw, heights, proof,
                                              max_upward=0, max_region_size=2))
        corrupted = deepcopy(proof)
        corrupted['moves'][0]['transport']['euler_jump'] += 1
        self.assertFalse(verify_pachner_descent(raw, heights, corrupted, max_upward=0))
        for options in (dict(max_nodes=0), dict(max_work=0), dict(max_regions=0)):
            limited = find_pachner_descent(raw, heights, max_upward=0, **options)
            self.assertEqual(limited['status'], 'INCONCLUSIVE')

    def test_complete_descent_scope_and_small_radius_are_distinct(self):
        raw, _ = layered_torus(2)
        heights = rank_one_cocycle_seed(raw)['heights']
        full = find_pachner_descent(raw, heights, max_upward=0, max_nodes=None)
        local = find_pachner_descent(raw, heights, max_upward=0,
                                    max_region_size=0, max_nodes=None)
        self.assertEqual(full['status'], 'COMPLETE_BOUNDED_DESCENT')
        self.assertTrue(full['descent_scope']['covers_all_bounded_upward_descents'])
        self.assertEqual(local['status'], 'COMPLETE_BOUNDED_LOCAL_DESCENT')
        self.assertFalse(local['descent_scope']['covers_all_bounded_upward_descents'])

    def test_verifier_independently_rejects_disconnected_cover(self):
        fixture = independent_bipyramids(2)
        raw, heights = fixture['triangulation'], fixture['heights']
        source = search_pachner_cover(raw, heights, max_region_size=0,
            endpoint=lambda proof: True)['certificate']
        rows = raw['tetrahedra']
        pair = next((a, b) for a, b in combinations(range(6), 2)
                    if all(entry is None or entry['tetrahedron'] != b for entry in rows[a]))
        proof = dict(source, active_initial_tetrahedra=list(pair))
        self.assertIsNotNone(inspect_pachner_endpoint(raw, heights, proof))
        self.assertFalse(verify_pachner_cover(raw, heights, proof,
                                             max_region_size=2, max_components=1))
        self.assertTrue(verify_pachner_cover(raw, heights, proof,
                                            max_region_size=2, max_components=2))

    def test_genuine_one_upward_descent_and_six_cell_consumption(self):
        fixture = descent_gadgets(1)
        raw, heights = fixture['triangulation'], fixture['heights']
        zero = find_pachner_descent(raw, heights, max_upward=0, max_nodes=None)
        small = find_pachner_descent(raw, heights, max_upward=1,
                                     max_region_size=5, max_nodes=None)
        enough = find_pachner_descent(raw, heights, max_upward=1, max_nodes=None)
        self.assertEqual(zero['status'], 'COMPLETE_BOUNDED_DESCENT')
        self.assertEqual(small['status'], 'COMPLETE_BOUNDED_LOCAL_DESCENT')
        self.assertEqual(enough['status'], 'DESCENT_FOUND')
        proof = enough['certificate']
        replay = inspect_pachner_descent(raw, heights, proof, max_upward=1)
        self.assertEqual((replay['upward_moves'], replay['downward_moves']), (1, 2))
        self.assertEqual(len(replay['consumed_initial_tetrahedra']), 6)
        self.assertEqual((replay['initial_tetrahedra'], replay['final_tetrahedra']), (7, 6))
        self.assertFalse(verify_pachner_descent(raw, heights, proof, max_upward=0))

    def test_lazy_transport_respects_cap_before_unvisited_children(self):
        fixture = descent_gadgets(3)
        raw, heights = fixture['triangulation'], fixture['heights']
        with patch('fastunknot.pachner_cover_search._advance', side_effect=AssertionError):
            answer = search_pachner_cover(raw, heights, max_region_size=6,
                                          max_upward=1, max_nodes=1)
        self.assertEqual(answer['status'], 'INCONCLUSIVE')
        self.assertEqual(answer['stats']['nodes'], 1)
        self.assertEqual(answer['stats']['moves'], 0)

    def test_capped_endpoint_query_never_becomes_complete_negative(self):
        fixture = independent_bipyramids(1)
        with patch('fastunknot.normal_disk_kernel.normal_compressing_disk_count',
                   return_value={'status': 'INCONCLUSIVE'}):
            answer = search_pachner_cover(fixture['triangulation'], fixture['heights'],
                max_region_size=0, seek_disc=True, max_cycles=0, max_nodes=None)
        self.assertEqual(answer['status'], 'INCONCLUSIVE')
        self.assertEqual(answer['stats']['incomplete_disc_queries'], 1)
        self.assertNotIn('certificate', answer)


if __name__ == '__main__':
    unittest.main()
