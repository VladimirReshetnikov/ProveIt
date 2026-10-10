from copy import deepcopy
import json
from math import factorial
from pathlib import Path
from unittest.mock import patch
import unittest

from fastunknot.cocycle_transport_verify import verify_cocycle_transport
from fastunknot.normal_cocycle import rank_one_cocycle_seed, CocycleLimit
from fastunknot.pachner_commitments import (
    search_pachner_endpoints, _Names, _State, _events, _advance, _state_key,
)
from fastunknot.pachner_commitments_verify import (
    inspect_pachner_endpoint, verify_pachner_endpoint,
)
from normal_orbit_research.fixtures import layered_torus
from commitment_research.fixtures import independent_bipyramids, endpoint_keys


class PachnerCommitmentTests(unittest.TestCase):
    def test_all_three_routes_cover_tiny_bounded_upward_families(self):
        for n, upward in ((1, 0), (2, 1), (3, 1)):
            raw, _ = layered_torus(n)
            heights = rank_one_cocycle_seed(raw)['heights']
            answers = []
            for method in ('naive', 'sleep', 'commitments'):
                result = search_pachner_endpoints(raw, heights, method=method,
                    max_upward=upward, max_nodes=None, collect_endpoints=True)
                self.assertEqual(result['status'], 'COMPLETE_BOUNDED_FAMILY')
                for proof in result['endpoints']:
                    self.assertTrue(verify_pachner_endpoint(raw, heights, proof))
                answers.append(endpoint_keys(raw, heights, result['endpoints']))
            self.assertEqual(answers[0], answers[1])
            self.assertEqual(answers[0], answers[2])

    def test_disjoint_geometric_moves_commute_with_exact_birth_ids(self):
        fixture = independent_bipyramids(2)
        raw, h = fixture['triangulation'], fixture['heights']
        state = _State(raw, h, tuple(range(6)), 0, 0, ())
        names = _Names(6)
        a, b = _events(state, False, lambda: None)
        self.assertTrue(a.cells.isdisjoint(b.cells))
        ab = _advance(_advance(state, a, names, lambda: None), b, names, lambda: None)
        ba = _advance(_advance(state, b, names, lambda: None), a, names, lambda: None)
        self.assertEqual(_state_key(ab), _state_key(ba))
        self.assertEqual(names.children(a), names.children(a))
        self.assertEqual(len(names.names), 10)

    def test_independent_geometric_family_removes_factorial_interleavings(self):
        for p in (1, 2, 3, 4):
            fixture = independent_bipyramids(p)
            raw, h = fixture['triangulation'], fixture['heights']
            expected_naive = sum(factorial(p)//factorial(p-j) for j in range(p+1))
            naive = search_pachner_endpoints(raw, h, method='naive', max_nodes=None,
                                             collect_endpoints=True)
            reduced = search_pachner_endpoints(raw, h, method='sleep', max_nodes=None,
                                               collect_endpoints=True)
            self.assertEqual(naive['stats']['nodes'], expected_naive)
            self.assertEqual(reduced['stats']['nodes'], 2**p)
            self.assertEqual(reduced['stats']['unique_endpoints'], 2**p)
            self.assertEqual(endpoint_keys(raw, h, naive['endpoints']),
                             endpoint_keys(raw, h, reduced['endpoints']))

    def test_restricted_source_footprint_and_independent_ancestry_replay(self):
        fixture = independent_bipyramids(3)
        raw, h = fixture['triangulation'], fixture['heights']
        active = fixture['regions'][1]
        answers = []
        for method in ('naive', 'sleep', 'commitments'):
            result = search_pachner_endpoints(raw, h, method=method,
                active_initial_tetrahedra=active, max_nodes=None, collect_endpoints=True)
            self.assertEqual(result['stats']['unique_endpoints'], 2)
            self.assertLessEqual(result['stats']['maximum_assigned_incarnations'], 9)
            for proof in result['endpoints']:
                summary = inspect_pachner_endpoint(raw, h, proof)
                self.assertIsNotNone(summary)
                self.assertTrue(set(summary['consumed_initial_tetrahedra']) <= set(active))
            answers.append(endpoint_keys(raw, h, result['endpoints']))
        self.assertEqual(answers[0], answers[1])
        self.assertEqual(answers[0], answers[2])
        forbidden = deepcopy(result['endpoints'][-1])
        forbidden['active_initial_tetrahedra'] = []
        self.assertFalse(verify_pachner_endpoint(raw, h, forbidden))

    def test_positive_endpoint_has_independent_source_bound_disc_proof(self):
        fixture = independent_bipyramids(1)
        raw, h = fixture['triangulation'], fixture['heights']
        result = search_pachner_endpoints(raw, h, method='sleep', seek_disc=True)
        self.assertEqual(result['status'], 'DISC_FOUND')
        proof = result['certificate']
        with patch('fastunknot.pachner_commitments.search_pachner_endpoints',
                   side_effect=AssertionError), \
             patch('fastunknot.cocycle_transport.transport_cocycle', side_effect=AssertionError), \
             patch('fastunknot.pachner23.pachner_23', side_effect=AssertionError), \
             patch('fastunknot.pachner32.pachner_32', side_effect=AssertionError), \
             patch('fastunknot.normal_disk_kernel.normal_compressing_disk_count',
                   side_effect=AssertionError):
            replay = inspect_pachner_endpoint(raw, h, proof)
            self.assertIsNotNone(replay)
            self.assertTrue(replay['contains_compressing_disk'])
        for bad in (None, {}, dict(proof, extra=1), dict(proof, max_upward=True),
                    dict(proof, coordinates=[]), dict(proof, moves=[{}]),
                    dict(proof, active_initial_tetrahedra=[False])):
            self.assertFalse(verify_pachner_endpoint(raw, h, bad))
        changed = deepcopy(proof)
        changed['coordinates'][0][0] += 1
        self.assertFalse(verify_pachner_endpoint(raw, h, changed))

    def test_caps_validation_callbacks_and_immutability(self):
        fixture = independent_bipyramids(1)
        raw, h = fixture['triangulation'], fixture['heights']
        saved = deepcopy((raw, h))
        for kwargs in (dict(max_nodes=0), dict(max_work=0)):
            self.assertEqual(search_pachner_endpoints(raw, h, **kwargs)['status'], 'INCONCLUSIVE')
        for kwargs in (dict(max_nodes=-1), dict(max_upward=True), dict(method='unknown'),
                       dict(active_initial_tetrahedra=[0, 0]), dict(seek_disc=1)):
            with self.assertRaises(ValueError):
                search_pachner_endpoints(raw, h, **kwargs)
        def abort():
            raise CocycleLimit('user cancellation')
        with self.assertRaisesRegex(CocycleLimit, 'user cancellation'):
            search_pachner_endpoints(raw, h, check=abort)
        def abort_endpoint(proof):
            raise CocycleLimit('endpoint cancellation')
        with self.assertRaisesRegex(CocycleLimit, 'endpoint cancellation'):
            search_pachner_endpoints(raw, h, endpoint=abort_endpoint)
        def select_mutated(proof):
            proof['coordinates'].clear()
            return True
        result = search_pachner_endpoints(raw, h, endpoint=select_mutated)
        self.assertEqual(result['status'], 'ENDPOINT_SELECTED')
        self.assertTrue(verify_pachner_endpoint(raw, h, result['certificate']))
        self.assertEqual((raw, h), saved)
        for operation in (lambda cb: search_pachner_endpoints(raw, h, method='sleep', check=cb),
                          lambda cb: verify_pachner_endpoint(raw, h, result['certificate'], check=cb)):
            seen = [0]
            def delayed():
                seen[0] += 1
                if seen[0] == 7:
                    raise RuntimeError('delayed stop')
            with self.assertRaisesRegex(RuntimeError, 'delayed stop'):
                operation(delayed)

    def test_maintained_coherent_obstruction_requires_a_move_then_has_disc(self):
        path = Path(__file__).resolve().parents[2]/'reports/79/repro/fast/commitment_research'/(
            'coherent-obstruction-certificate.json')
        source = json.loads(path.read_text())
        raw = source['moves'][-1]['triangulation']
        h = rank_one_cocycle_seed(raw)['heights']
        result = search_pachner_endpoints(raw, h, method='sleep', seek_disc=True)
        self.assertEqual(result['status'], 'DISC_FOUND')
        self.assertEqual(len(result['certificate']['moves']), 1)
        self.assertEqual(result['stats']['disc_queries'], 2)
        summary = inspect_pachner_endpoint(raw, h, result['certificate'])
        self.assertTrue(summary['contains_compressing_disk'])
        with patch('fastunknot.pachner_commitments._advance', side_effect=AssertionError), \
             patch('fastunknot.cocycle_transport.transport_cocycle', side_effect=AssertionError):
            self.assertTrue(verify_pachner_endpoint(raw, h, result['certificate']))
        for field in ('euler_jump', 'normal_disc_jump'):
            bad = deepcopy(result['certificate'])
            bad['moves'][0]['transport'][field] += 1
            self.assertFalse(verify_pachner_endpoint(raw, h, bad))
        for field, i in (('heights', 1), ('coordinates', 0)):
            bad = deepcopy(result['certificate'])
            bad['moves'][0]['transport'][field][0][i] += 1
            self.assertFalse(verify_pachner_endpoint(raw, h, bad))

    def test_binary_heights_and_exact_work_limit(self):
        raw, _ = layered_torus(2)
        h = rank_one_cocycle_seed(raw)['heights']
        selected = lambda proof: len(proof['moves']) == 1
        small = search_pachner_endpoints(raw, h, method='sleep', max_upward=1,
                                        endpoint=selected)
        scaled = [[(1 << 2048)*x+17*t for x in row] for t, row in enumerate(h)]
        big = search_pachner_endpoints(raw, scaled, method='sleep', max_upward=1,
                                      endpoint=selected)
        self.assertEqual(small['stats']['work'], big['stats']['work'])
        self.assertTrue(verify_pachner_endpoint(raw, scaled, big['certificate']))
        exact = small['stats']['work']
        enough = search_pachner_endpoints(raw, h, method='sleep', max_upward=1,
                                         endpoint=selected, max_work=exact)
        short = search_pachner_endpoints(raw, h, method='sleep', max_upward=1,
                                        endpoint=selected, max_work=exact-1)
        self.assertEqual(enough['status'], 'ENDPOINT_SELECTED')
        self.assertEqual(short['status'], 'INCONCLUSIVE')


if __name__ == '__main__':
    unittest.main()
