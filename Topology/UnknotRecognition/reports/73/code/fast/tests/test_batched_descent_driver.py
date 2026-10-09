"""Whole collapse trajectories, source-bound replay, and resource aborts."""
from copy import deepcopy
import json
import unittest
from unittest.mock import patch

from batched_descent_research.descend import descend, verify_descent_chain
from batched_descent_research.fixtures import inflate_disjoint, source_fixture
from fastunknot.integer_codec import json_safe
from fastunknot.normal_cocycle import CocycleLimit


class BatchedDescentDriverTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # A source-verified diagram exterior, followed by one certified 2--3
        # expansion.  The driver binds the resulting 21-tetrahedron source;
        # its chain does not assert a fresh knot-diagram correspondence.
        raw, heights, _ = source_fixture('unknot', 1)
        cls.tri, cls.heights, _, _ = inflate_disjoint(raw, heights, 1)
        cls.answer = descend(cls.tri, cls.heights, endpoint_disk_count=True)

    def test_complete_trajectory_and_endpoint_replay_without_producers(self):
        answer = json.loads(json.dumps(json_safe(self.answer)))
        self.assertEqual(answer['status'], 'STALLED')
        self.assertGreaterEqual(answer['stats']['committed_rounds'], 2)
        proof = answer['certificate']
        moves = sum(len(step['move']['regions']) for step in proof['steps'])
        self.assertEqual(moves, len(self.tri['tetrahedra'])-
                         len(proof['final']['triangulation']['tetrahedra']))
        self.assertTrue(all(step['peeling']['peeled_euler_gain'] >= 0
                            for step in proof['steps']))
        self.assertLessEqual(answer['stats']['final_edge_difference_bits'],
                             answer['stats']['initial_edge_difference_bits'])
        self.assertEqual(answer['endpoint_disk_count']['status'], 'COMPLETE')
        self.assertEqual(answer['endpoint_disk_count']['compressing_disk_components'], 1)
        with patch('fastunknot.cocycle_peeling.CocyclePeelingState', side_effect=AssertionError), \
             patch('fastunknot.pachner_batch.pachner_32_batch', side_effect=AssertionError), \
             patch('fastunknot.pachner_batch.select_disjoint_collapses', side_effect=AssertionError), \
             patch('fastunknot.normal_disk_kernel.normal_compressing_disk_count',
                   side_effect=AssertionError):
            self.assertTrue(verify_descent_chain(self.tri, self.heights, proof))

    def test_chain_corruption_and_source_binding(self):
        proof = self.answer['certificate']
        corrupt = []
        bad = deepcopy(proof)
        bad['steps'][0]['peeling']['peeled_euler_gain'] += 1
        corrupt.append(bad)
        bad = deepcopy(proof)
        bad['steps'][0]['move']['regions'][0][0]['vertices'][0] = 7
        corrupt.append(bad)
        bad = deepcopy(proof)
        del bad['steps'][1]
        corrupt.append(bad)
        bad = deepcopy(proof)
        bad['steps'].insert(1, deepcopy(bad['steps'][0]))
        corrupt.append(bad)
        bad = deepcopy(proof)
        bad['final']['heights'][0][0] += 1
        corrupt.append(bad)
        bad = deepcopy(proof)
        bad['disk_certificate']['compressing_disk_components'] += 1
        corrupt.append(bad)
        for i, bad in enumerate(corrupt):
            with self.subTest(corruption=i):
                self.assertFalse(verify_descent_chain(self.tri, self.heights, bad))
        scaled = [[2*value for value in row] for row in self.heights]
        self.assertFalse(verify_descent_chain(self.tri, scaled, proof))
        changed_source = deepcopy(self.tri)
        changed_source['different_source_tag'] = 'binding must fail'
        self.assertFalse(verify_descent_chain(changed_source, self.heights, proof))
        # Gauge constants are deliberately absent from the source cochain:
        # equal signed differences represent the very same input certificate.
        gauged = [[value+(i+1)*(1 << 5000) for value in row]
                  for i, row in enumerate(self.heights)]
        self.assertTrue(verify_descent_chain(self.tri, gauged, proof))

    def test_round_caps_work_limits_and_callback_cancellation(self):
        capped = descend(self.tri, self.heights, max_rounds=1)
        self.assertEqual(capped['status'], 'ROUND_LIMIT')
        self.assertEqual(capped['stats']['committed_rounds'], 1)
        self.assertTrue(verify_descent_chain(self.tri, self.heights, capped['certificate']))
        empty = descend(self.tri, self.heights, max_rounds=0)
        self.assertEqual(empty['status'], 'ROUND_LIMIT')
        self.assertEqual(empty['certificate']['steps'], [])
        self.assertTrue(verify_descent_chain(self.tri, self.heights, empty['certificate']))
        old_tri, old_h = deepcopy(self.tri), deepcopy(self.heights)
        with self.assertRaises(CocycleLimit):
            descend(self.tri, self.heights, max_work=capped['stats']['work']+10)
        self.assertEqual(self.tri, old_tri)
        self.assertEqual(self.heights, old_h)
        for operation in (
                lambda check: descend(self.tri, self.heights, check=check),
                lambda check: verify_descent_chain(self.tri, self.heights,
                    self.answer['certificate'], check=check)):
            calls = 0
            error = ValueError('caller cancelled geometric work')

            def cancel():
                nonlocal calls
                calls += 1
                if calls == 100:
                    raise error

            with self.assertRaises(ValueError) as caught:
                operation(cancel)
            self.assertIs(caught.exception, error)
        self.assertEqual(self.tri, old_tri)
        self.assertEqual(self.heights, old_h)


if __name__ == '__main__':
    unittest.main()
