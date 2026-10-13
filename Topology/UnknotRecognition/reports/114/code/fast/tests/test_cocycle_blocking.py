"""Blocking-flow invariants, adaptive handoff and nonrecursive traversal."""
import json
import unittest
from unittest.mock import patch

from fastunknot.cocycle_span import minimize_cocycle_span, _zero_block
from fastunknot.cocycle_span_verify import verify_cocycle_span
from fastunknot.normal_cocycle import _Budget, CocycleLimit
from fastunknot.integer_codec import json_safe


class CocycleBlockingTests(unittest.TestCase):
    def test_equal_cost_units_share_one_linear_block(self):
        for n in (16, 64, 256):
            vertices, heights = [[0, 1, 2, 3]]*n, [[0, 0, 0, 0]]*n
            result = minimize_cocycle_span(vertices, heights)
            stats = result['stats']
            self.assertEqual(stats['disc_count'], 0)
            self.assertEqual(stats['blocking_units'], n)
            self.assertEqual(stats['zero_searches'], 1)
            self.assertEqual(stats['dijkstra_searches'], 0)
            self.assertLess(stats['blocking_scans'], 40*n)
            self.assertTrue(verify_cocycle_span(vertices, heights, result['certificate']))

    def test_distinct_marginal_costs_trigger_bounded_handoff(self):
        n = 128
        vertices, heights = [[i]*4 for i in range(n)], [[0, 0, 0, i] for i in range(n)]
        result = minimize_cocycle_span(vertices, heights)
        stats = result['stats']
        self.assertEqual(stats['disc_count'], n*(n-1)//2)
        self.assertEqual(stats['zero_searches'], 2)
        self.assertEqual(stats['blocking_units'], 1)
        self.assertEqual(stats['dijkstra_searches'], n-1)
        self.assertEqual(stats['blocking_fallbacks'], 1)
        self.assertEqual(stats['blocking_restarts'], 0)
        self.assertLess(stats['blocking_scans'], 100*n)
        self.assertTrue(verify_cocycle_span(vertices, heights, result['certificate']))

    def test_zero_distance_evidence_restarts_batching_and_binary_scaling(self):
        vertices = [[2, 1, 0, 3], [3, 0, 1, 3], [1, 3, 2, 2], [1, 0, 1, 1],
                    [1, 2, 1, 2], [3, 3, 1, 3], [1, 2, 3, 0], [0, 1, 0, 2], [1, 0, 1, 3]]
        heights = [[2, -1, -3, -2], [-4, 1, -4, -3], [0, -3, 2, -4], [2, 0, -4, -2],
                   [-1, 3, -2, -2], [3, 1, -4, 0], [-1, -1, 3, 4], [3, -2, 2, 1], [1, -4, 4, -1]]
        small = minimize_cocycle_span(vertices, heights)
        self.assertEqual(small['stats']['disc_count'], 48)
        self.assertGreater(small['stats']['blocking_fallbacks'], 0)
        self.assertGreater(small['stats']['blocking_restarts'], 0)
        scale = 1 << 20000
        large_heights = [[scale*h for h in row] for row in heights]
        large = minimize_cocycle_span(vertices, large_heights)
        for key, value in small['stats'].items():
            self.assertEqual(large['stats'][key], value*scale if key in ('disc_count', 'initial_disc_count') else value)
        certificate = json.loads(json.dumps(json_safe(large['certificate'])))
        with patch('fastunknot.cocycle_span._zero_block', side_effect=AssertionError), \
             patch('fastunknot.cocycle_span.minimize_cocycle_span', side_effect=AssertionError):
            self.assertTrue(verify_cocycle_span(vertices, large_heights, certificate))

    def test_long_zero_cost_path_and_cycles_need_no_recursion(self):
        n = 2500
        graph = [[] for _ in range(n)]
        def add(u, v):
            i, j = len(graph[u]), len(graph[v])
            graph[u].append([v, j, 1, 0]); graph[v].append([u, i, 0, 0])
        for i in range(n-1): add(i, i+1)
        for i in range(3, n-1): add(i, i-2)
        stats = dict(zero_searches=0, blocking_phases=0, blocking_scans=0,
                     blocking_path_steps=0, blocking_units=0)
        sent = _zero_block(graph, [0]*n, 0, n-1, 1, _Budget(lambda: None, None), stats)
        self.assertEqual(sent, 1)
        self.assertEqual(stats['blocking_path_steps'], n-1)
        self.assertEqual(_zero_block(graph, [0]*n, 0, n-1, 1,
                                    _Budget(lambda: None, None), stats), 0)

    def test_caps_and_cancellation_cover_blocks_and_handoff(self):
        for vertices, heights in (([[0, 1, 2, 3]]*32, [[0, 0, 0, 0]]*32),
                                  ([[i]*4 for i in range(32)], [[0, 0, 0, i] for i in range(32)])):
            full = minimize_cocycle_span(vertices, heights)
            for cap in (0, full['stats']['work']//2, full['stats']['work']-1):
                with self.assertRaises(CocycleLimit):
                    minimize_cocycle_span(vertices, heights, max_work=cap)
            self.assertEqual(minimize_cocycle_span(vertices, heights, max_work=full['stats']['work'])['certificate'],
                             full['certificate'])
            calls = [0]
            def stop():
                calls[0] += 1
                if calls[0] == full['stats']['work']//2: raise RuntimeError('cancelled')
            with self.assertRaisesRegex(RuntimeError, 'cancelled'):
                minimize_cocycle_span(vertices, heights, check=stop)


if __name__ == '__main__':
    unittest.main()
