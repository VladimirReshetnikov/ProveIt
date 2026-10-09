"""Independent exhaustive checks of the two-endpoint matching reduction."""
from copy import deepcopy
from importlib.util import find_spec
import random
import unittest
from unittest.mock import patch

from fastunknot.peeled_batch_selection import (
    evaluate_two_endpoint_rewards, exhaustive_optimum,
    solve_two_endpoint_rewards, two_endpoint_matching_reduction,
    verify_matching_dual, verify_selection_value)


requires_networkx = unittest.skipUnless(find_spec('networkx') is not None,
                                       'optional networkx matching backend absent')


class PeeledBatchSelectionTests(unittest.TestCase):
    @requires_networkx
    def test_shared_interior_apex_geometric_rewards(self):
        # Actual 32-tetrahedron counterexample: both moves share interior
        # v=0 and each has a separate boundary apex.  Each singleton has
        # peeled gain 1; executing both has gain 0.  Omit exactly one.
        items = [dict(cost=2, rewards=[[0, 2], [1, 1]]),
                 dict(cost=2, rewards=[[0, 2], [2, 1]])]
        answer = solve_two_endpoint_rewards(items)
        self.assertEqual(answer['objective'], 1)
        self.assertEqual(len(answer['omitted_indices']), 1)
        self.assertEqual(answer['baseline_value'], 0)
        self.assertTrue(answer['costs_dominate_endpoint_rewards'])
        self.assertTrue(verify_selection_value(items, answer))

    @requires_networkx
    def test_random_general_instances_against_all_subsets(self):
        rng = random.Random(261009701)
        for _ in range(200):
            vertices, size = rng.randrange(1, 8), rng.randrange(10)
            items = []
            for i in range(size):
                entries = [[rng.randrange(vertices), rng.randrange(12)]
                           for _ in range(rng.randrange(3))]
                items.append(dict(cost=rng.randrange(12), rewards=entries))
            answer = solve_two_endpoint_rewards(items)
            reference = exhaustive_optimum(items, max_items=10)
            self.assertEqual(answer['objective'], reference['objective'], items)
            self.assertTrue(verify_selection_value(items, answer))
            self.assertEqual(set(answer['retained_indices']) |
                             set(answer['omitted_indices']), set(range(size)))

    @requires_networkx
    def test_loops_parallel_edges_zero_costs_and_large_integers(self):
        large = 1 << 200
        items = [dict(cost=0, rewards=[[0, 3], [0, 5]]),
                 dict(cost=3, rewards=[[0, 7], [1, 8]]),
                 dict(cost=2, rewards=[[1, 8], [0, 7]]),
                 dict(cost=large, rewards=[[1, large+9], [2, large+3]]),
                 dict(cost=0, rewards=[])]
        saved = deepcopy(items)
        answer = solve_two_endpoint_rewards(items)
        reference = exhaustive_optimum(items)
        self.assertEqual(answer['objective'], reference['objective'])
        self.assertEqual(items, saved)
        self.assertEqual(evaluate_two_endpoint_rewards(items, [0]), 5)
        self.assertTrue(verify_selection_value(items, answer))
        reduction = two_endpoint_matching_reduction(items)
        self.assertTrue(all(e['weight'] > 0 for e in reduction['edges']))

    @requires_networkx
    def test_dominated_endpoint_case_has_no_singleton_choices(self):
        rng = random.Random(261009702)
        for _ in range(100):
            items = []
            for i in range(rng.randrange(10)):
                cost = rng.randrange(10)
                items.append(dict(cost=cost,
                    rewards=[[rng.randrange(6), rng.randrange(cost+1)]
                             for _ in range(rng.randrange(3))]))
            answer = solve_two_endpoint_rewards(items)
            self.assertEqual(answer['singleton_items'], [])
            self.assertEqual(answer['baseline_value'], 0)
            reference = exhaustive_optimum(items)
            self.assertEqual(answer['objective'], reference['objective'])
            self.assertEqual(len(answer['omitted_indices']), len(reference['omitted_indices']))
            self.assertTrue(answer['maximum_retention_tie_break'])

    @requires_networkx
    def test_equal_weight_matchings_prefer_fewer_omissions(self):
        # Two outer weight-one edges tie the central weight-two edge.
        # Merely dropping zero-weight edges would not decide cardinality.
        items = [dict(cost=2, rewards=[[0, 1], [1, 2]]),
                 dict(cost=2, rewards=[[1, 2], [2, 2]]),
                 dict(cost=2, rewards=[[2, 2], [3, 1]])]
        answer = solve_two_endpoint_rewards(items)
        self.assertEqual(answer['omitted_indices'], [1])
        self.assertEqual(answer['objective'], 2)
        witness = dict(denominator=1, vertices=[[1, 1], [2, 1]], odd_sets=[])
        self.assertTrue(verify_matching_dual(items, answer['matching_items'], witness))

    def test_edmonds_dual_independent_checker_and_tampering(self):
        # Unit triangle: vertex constraints alone have a fractional gap;
        # the odd-set price gives the exact integral matching bound.
        items = [dict(cost=1, rewards=[[u, 1], [v, 1]])
                 for u, v in ((0, 1), (1, 2), (0, 2))]
        witness = dict(denominator=1, vertices=[],
                       odd_sets=[dict(vertices=[0, 1, 2], price=1)])
        self.assertTrue(verify_matching_dual(items, [0], witness))
        for mutate in (
            lambda d: d.update(denominator=0),
            lambda d: d.update(odd_sets=[]),
            lambda d: d['odd_sets'][0].update(price=2),
            lambda d: d['odd_sets'][0].update(vertices=[0, 1]),
            lambda d: d['odd_sets'][0].update(vertices=[0, 0, 1]),
            lambda d: d['odd_sets'][0].update(vertices=[0, 1, 9]),
            lambda d: d.update(vertices=[[0, -1]]),
            lambda d: d.update(vertices=[[0, 0], [0, 0]])):
            altered = deepcopy(witness)
            mutate(altered)
            self.assertFalse(verify_matching_dual(items, [0], altered), altered)
        self.assertFalse(verify_matching_dual(items, [], witness))
        self.assertFalse(verify_matching_dual(items, [0, 1], witness))
        self.assertTrue(verify_matching_dual([], [],
            dict(denominator=1, vertices=[], odd_sets=[])))

    def test_two_vertex_cover_against_all_subsets_without_networkx(self):
        rng = random.Random(261009703)
        with patch.dict('sys.modules', {'networkx': None}):
            for dominated in (False, True):
                for _ in range(150):
                    items = []
                    for i in range(rng.randrange(10)):
                        cost = rng.randrange(12)
                        upper = cost+1 if dominated else 16
                        entries = [[rng.randrange(2), rng.randrange(upper)],
                                   [rng.randrange(7), rng.randrange(upper)]]
                        if rng.randrange(5) == 0:
                            entries = entries[:rng.randrange(2)]
                        items.append(dict(cost=cost, rewards=entries))
                    answer = solve_two_endpoint_rewards(items, cover_vertices=[0, 1])
                    reference = exhaustive_optimum(items)
                    self.assertEqual(answer['objective'], reference['objective'], items)
                    if dominated:
                        self.assertEqual(len(answer['omitted_indices']),
                                         len(reference['omitted_indices']))
                        self.assertLessEqual(len(answer['omitted_indices']), 2)
                    self.assertEqual(answer['optimality_basis'],
                                     'two-vertex-cover-exact-enumeration')
                    self.assertTrue(verify_selection_value(items, answer))

    def test_two_vertex_cover_parallel_loops_endpoint_collision_and_tie(self):
        # Both poles prefer outside vertex 2; their second choices must be
        # considered. The pole-pole edge ties the best two-edge matching,
        # and the smaller omission set wins.
        items = [dict(cost=10, rewards=[[0, 10], [2, 9]]),
                 dict(cost=10, rewards=[[0, 10], [3, 7]]),
                 dict(cost=10, rewards=[[1, 10], [2, 8]]),
                 dict(cost=10, rewards=[[1, 10], [4, 6]]),
                 dict(cost=10, rewards=[[0, 10], [2, 8]]),
                 dict(cost=15, rewards=[[0, 15], [1, 15]]),
                 dict(cost=1, rewards=[[0, 1], [0, 1]]),
                 dict(cost=0, rewards=[])]
        with patch.dict('sys.modules', {'networkx': None}):
            answer = solve_two_endpoint_rewards(items, cover_vertices=[1, 0])
            self.assertEqual(answer['objective'], 15)
            self.assertEqual(answer['omitted_indices'], [5])
            without_central = items[:5]+items[6:]
            answer = solve_two_endpoint_rewards(without_central, cover_vertices=[0, 1])
            self.assertEqual(answer['objective'], 15)
            self.assertEqual(len(answer['omitted_indices']), 2)
            self.assertEqual(solve_two_endpoint_rewards(
                items[:2], cover_vertices=[0])['omitted_indices'], [0])
            self.assertEqual(solve_two_endpoint_rewards(
                [], cover_vertices=[])['objective'], 0)
            large = 1 << 200
            big = [dict(cost=large, rewards=[[0,large],[1,large]])]
            self.assertEqual(solve_two_endpoint_rewards(
                big, cover_vertices=[0])['objective'], large)

    def test_invalid_small_vertex_covers(self):
        items = [dict(cost=1, rewards=[[0,1],[1,1]])]
        for cover in ({0}, [0, 0], [0, 1, 2], [True], ['0'], [], [7, 8]):
            with self.assertRaises(ValueError):
                solve_two_endpoint_rewards(items, cover_vertices=cover)

    def test_invalid_inputs_and_explicit_exhaustive_limit(self):
        for items in (None, {}, [dict(cost=-1, rewards=[])],
                      [dict(cost=True, rewards=[])],
                      [dict(cost=1, rewards=[[0, -1]])],
                      [dict(cost=1, rewards=[[True, 2]])],
                      [dict(cost=1, rewards=[[0, 1], [1, 1], [2, 1]])],
                      [dict(cost=1, rewards=[], extra=1)]):
            with self.assertRaises(ValueError):
                two_endpoint_matching_reduction(items)
        with self.assertRaises(ValueError):
            exhaustive_optimum([dict(cost=0, rewards=[])]*4, max_items=3)
        self.assertFalse(verify_selection_value([], dict(objective=True, omitted_indices=[])))
        self.assertFalse(verify_selection_value([], dict(objective=0, omitted_indices=[0])))
        self.assertFalse(verify_selection_value([dict(cost=0,rewards=[])],
                                               dict(objective=0,omitted_indices=[0,0])))
        self.assertEqual(solve_two_endpoint_rewards([])['objective'], 0)

    def test_callback_cancellation(self):
        def cancel():
            raise RuntimeError('stop selection')
        with self.assertRaisesRegex(RuntimeError, 'stop selection'):
            solve_two_endpoint_rewards([dict(cost=1,rewards=[[0,1]])], check=cancel)
        with self.assertRaisesRegex(RuntimeError, 'stop selection'):
            exhaustive_optimum([], check=cancel)
        def cancel_value():
            raise ValueError('stop verification')
        items = [dict(cost=1,rewards=[[0,1]])]
        with self.assertRaisesRegex(ValueError, 'stop verification'):
            verify_selection_value(items, dict(objective=0,omitted_indices=[0]),
                                   check=cancel_value)
        with self.assertRaisesRegex(ValueError, 'stop verification'):
            verify_matching_dual(items, [],
                dict(denominator=1,vertices=[],odd_sets=[]), check=cancel_value)


if __name__ == '__main__':
    unittest.main()
