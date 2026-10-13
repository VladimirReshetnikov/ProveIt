import copy
from itertools import product
import random
import unittest
from unittest.mock import patch

from activation_forests import from_dense, parameters, solve, verify_result, verify_success
from activation_forests.model import parse_problem
from activation_forests.oracle import tree_oracle
from activation_forests.solver import Work, _rainbow


class ActivationForestTests(unittest.TestCase):
    forest_oracle_cases = 0
    cloned_rado_oracle_cases = 0

    def assert_exact(self, problem, pivots=False):
        type(self).forest_oracle_cases += 1
        result = solve(problem)
        reference = tree_oracle(problem, positive_pivots=pivots)
        self.assertEqual(result['status'], reference['status'], (problem, result, reference))
        self.assertTrue(verify_result(problem, result), (problem, result))
        return result

    def test_empty_and_disconnected_namespaces(self):
        self.assert_exact(from_dense(1, [], []))
        self.assert_exact(from_dense(2, [None], [[]]))
        large = from_dense(1 << 16384, [[0, 1]], [[]])
        result = solve(large)
        self.assertEqual(result['status'], 'NO_FOREST')
        self.assertTrue(verify_result(large, result))

    def test_triangle_and_parallel_triple(self):
        yes = from_dense(3, [[0, 1], [1, 2], [2, 0]], [[1], [1], [1]])
        no = from_dense(2, [[0, 1]] * 3, [[1], [1], [1]])
        self.assertEqual(self.assert_exact(yes, True)['status'], 'SUCCESS')
        result = self.assert_exact(no, True)
        self.assertEqual(result['certificate']['kind'], 'exhaustive_scenarios')
        self.assertEqual(len(result['certificate']['branches']), 3)

    def test_shared_witness_requires_partition_block(self):
        # Rows d,w,x,y; the two demands of output w have the same only
        # available tree slot.  One seed d satisfies both antecedents.
        problem = from_dense(2, [[0, 1], [0, 1], [0, 1], [0, 0]],
                             [[1, 1, 2, 0], [1, 0, 0, 1],
                              [0, 1, 0, 1], [0, 0, 1, 1]])
        result = self.assert_exact(problem, True)
        self.assertEqual(result['selected_scenario']['partition'], [0, 0])
        self.assertEqual(result['certificate']['tree'], [0])

    def test_future_output_cannot_seed_earlier_event(self):
        # b,d have free singletons; a,c depend cyclically on each other.
        problem = from_dense(1, [[0, 0]] * 4,
                             [[0, 0, 1, 1], [1, 0, 1, 0],
                              [0, 0, 1, 1], [0, 1, 0, 1]])
        result = self.assert_exact(problem, True)
        self.assertEqual(result['status'], 'NO_FOREST')

    def test_initial_closure_preserves_graph_edges(self):
        # All four rows are initially free, but three of them still have
        # to be available as a spanning tree of the source graph.
        problem = from_dense(4, [[0, 1], [1, 2], [2, 3], [0, 0]],
                             [[1, 0, 0, 0, 1], [0, 1, 0, 0, 1],
                              [0, 0, 1, 0, 1], [0, 0, 0, 1, 0]])
        pars = parameters(problem)
        self.assertEqual(pars['raw_exceptional_columns'], 1)
        self.assertEqual(pars['exceptional_columns'], 0)
        result = self.assert_exact(problem, True)
        self.assertEqual(len(result['certificate']['tree']), 3)

    def test_general_nonunit_exception_and_binary_counts(self):
        problem = from_dense(3, [[0, 1], [1, 2], [0, 0]], [[2], [3], [1]])
        self.assert_exact(problem, True)
        huge = from_dense(3, [[0, 1], [1, 2], [0, 0]], [[1 << 16384], [3], [1]])
        result = self.assert_exact(huge, True)
        self.assertEqual(result['status'], 'SUCCESS')
        forged = copy.deepcopy(huge)
        forged['rows'][0][0][1] += 1
        self.assertFalse(verify_result(forged, result))

    def test_positive_replay_has_no_producer_dependency(self):
        problem = from_dense(3, [[0, 1], [1, 2], [2, 0]], [[1], [1], [1]])
        result = solve(problem)
        with patch('activation_forests.solver.solve', side_effect=AssertionError), \
             patch('activation_forests.solver._peel', side_effect=AssertionError), \
             patch('activation_forests.solver._compile', side_effect=AssertionError):
            self.assertTrue(verify_success(problem, result))
        bad = copy.deepcopy(result)
        bad['certificate']['peeling'][0][1] += 1
        self.assertFalse(verify_result(problem, bad))

    def test_negative_replay_has_no_producer_dependency(self):
        problem = from_dense(2, [[0, 1]] * 3, [[1], [1], [1]])
        result = solve(problem)
        with patch('activation_forests.solver._rainbow', side_effect=AssertionError), \
             patch('activation_forests.solver._compile', side_effect=AssertionError), \
             patch('activation_forests.solver._partitions', side_effect=AssertionError):
            self.assertTrue(verify_result(problem, result))
        for edit in ('branch', 'rank', 'output'):
            bad = copy.deepcopy(result)
            if edit == 'branch':
                bad['certificate']['branches'].pop()
            elif edit == 'rank':
                bad['certificate']['branches'][0]['rank'] += 1
            else:
                bad['certificate']['branches'][0]['outputs'][0] = 2
            self.assertFalse(verify_result(problem, bad), edit)

    def test_resource_limits_are_inconclusive(self):
        problem = from_dense(2, [[0, 1]] * 3, [[1], [1], [1]])
        for limits in ({'max_work': 0}, {'max_scenarios': 0}):
            result = solve(problem, **limits)
            self.assertEqual(result['status'], 'INCONCLUSIVE')
            self.assertNotIn('certificate', result)
            self.assertFalse(verify_result(problem, result))
        with self.assertRaises(ValueError):
            solve(problem, max_work=True)
        shared = from_dense(2, [[0, 1], [0, 1], [0, 1], [0, 0]],
                            [[1, 1, 2, 0], [1, 0, 0, 1],
                             [0, 1, 0, 1], [0, 0, 1, 1]])
        limited = solve(shared, max_partitions=0)
        self.assertEqual(limited['status'], 'INCONCLUSIVE')
        self.assertNotIn('certificate', limited)

    def test_complete_negative_partition_coverage(self):
        problem = from_dense(2, [[0, 1]] * 3, [[1, 1, 1]] * 3)
        result = self.assert_exact(problem, True)
        proof = result['certificate']
        self.assertEqual(proof['kind'], 'exhaustive_scenarios')
        branches = [b for b in proof['branches'] if b['kind'] == 'partitions']
        self.assertTrue(branches)
        self.assertTrue(any(len(b['failures']) > 1 for b in branches))
        bad = copy.deepcopy(result)
        branch = next(b for b in bad['certificate']['branches']
                      if b['kind'] == 'partitions' and len(b['failures']) > 1)
        branch['failures'][1] = copy.deepcopy(branch['failures'][0])
        self.assertFalse(verify_result(problem, bad))
        branch['failures'].pop()
        self.assertFalse(verify_result(problem, bad))

    def test_raw_parity_never_uses_capped_counts(self):
        compatible = from_dense(2, [[0, 1]] * 2, [[3], [1]])
        incompatible = from_dense(2, [[0, 1]] * 2, [[3], [2]])
        self.assertTrue(parameters(compatible)['raw_parity'])
        self.assertFalse(parameters(incompatible)['raw_parity'])
        self.assert_exact(compatible, True)
        result = self.assert_exact(incompatible, True)
        self.assertFalse(result['certificate']['rank_layer'])
        result['certificate']['rank_layer'] = True
        self.assertFalse(verify_result(incompatible, result))

    def test_cycle_compatible_cardinality_pruning(self):
        # Two parallel pairs, and a loop in each triple.  Deleting all
        # eligible edges exposes the loop, but rank one cannot seed both
        # dependencies.  Every nonlinear scenario has too many source groups.
        problem = from_dense(2, [[0, 1]] * 4 + [[0, 0]],
                             [[1, 0], [1, 0], [0, 1], [0, 1], [1, 1]])
        self.assertTrue(parameters(problem)['raw_parity'])
        result = self.assert_exact(problem, True)
        self.assertTrue(result['certificate']['rank_layer'])
        self.assertGreater(result['stats']['rank_layer_pruned_scenarios'], 0)
        ordinary = solve(problem, use_rank_layer=False)
        self.assertEqual(ordinary['status'], result['status'])
        self.assertTrue(verify_result(problem, ordinary))
        self.assertGreater(ordinary['stats'].get('graphic_oracle_calls', 0),
                           result['stats'].get('graphic_oracle_calls', 0))

    def test_exhaustive_three_rows_two_columns(self):
        geometries = [
            (1, [[0, 0]] * 3),
            (2, [[0, 1]] * 3),
            (2, [[0, 1], [0, 0], None]),
            (3, [[0, 1], [1, 2], [2, 0]]),
        ]
        for entries in product(range(3), repeat=6):
            rows = [list(entries[i:i + 2]) for i in (0, 2, 4)]
            for vertices, edges in geometries:
                self.assert_exact(from_dense(vertices, edges, rows), True)

    def test_random_unit_triples(self):
        rng = random.Random(0xA671)
        for _ in range(1800):
            n, m, width = rng.randrange(1, 5), rng.randrange(1, 8), rng.randrange(0, 5)
            edges = [None if rng.randrange(7) == 0 else [rng.randrange(n), rng.randrange(n)]
                     for _ in range(m)]
            matrix = [[0] * width for _ in range(m)]
            for c in range(width):
                support = rng.sample(range(m), rng.randrange(min(3, m) + 1))
                for r in support:
                    matrix[r][c] = 1 if len(support) == 3 else rng.choice((1, 1, 2))
            self.assert_exact(from_dense(n, edges, matrix))

    def test_general_support_and_nonunit_targets(self):
        rng = random.Random(0xED63)
        for _ in range(400):
            n, m = rng.randrange(1, 5), rng.randrange(3, 7)
            edges = [None if rng.randrange(7) == 0 else [rng.randrange(n), rng.randrange(n)]
                     for _ in range(m)]
            matrix = [[rng.choice((0, 1, 1, 2)), 0, 0] for _ in range(m)]
            for c in (1, 2):
                for r in rng.sample(range(m), rng.randrange(3)):
                    matrix[r][c] = rng.choice((1, 2))
            self.assert_exact(from_dense(n, edges, matrix), True)

    def test_cloned_rado_solver_against_direct_representatives(self):
        rng = random.Random(0xB211)
        for _ in range(800):
            type(self).cloned_rado_oracle_cases += 1
            n, m = rng.randrange(1, 6), rng.randrange(1, 8)
            edges = [None if rng.randrange(8) == 0 else [rng.randrange(n), rng.randrange(n)]
                     for _ in range(m)]
            problem = from_dense(n, edges, [[] for _ in edges])
            groups = [set(r for r in range(m) if rng.randrange(2))
                      for _ in range(rng.randrange(5))]
            data = parse_problem(problem)
            selected, obstruction = _rainbow(data, groups, Work())
            exists = False
            for representatives in product(*(sorted(g) for g in groups)):
                if len(set(representatives)) != len(representatives):
                    continue
                labels = list(range(n))
                valid = True
                for row in representatives:
                    edge = edges[row]
                    if edge is None or labels[edge[0]] == labels[edge[1]]:
                        valid = False
                        break
                    a, b = [labels[v] for v in edge]
                    labels = [a if value == b else value for value in labels]
                if valid:
                    exists = True
                    break
            self.assertEqual(selected is not None, exists)
            if obstruction:
                self.assertLess(obstruction['rank'], len(obstruction['groups']))


if __name__ == '__main__':
    unittest.main()
