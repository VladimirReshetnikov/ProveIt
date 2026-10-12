import copy
from itertools import product
import random
import unittest
from unittest.mock import patch

from activation_forests import (from_dense, solve, solve_output,
                               verify_output, parameters)
from activation_forests.oracle import tree_oracle


class OutputForestTests(unittest.TestCase):
    forest_oracle_cases = 0

    def assert_exact(self, problem, pivots=False):
        type(self).forest_oracle_cases += 1
        result = solve_output(problem)
        oracle = tree_oracle(problem, positive_pivots=pivots)
        self.assertEqual(result['status'], oracle['status'], (problem, result, oracle))
        self.assertTrue(verify_output(problem, result), (problem, result))
        return result

    def test_empty_disconnected_and_huge(self):
        self.assert_exact(from_dense(1, [], []))
        self.assert_exact(from_dense(2, [None], [[]]))
        problem = from_dense(1 << 16384, [[0, 1]], [[]])
        result = solve_output(problem)
        self.assertEqual(result['status'], 'NO_FOREST')
        self.assertTrue(verify_output(problem, result))
        huge = from_dense(3, [[0, 1], [1, 2], [0, 0]], [[1 << 16384], [3], [1]])
        self.assert_exact(huge, True)

    def test_null_block_is_not_a_negative_activation_requirement(self):
        # U already contains b,c, hence X is empty and the special block is
        # the sole block.  The chosen output a is activated after the seed rows.
        problem = from_dense(3, [[0, 1], [1, 2], [2, 0]], [[1], [1], [1]])
        result = self.assert_exact(problem, True)
        self.assertEqual(result['selected_assignment']['partition'], [0])
        self.assertEqual(result['selected_assignment']['prerequisites'], [])

    def test_shared_seed_block_and_replay(self):
        problem = from_dense(2, [[0, 1], [0, 1], [0, 1], [0, 0]],
                             [[1, 1, 2, 0], [1, 0, 0, 1],
                              [0, 1, 0, 1], [0, 0, 1, 1]])
        result = self.assert_exact(problem, True)
        # The chosen seed also activates an undemanded prerequisite.  The
        # distinguished block therefore must not be interpreted as inactive.
        self.assertEqual(result['selected_assignment']['partition'], [0, 1, 0])
        self.assertEqual(result['certificate']['tree'], [0])
        with patch('activation_forests.output_solver.solve_output', side_effect=AssertionError), \
             patch('activation_forests.output_solver._output_closure', side_effect=AssertionError), \
             patch('activation_forests.output_solver._rainbow', side_effect=AssertionError):
            self.assertTrue(verify_output(problem, result))

    def test_factorial_removed_and_complete_negative_replay(self):
        problem = from_dense(2, [[0, 1]] * 3, [[1, 1, 1]] * 3)
        result = self.assert_exact(problem, True)
        old = solve(problem)
        self.assertEqual(result['stats']['output_assignments'], 27)
        self.assertEqual(old['stats']['scenarios'], 162)
        self.assertLess(result['stats']['structural_work'], old['stats']['structural_work'])
        kinds = {p['kind'] for assignment in result['certificate']['assignments']
                 if assignment['kind'] == 'partitions' for p in assignment['failures']}
        self.assertEqual(kinds, {'rank', 'nonclosure'})
        with patch('activation_forests.output_solver._output_closure', side_effect=AssertionError), \
             patch('activation_forests.solver._compile', side_effect=AssertionError), \
             patch('activation_forests.solver._rainbow', side_effect=AssertionError):
            self.assertTrue(verify_output(problem, result))
        missing = copy.deepcopy(result)
        missing['certificate']['assignments'].pop()
        self.assertFalse(verify_output(problem, missing))
        missing = copy.deepcopy(result)
        assignment = next(a for a in missing['certificate']['assignments']
                          if a['kind'] == 'partitions')
        assignment['failures'].pop()
        self.assertFalse(verify_output(problem, missing))
        forged = copy.deepcopy(result)
        proof = next(p for a in forged['certificate']['assignments']
                     if a['kind'] == 'partitions' for p in a['failures']
                     if p['kind'] == 'nonclosure')
        proof['unreached'] = 100
        self.assertFalse(verify_output(problem, forged))

    def test_parity_stirling_layer_and_ablation(self):
        problem = from_dense(2, [[0, 1]] * 4 + [[0, 0]],
                             [[1, 0], [1, 0], [0, 1], [0, 1], [1, 1]])
        result = self.assert_exact(problem, True)
        self.assertTrue(result['certificate']['rank_layer'])
        ordinary = solve_output(problem, use_rank_layer=False)
        self.assertEqual(result['status'], ordinary['status'])
        self.assertTrue(verify_output(problem, ordinary))
        incompatible = from_dense(2, [[0, 1]] * 2, [[3], [2]])
        proof = self.assert_exact(incompatible, True)
        self.assertFalse(parameters(incompatible)['raw_parity'])
        proof['certificate']['rank_layer'] = True
        self.assertFalse(verify_output(incompatible, proof))

    def test_limits(self):
        problem = from_dense(3, [[0, 1], [1, 2], [2, 0]], [[1], [1], [1]])
        for limits in ({'max_work': 0}, {'max_assignments': 0}, {'max_partitions': 0}):
            result = solve_output(problem, **limits)
            self.assertEqual(result['status'], 'INCONCLUSIVE')
            self.assertNotIn('certificate', result)
            self.assertFalse(verify_output(problem, result))

    def test_exhaustive_three_rows_two_columns(self):
        geometries = [(1, [[0, 0]] * 3), (2, [[0, 1]] * 3),
                      (2, [[0, 1], [0, 0], None]),
                      (3, [[0, 1], [1, 2], [2, 0]])]
        for values in product(range(3), repeat=6):
            rows = [list(values[i:i + 2]) for i in (0, 2, 4)]
            for vertices, edges in geometries:
                self.assert_exact(from_dense(vertices, edges, rows), True)

    def test_random_unit_triples(self):
        rng = random.Random(0xFB675)
        for _ in range(2500):
            n, m, width = rng.randrange(1, 5), rng.randrange(1, 9), rng.randrange(5)
            edges = [None if rng.randrange(7) == 0 else [rng.randrange(n), rng.randrange(n)]
                     for _ in range(m)]
            matrix = [[0] * width for _ in range(m)]
            for c in range(width):
                owners = rng.sample(range(m), rng.randrange(min(3, m) + 1))
                for row in owners:
                    matrix[row][c] = 1 if len(owners) == 3 else rng.choice((1, 1, 2))
            self.assert_exact(from_dense(n, edges, matrix))

    def test_random_generic_nonlinear_columns(self):
        rng = random.Random(0xE632)
        for _ in range(600):
            n, m = rng.randrange(1, 5), rng.randrange(3, 8)
            edges = [None if rng.randrange(7) == 0 else [rng.randrange(n), rng.randrange(n)]
                     for _ in range(m)]
            matrix = [[rng.choice((0, 1, 1, 2)), 0, 0] for _ in range(m)]
            for c in (1, 2):
                for row in rng.sample(range(m), rng.randrange(3)):
                    matrix[row][c] = rng.choice((1, 2))
            self.assert_exact(from_dense(n, edges, matrix), True)


if __name__ == '__main__':
    unittest.main()
