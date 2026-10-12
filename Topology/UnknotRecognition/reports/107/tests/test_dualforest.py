import copy
import itertools
import random
import unittest
import subprocess
import sys
from pathlib import Path
from unittest.mock import patch

from dualforest import (from_dense, from_data, make_instance, solve, solve_pair,
                        verify_positive, verify_pair_optimality, verify_negative)
from dualforest.dependencies import build, peel, reach, partitions, scc
from dualforest.intersection import transversal
from dualforest.model import rank
from dualforest.solver import positive_certificate
from experiments.oracles import (tree_oracle, defect_oracle, transversal_oracle,
                                 literal_peel, full_positive_oracle)


def loop_fixture():
    return from_dense(2, [(0, 1)] * 4 + [(1, 1)],
                      [[0, 0, 1, 0, 0], [1, 1, 0, 0, 0], [0, 1, 0, 1, 1],
                       [1, 0, 1, 1, 1], [0, 1, 1, 1, 0]])


class ValidationTests(unittest.TestCase):
    def test_round_trip(self):
        obj = loop_fixture()
        self.assertEqual(obj, from_data(obj.data()))

    def test_ragged(self):
        with self.assertRaises(ValueError):
            from_dense(1, [(0, 0)] * 2, [[1], [1, 2]])

    def test_huge_vertex_count_rejected_before_allocation(self):
        with self.assertRaises(ValueError):
            from_dense(1 << 1000, [], [])

    def test_disconnected(self):
        with self.assertRaises(ValueError):
            from_dense(2, [(0, 0)], [[1]])

    def test_negative(self):
        with self.assertRaises(ValueError):
            from_dense(1, [(0, 0)], [[-1]])

    def test_boolean_is_not_incidence(self):
        with self.assertRaises(ValueError):
            from_dense(1, [(0, 0)], [[True]])

    def test_wrong_row_count(self):
        with self.assertRaises(ValueError):
            from_dense(1, [], [[1]])

    def test_large_binary_entry(self):
        inst = from_dense(2, [(0, 1), (1, 1)], [[1 << 16384], [1]])
        self.assertEqual(inst.rows[0], ((0, 2),))
        result = solve_pair(inst)
        self.assertEqual(result['status'], 'yes')
        self.assertTrue(verify_positive(inst, result['certificate']))

    def test_empty(self):
        inst = from_dense(1, [], [])
        result = solve_pair(inst)
        self.assertTrue(verify_positive(inst, result['certificate']))
        self.assertTrue(verify_pair_optimality(inst, result['optimality']))

    def test_duplicate_serialized_column(self):
        data = from_dense(1, [(0, 0)], [[1]]).data()
        data['rows'][0].append([0, 2])
        with self.assertRaises(ValueError):
            from_data(data)


class DependencyTests(unittest.TestCase):
    def test_asymmetric_unit_arcs(self):
        inst = from_dense(2, [(0, 1), (0, 1)], [[1], [2]])
        info = build(inst)
        self.assertEqual(info['adj'], [set(), {0}])
        self.assertEqual(info['required'], [{1}])
        self.assertIsNone(peel(inst, {0}))
        self.assertIsNotNone(peel(inst, {1}))

    def test_bidirectional_unit_arcs(self):
        inst = from_dense(2, [(0, 1), (0, 1)], [[1], [1]])
        self.assertEqual(build(inst)['required'], [{0, 1}])

    def test_anchor_downstream_does_not_seed_source(self):
        inst = from_dense(2, [(0, 1), (0, 1)], [[2, 0], [1, 1]])
        self.assertEqual(build(inst)['required'], [{0}])

    def test_unusable_high_column_ignored(self):
        inst = from_dense(2, [(0, 1)] * 3, [[2], [2], [2]])
        self.assertEqual(build(inst)['boundary'], set())
        self.assertEqual(solve_pair(inst)['optimality']['defect'], 2)

    def test_exceptional_boundary(self):
        self.assertEqual(build(loop_fixture())['boundary'], set(range(5)))

    def test_scc_independent_small(self):
        rng = random.Random(182)
        for n in range(1, 12):
            for _ in range(20):
                adj = [{j for j in range(n) if rng.randrange(5) == 0} for i in range(n)]
                got = {frozenset(s) for s in scc(adj)}
                rr = [reach(adj, [i]) for i in range(n)]
                expected = {frozenset(j for j in range(n) if j in rr[i] and i in rr[j])
                            for i in range(n)}
                self.assertEqual(got, expected)

    def test_deep_partition_prefix_without_recursion(self):
        from dualforest.verify import _partitions
        left, right = partitions(1200), _partitions(1200)
        for _ in range(3):
            self.assertEqual(next(left), next(right))

    def test_partition_counts(self):
        self.assertEqual([len(list(partitions(n))) for n in range(7)],
                         [1, 1, 2, 5, 15, 52, 203])


class IntersectionTests(unittest.TestCase):
    def test_parallel_obstruction(self):
        inst = from_dense(2, [(0, 1)] * 2, [[], []])
        got = transversal(inst, [{0}, {1}])
        self.assertEqual(got['size'], 1)
        self.assertEqual(got['defect'], 1)

    def test_overlapping_clone_colors(self):
        inst = from_dense(3, [(0, 1), (1, 2), (0, 2)], [[], [], []])
        got = transversal(inst, [{0, 1}, {0}])
        self.assertEqual(got['size'], 2)
        self.assertEqual({r for r, c in got['representatives']}, {0, 1})

    def test_exchange_augmentation(self):
        inst = from_dense(3, [(0, 1), (1, 2)], [[], []])
        got = transversal(inst, [{0, 1}, {0}])
        self.assertEqual(got['size'], 2)
        self.assertEqual(got['augments'], 2)

    def test_loop_only_color(self):
        inst = from_dense(2, [(0, 1), (1, 1)], [[], []])
        got = transversal(inst, [{1}])
        self.assertEqual(got['size'], 0)
        self.assertEqual(got['obstruction_colors'], [0])

    def test_empty_group(self):
        inst = from_dense(1, [], [])
        self.assertEqual(transversal(inst, [set()])['defect'], 1)

    def test_optimized_python_preserves_forest_updates(self):
        code = """
from dualforest import from_dense
from dualforest.intersection import transversal
from dualforest.model import rank
x=from_dense(3,[(0,1),(1,2)],[[],[]])
a=transversal(x,[{0,1},{0}])
if a['size'] != 2 or rank(x,[r for r,c in a['representatives']]) != 2:
    raise RuntimeError('optimized execution lost forest independence')
"""
        result = subprocess.run([sys.executable, '-O', '-c', code],
                                cwd=Path(__file__).resolve().parents[1],
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_random_against_assignments(self):
        rng = random.Random(712)
        for _ in range(250):
            v = rng.randint(1, 5)
            edges = [(i - 1, i) for i in range(1, v)]
            edges += [(rng.randrange(v), rng.randrange(v)) for _ in range(rng.randrange(5))]
            inst = from_dense(v, edges, [[] for _ in edges])
            groups = [{r for r in range(inst.m) if rng.randrange(2)}
                      for _ in range(rng.randrange(6))]
            ans = transversal(inst, groups)
            self.assertEqual(ans['size'], transversal_oracle(inst, groups))
            js = ans['obstruction_colors']
            union = set().union(set(), *(groups[j] for j in js))
            self.assertEqual(len(js) - rank(inst, union), ans['defect'])


class SelectorTests(unittest.TestCase):
    def test_repository_loop_fixture(self):
        inst = loop_fixture()
        self.assertIsNone(peel(inst, [0]))
        ans = solve(inst, try_incumbent=False)
        self.assertEqual(ans['status'], 'yes')
        self.assertNotEqual(ans['certificate']['tree'], [0])
        self.assertTrue(verify_positive(inst, ans['certificate']))

    def test_high_column_can_repair_pair_failure(self):
        inst = from_dense(3, [(0, 1), (1, 2), (0, 2)], [[1], [1], [1]])
        result = solve(inst, try_incumbent=False)
        self.assertEqual(result['status'], 'yes')
        self.assertTrue(verify_positive(inst, result['certificate']))

    def test_high_negative_replay(self):
        inst = from_dense(2, [(0, 1), (0, 1), (1, 1)], [[1], [1], [1]])
        ans = solve(inst, try_incumbent=False)
        self.assertEqual(ans['status'], 'no')
        self.assertTrue(verify_negative(inst, ans['negative_certificate']))

    def test_branch_cap_unknown(self):
        ans = solve(loop_fixture(), max_branches=1, try_incumbent=False)
        self.assertEqual(ans['status'], 'unknown')
        self.assertIsNone(ans['certificate'])

    def test_zero_cap_low_unknown(self):
        inst = from_dense(2, [(0, 1)] * 2, [[0], [0]])
        self.assertEqual(solve(inst, max_branches=0, try_incumbent=False)['status'], 'unknown')

    def test_bad_cap(self):
        with self.assertRaises(ValueError):
            solve(loop_fixture(), max_branches=True)

    def test_pair_defect_exact(self):
        rng = random.Random(404)
        for _ in range(80):
            v = rng.randint(1, 4)
            edges = [(i - 1, i) for i in range(1, v)]
            edges += [(rng.randrange(v), rng.randrange(v)) for _ in range(3)]
            m = len(edges)
            mat = [[0] * 4 for _ in edges]
            for c in range(4):
                for r in rng.sample(range(m), min(m, rng.randrange(3))):
                    mat[r][c] = rng.randint(1, 2)
            inst = from_dense(v, edges, mat)
            ans = solve_pair(inst)
            self.assertEqual(ans['optimality']['defect'], defect_oracle(inst))
            self.assertTrue(verify_pair_optimality(inst, ans['optimality']))

    def test_arbitrary_positive_fill_oracle(self):
        rng = random.Random(994)
        for _ in range(150):
            matrix = tuple(tuple(rng.randrange(3) for _ in range(3)) for _ in range(3))
            inst = from_dense(1, [(0, 0)] * 3, matrix)
            self.assertEqual(peel(inst, []) is not None, full_positive_oracle(matrix))

    def test_nonzero_root(self):
        inst = from_dense(3, [(0, 1), (1, 2)], [[], []], root=2)
        ans = solve(inst)
        self.assertTrue(verify_positive(inst, ans['certificate']))


class VerifierTests(unittest.TestCase):
    def setUp(self):
        self.inst = loop_fixture()
        self.cert = positive_certificate(self.inst, [1])

    def test_replay_without_producer(self):
        with patch('dualforest.solver.solve', side_effect=RuntimeError), \
             patch('dualforest.intersection.transversal', side_effect=RuntimeError), \
             patch('dualforest.dependencies.build', side_effect=RuntimeError):
            self.assertTrue(verify_positive(self.inst, self.cert))
            inst = from_dense(2, [(0, 1)] * 2, [[0], [0]])
            cert = dict(schema='pair-defect-v1', tree=[0], extra=[1], pivots=[],
                        obstruction_colors=[0, 1], defect=1)
            self.assertTrue(verify_pair_optimality(inst, cert))

    def test_pivot_entry_mutation(self):
        rows = [dict(row) for row in self.inst.rows]
        r, c = self.cert['pivots'][0]
        rows[r][c] = 2
        changed = make_instance(self.inst.vertices, self.inst.edges, rows, columns=self.inst.columns)
        self.assertFalse(verify_positive(changed, self.cert))

    def test_reordered_invalid_pivots(self):
        cert = copy.deepcopy(self.cert)
        cert['pivots'].reverse()
        self.assertFalse(verify_positive(self.inst, cert))

    def test_missing_pivot(self):
        cert = copy.deepcopy(self.cert)
        cert['pivots'].pop()
        self.assertFalse(verify_positive(self.inst, cert))

    def test_duplicate_pivot(self):
        cert = copy.deepcopy(self.cert)
        cert['pivots'].append(cert['pivots'][0])
        self.assertFalse(verify_positive(self.inst, cert))

    def test_loop_cannot_be_tree(self):
        cert = copy.deepcopy(self.cert)
        cert['tree'] = [4]
        self.assertFalse(verify_positive(self.inst, cert))

    def test_bad_child(self):
        cert = copy.deepcopy(self.cert)
        cert['dual_cancellations'][0][1] = 0
        self.assertFalse(verify_positive(self.inst, cert))

    def test_missing_negative_branch(self):
        inst = from_dense(2, [(0, 1)] * 3, [[1], [1], [1]])
        ans = solve(inst, try_incumbent=False)
        cert = ans['negative_certificate']
        self.assertTrue(verify_negative(inst, cert))
        cert['rank_obstructions'].pop()
        self.assertFalse(verify_negative(inst, cert))

    def test_negative_rank_tampering(self):
        inst = from_dense(2, [(0, 1)] * 3, [[1], [1], [1]])
        cert = solve(inst, try_incumbent=False)['negative_certificate']
        cert['rank_obstructions'][0] = []
        self.assertFalse(verify_negative(inst, cert))

    def test_nonunit_oracle_not_geometry(self):
        inst = from_dense(1, [(0, 0)] * 2, [[1, 1], [1, 2]])
        self.assertEqual(solve_pair(inst)['status'], 'no')


if __name__ == '__main__':
    unittest.main()
