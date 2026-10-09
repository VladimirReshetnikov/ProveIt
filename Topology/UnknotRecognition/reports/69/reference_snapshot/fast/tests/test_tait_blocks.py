"""Signed block products versus tree enumeration, dense cofactors and closures."""
from collections import defaultdict
from itertools import combinations
import json
from pathlib import Path
import random
import sys
import unittest
from unittest.mock import patch

from fastunknot import Diagram
from fastunknot.diagram import DisjointSet
from fastunknot.euler_scan import EulerBudget
from fastunknot.geometry import ScanLimit
from fastunknot.shadow_scan import ClosureShadow, _bareiss, shadow_compressed_khovanov_decide
from fastunknot.tait_blocks import spanning_tree_product

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'reports/26'))
from detshadow.linalg import signed_laplacian, bareiss
from detshadow.diagram import Diagram as Reference


def product(n, edges):
    stats = defaultdict(int)
    value = spanning_tree_product(n, edges, lambda amount=1: None, _bareiss, stats)
    return value, stats


def enumerate_trees(n, edges):
    total = 0
    for tree in combinations(edges, n - 1):
        sets, value = DisjointSet(n), 1
        for u, v, weight in tree:
            if sets.find(u) == sets.find(v):
                break
            sets.union(u, v)
            value *= weight
        else:
            total += value
    return total


class TaitBlockTests(unittest.TestCase):
    def test_random_multigraphs_against_tree_enumeration(self):
        rng = random.Random(2610)
        for n in range(1, 8):
            for _ in range(35):
                edges = [(rng.randrange(n), rng.randrange(n), rng.randrange(-2, 3))
                         for _ in range(rng.randrange(12))]
                self.assertEqual(product(n, edges)[0], enumerate_trees(n, edges), (n, edges))

    def test_random_larger_graphs_against_independent_dense_cofactors(self):
        rng = random.Random(2611)
        for n in range(2, 26):
            for _ in range(8):
                edges = [(rng.randrange(n), rng.randrange(n), rng.randrange(-3, 4))
                         for _ in range(3 * n)]
                lap = signed_laplacian(n, edges)
                expected = bareiss([row[1:] for row in lap[1:]])
                self.assertEqual(product(n, edges)[0], expected, (n, edges))

    def test_signed_cancellation_zero_blocks_and_long_chain(self):
        # A connected original multigraph may disconnect after parallel sums.
        value, stats = product(3, [(0, 1, 2), (1, 2, 1), (2, 1, -1)])
        self.assertEqual(value, 0)
        self.assertEqual(stats['tait_disconnected'], 1)
        # The nonzero graph is connected but the signed tree sum cancels.
        value, stats = product(4, [(0, 1, 2), (1, 2, 2), (2, 0, -1), (2, 3, 7)])
        self.assertEqual(value, 0)
        self.assertEqual(stats['tait_zero_factors'], 1)
        # No recursive DFS and no quadratic cofactor allocation on a long tree.
        value, stats = product(5000, [(i, i+1, -1) for i in range(4999)])
        self.assertEqual(value, -1)
        self.assertEqual(stats['tait_bridge_factors'], 4999)
        self.assertEqual(stats['max_cofactor_size'], 0)
        self.assertEqual(product(1, [(0, 0, -17)])[0], 1)

    def test_large_classical_phases_and_small_block_sizes(self):
        root = Path(__file__).resolve().parents[1] / 'examples'
        for name in ('conway_sum_2', 'conway_sum_8', 'stress_braid5_36', 'unknot_braid40'):
            d = Diagram.from_json(json.loads((root / (name+'.json')).read_text()))
            for diagram in (d, d.mirror()):
                ref = Reference(diagram.pd)
                engine = ClosureShadow(diagram.pd, list(range(diagram.crossings)), max_work=None)
                residues = engine.evaluate(0, ())
                self.assertEqual(sum(residues), ref.euler_one())
                self.assertEqual((residues[0]-residues[2], residues[1]-residues[3]), ref.euler_i())
                if name == 'conway_sum_8':
                    self.assertEqual(engine.stats['tait_blocks'], 8)
                    self.assertLessEqual(engine.stats['max_cofactor_size'], 6)
                    self.assertEqual(engine.stats['max_unsplit_cofactor_size'], 41)

    def test_interrupted_block_product_and_exact_fallback(self):
        path = Path(__file__).resolve().parents[1] / 'examples/conway_sum_8.json'
        d = Diagram.from_json(json.loads(path.read_text()))
        engine = ClosureShadow(d.pd, list(range(d.crossings)), max_work=None)
        completed = []
        def interrupt(matrix, tick):
            value = _bareiss(matrix, tick)
            completed.append(value)
            if len(completed) == 1:
                engine.max_work = engine.stats['work_units']
            return value
        with patch('fastunknot.shadow_scan._bareiss', side_effect=interrupt):
            with self.assertRaises(EulerBudget):
                engine.evaluate(0, ())
        self.assertEqual(len(completed), 1)
        self.assertNotIn((0, ()), engine.shadow_cache)
        engine.max_work = None
        self.assertEqual(sum(map(abs, engine.evaluate(0, ()))), 1)
        engine.deadline = 0
        with self.assertRaises(ScanLimit):
            engine.evaluate(0, ())
        # A real local work limit ends after only part of the optional graph
        # computation, but the complete scanner still decides the same knot.
        out = shadow_compressed_khovanov_decide(d.pd, shadow_max_work=2000)
        self.assertEqual(out['status'], 'KNOTTED')
        self.assertTrue(out['shadow_exhausted'])
        self.assertEqual((out['method'], out['stage']), ('component-euler', 11))
        self.assertFalse(out['euler_exhausted'])


if __name__ == '__main__':
    unittest.main()
