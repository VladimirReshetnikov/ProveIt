"""Sparse scalar components preserve the frozen contraction's exact basis."""
from collections import defaultdict
import copy
import random
import unittest

from fastunknot import Diagram
from fastunknot.binary_contraction import binary_contraction
from fastunknot.diagram import DiagramError
from fastunknot.geometry import ScanLimit
from fastunknot.graded import GradedScan
from fastunknot.ordering import best_scan_order
from fastunknot.scalar_components import component_contraction


def as_masks(result):
    return dict(i=[sum(1 << a for a in col) for col in result['i']],
                p=[sum(1 << a for a in col) for col in result['p']],
                h=[sum(1 << a for a in col) for col in result['h']],
                mid=result['mid'], deg=result['deg'], q=result['q'])


def synthetic(degree, quantum, out):
    scan = GradedScan(shape_cache=False)
    ma = scan.algebra.intern(((0, 1),))
    scan.points = frozenset((0, 1))
    scan.mid = [ma] * len(degree)
    scan.deg, scan.qshift = list(degree), list(quantum)
    scan.out = copy.deepcopy(out)
    scan.inc = [set() for _ in degree]
    for a, row in enumerate(scan.out):
        for b in row:
            scan.inc[b].add(a)
    scan.live = len(degree)
    return scan


class ScalarComponentsTests(unittest.TestCase):
    def compare(self, scan):
        expected = binary_contraction(scan)
        actual = component_contraction(scan)
        self.assertEqual(as_masks(actual), expected)
        for field in ('i', 'p', 'h'):
            for column in actual[field]:
                self.assertIsInstance(column, tuple)
                self.assertEqual(tuple(sorted(set(column))), column)
        return actual

    def test_interleaved_components_and_dead_slots(self):
        scan = synthetic([1, 0, 0, 1, 4, 0, 1], [0, 0, 0, 0, 8, 2, 2],
                         [{}, {0: 1}, {}, {}, {}, {6: 1}, {}])
        result = self.compare(scan)
        self.assertEqual(result['stats']['pair_components'], 2)
        self.assertEqual(result['stats']['singleton_components'], 3)
        scan.eliminate(update_budget=0)
        self.compare(scan)

    def test_many_pairs_use_no_dense_local_binary_problem(self):
        pairs = 2000
        degree = [0, 1] * pairs + [0, 1]
        out = [{} for _ in degree]
        for a in range(0, 2 * pairs, 2):
            out[a][a + 1] = 1
        scan = synthetic(degree, [0] * len(degree), out)
        result = component_contraction(scan)
        self.assertEqual(result['stats']['pair_components'], pairs)
        self.assertEqual(result['stats']['singleton_components'], 2)
        self.assertEqual(result['stats']['binary_components'], 0)
        self.assertEqual(result['stats']['local_cubic_bound'], 0)
        self.assertEqual(result['stats']['h_entries'], pairs)
        self.assertEqual(result['stats']['i_entries'], 2)
        self.assertEqual(result['stats']['p_entries'], 2)

    def test_random_scalar_complexes_and_interleaved_bases(self):
        rng = random.Random(20261008411)
        for _ in range(180):
            labels, arrows = [], []
            for _ in range(rng.randrange(1, 12)):
                degree, quantum = rng.randrange(-2, 4), rng.randrange(3)
                a = len(labels)
                labels.extend([(degree, quantum), (degree + 1, quantum)])
                arrows.append((a, a + 1))
            for _ in range(rng.randrange(1, 10)):
                labels.append((rng.randrange(-2, 5), rng.randrange(3)))
            order = list(range(len(labels)))
            rng.shuffle(order)
            inverse = {a: j for j, a in enumerate(order)}
            labels = [labels[a] for a in order]
            out = [{} for _ in labels]
            for a, b in arrows:
                out[inverse[a]][inverse[b]] = 1
            groups = defaultdict(list)
            for a, label in enumerate(labels):
                groups[label].append(a)
            choices = [group for group in groups.values() if len(group) > 1]
            for _ in range(100):
                if not choices:
                    break
                a, b = rng.sample(rng.choice(choices), 2)
                # The same elementary involution changes the source basis
                # of d^h and target basis of d^(h-1), preserving d^2=0.
                for target in list(out[b]):
                    if target in out[a]:
                        del out[a][target]
                    else:
                        out[a][target] = 1
                for source, row in enumerate(out):
                    if a in row:
                        if b in row:
                            del row[b]
                        else:
                            row[b] = 1
            scan = synthetic([a for a, _ in labels], [b for _, b in labels], out)
            scan.check_d_squared()
            scan.check_grading()
            self.compare(scan)

    def test_actual_prefixes_match_all_three_scalar_maps(self):
        rng = random.Random(20261008412)
        accepted = stages = 0
        while accepted < 64:
            strands = rng.randrange(2, 6)
            word = [rng.choice((-1, 1)) * rng.randrange(1, strands)
                    for _ in range(rng.randrange(1, 13))]
            try:
                diagram = Diagram.from_braid(strands, word)
            except DiagramError:
                continue
            order = best_scan_order(diagram.pd)
            if accepted % 2:
                rng.shuffle(order)
            scan = GradedScan(shape_cache=False)
            for crossing in order:
                scan.add_crossing(diagram.pd[crossing], reduce_now=False)
                if accepted % 3 == 0:
                    scan.eliminate(update_budget=rng.randrange(0, 4))
                self.compare(scan)
                scan.eliminate()
                stages += 1
            accepted += 1
        self.assertGreater(stages, 300)

    def test_invalid_scalar_chain_and_resource_hook(self):
        scan = synthetic([0, 1, 2], [0, 0, 0], [{1: 1}, {2: 1}, {}])
        with self.assertRaises(ArithmeticError):
            component_contraction(scan)
        scan = GradedScan(deadline=0)
        with self.assertRaises(ScanLimit):
            component_contraction(scan)


if __name__ == '__main__':
    unittest.main()
