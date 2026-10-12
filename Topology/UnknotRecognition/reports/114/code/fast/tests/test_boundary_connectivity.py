"""Independent orientation, smoothing, recurrence and resource checks."""
from pathlib import Path
import random
import sys
import unittest
from unittest.mock import patch

from fastunknot import Diagram
from fastunknot.boundary_connectivity import BoundaryConnectivity
from fastunknot.euler_scan import AdaptiveClosureEuler, ClosureEuler, EulerBudget, SuffixEuler
from fastunknot.geometry import ScanLimit
from fastunknot.scan_fast import FastScan

sys.path.insert(0, str(Path(__file__).resolve().parents[2]/'reports/26'))
from detshadow.diagram import complete_matching


WORD = [-2, 3, 2, 2, 4, 2, -3, -2, -1, 1, -2, -1, -2, -2]
ORDER = [5, 1, 10, 2, 9, 11, 13, 6, 7, 0, 12, 4, 8, 3]


def stream(extra=16):
    diagram = Diagram.from_braid(5, WORD+[1, -1]*extra)
    order = ORDER+list(range(len(WORD), diagram.crossings))
    scan = FastScan(shape_cache=False)
    for i in order[:9]:
        scan.add_crossing(diagram.pd[i])
    return diagram, order, [scan.algebra.pairs[m] for m in sorted(set(scan.mid)-{None})]


class BoundaryTests(unittest.TestCase):
    def test_counts_sign_and_recurrence_on_actual_completions(self):
        rng = random.Random(2608)
        accepted = queries = 0
        while accepted < 45:
            strands = rng.randrange(2, 5)
            word = [rng.choice((-1, 1))*rng.randrange(1, strands)
                    for _ in range(rng.randrange(1, 9))]
            try:
                diagram = Diagram.from_braid(strands, word)
            except ValueError:
                continue
            accepted += 1
            for d in (diagram, diagram.mirror()):
                order = list(range(d.crossings))
                rng.shuffle(order)
                adaptive = AdaptiveClosureEuler(d.pd, order, compression_after=0, max_states=None)
                recurrence = SuffixEuler(d.pd, order, max_states=None)
                scan = FastScan(shape_cache=False)
                for stage, i in enumerate(order):
                    for m in set(scan.mid)-{None}:
                        pairs = scan.algebra.pairs[m]
                        actual = adaptive.evaluate(stage, pairs)
                        self.assertEqual(actual, recurrence.evaluate(stage, pairs))
                        reference = complete_matching([d.pd[j] for j in order[stage:]], pairs)
                        c, c0 = adaptive.summary.counts(pairs)
                        oriented_c, h = reference.orientation_data()
                        self.assertEqual(c, oriented_c)
                        self.assertEqual(c0, len(reference.state_circles(0)))
                        self.assertEqual((len(order)-stage+c+c0) % 2, h % 2)
                        queries += 1
                    scan.add_crossing(d.pd[i])
        self.assertGreater(queries, 500)

    def test_adaptive_switch_cache_and_wide_frontier_guard(self):
        d, order, pairs = stream()
        engine = AdaptiveClosureEuler(d.pd, order, max_states=None)
        reference = ClosureEuler(d.pd, order, max_states=None)
        for i, p in enumerate(pairs):
            self.assertEqual(engine.evaluate(9, p), reference.evaluate(9, p))
            self.assertEqual(engine.stats['boundary_preparations'], int(i >= 4))
        self.assertEqual(engine.stats['boundary_evaluations'], len(pairs)-4)
        before = dict(engine.stats)
        self.assertEqual(engine.evaluate(9, pairs[0]), reference.evaluate(9, pairs[0]))
        self.assertEqual(engine.stats['states'], before['states'])
        self.assertEqual(engine.stats['boundary_query_darts'], before['boundary_query_darts'])
        self.assertEqual(engine.evaluate(len(order), ()), 1)
        self.assertIsNone(engine.summary)
        short, short_order, short_pairs = stream(0)
        wide = AdaptiveClosureEuler(short.pd, short_order, max_states=None)
        for p in short_pairs:
            wide.evaluate(9, p)
        self.assertEqual(wide.stats['boundary_preparations'], 0)

    def test_query_limit_precedes_preparation_and_deadline_precedes_cache(self):
        d, order, pairs = stream()
        zero = AdaptiveClosureEuler(d.pd, order, max_states=0, compression_after=0)
        with self.assertRaises(EulerBudget):
            zero.evaluate(9, pairs[0])
        self.assertEqual(zero.stats['prepared_stages'], 0)
        engine = AdaptiveClosureEuler(d.pd, order, max_states=1, compression_after=0)
        value = engine.evaluate(9, pairs[0])
        self.assertEqual(engine.evaluate(9, pairs[0]), value)
        with self.assertRaises(EulerBudget):
            engine.evaluate(9, pairs[1])
        engine.deadline = 0
        with self.assertRaises(ScanLimit):
            engine.evaluate(9, pairs[0])

    def test_interrupted_summary_is_not_published(self):
        d, order, pairs = stream()
        engine = AdaptiveClosureEuler(d.pd, order, compression_after=0, max_states=None)
        original = BoundaryConnectivity._paths

        def interrupted(*args):
            original(*args)
            raise ScanLimit('interrupted between summaries')

        with patch.object(BoundaryConnectivity, '_paths', side_effect=interrupted):
            with self.assertRaises(ScanLimit):
                engine.evaluate(9, pairs[0])
        self.assertIsNone(engine.summary)
        self.assertNotIn((9, tuple(pairs[0])), engine.cache)
        self.assertEqual(engine.stats['boundary_preparations'], 0)
        self.assertEqual(engine.evaluate(9, pairs[0]), ClosureEuler(d.pd, order).evaluate(9, pairs[0]))

    def test_empty_scalar_and_invalid_coverage(self):
        engine = AdaptiveClosureEuler([], [], compression_after=0)
        self.assertEqual(engine.evaluate(0, ()), 1)
        self.assertEqual(engine.summary.counts(()), (0, 0))
        d, order, pairs = stream()
        engine = AdaptiveClosureEuler(d.pd, order, compression_after=0, max_states=None)
        for bad in ((), pairs[0]+(pairs[0][0],), ((-1, -2),)+pairs[0][1:]):
            with self.assertRaises(ValueError):
                engine.evaluate(9, bad)
        for limit in (-1, True, 1.5):
            with self.assertRaises(ValueError):
                AdaptiveClosureEuler([], [], compression_after=limit)


if __name__ == '__main__':
    unittest.main()
