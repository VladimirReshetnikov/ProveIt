"""Independent continuation checks and monotonicity tests for Euler inference."""
import json
import os
from pathlib import Path
import random
import unittest

from fastunknot import Diagram
from fastunknot.diagram import DiagramError
from fastunknot.ordering import best_scan_order
from fastunknot.scan import ScanComplex, khovanov_rank
from fastunknot.scan_fast import FastScan
from fastunknot.component_scan import ComponentScan
from fastunknot.euler_scan import (EulerBudget, SuffixEuler, component_euler_bound,
                        euler_compressed_khovanov_decide)


def random_diagrams(count, seed):
    rng = random.Random(seed)
    accepted = 0
    while accepted < count:
        strands = rng.randrange(2, 5)
        length = rng.randrange(2, 11)
        word = [rng.choice([-1, 1]) * rng.randrange(1, strands) for _ in range(length)]
        try:
            diagram = Diagram.from_braid(strands, word)
        except DiagramError:
            continue
        order = list(range(length))
        rng.shuffle(order)
        accepted += 1
        yield diagram, order


class EulerTests(unittest.TestCase):
    def test_suffix_matches_generic_algebra_continuation(self):
        checked = 0
        for diagram, order in random_diagrams(40, 1260107):
            stage = len(order) // 2
            scan = FastScan(shape_cache=False)
            for index in order[:stage]:
                scan.add_crossing(diagram.pd[index])
            engine = SuffixEuler(diagram.pd, order, max_states=10000)
            for matching in sorted({m for m in scan.mid if m is not None})[:3]:
                pairs = scan.algebra.pairs[matching]
                expected = ScanComplex(algebra="sets", pivot="lifo")
                expected.objects = {0: (frozenset(pairs), 0)}
                expected.next_id = 1
                expected.points = scan.points
                for index in order[stage:]:
                    expected.add_crossing(diagram.pd[index])
                    expected.check_d_squared()
                chi = sum((-1) ** h * rank for h, rank in expected.ranks_by_degree().items())
                self.assertEqual(engine.evaluate(stage, pairs), chi)
                checked += 1
        self.assertGreaterEqual(checked, 40)

    def test_bound_is_monotone_and_finishes_at_full_rank(self):
        for diagram, order in random_diagrams(50, 2260107):
            rank = khovanov_rank(diagram.pd, order=order)["rank"]
            scan = ComponentScan(shape_cache=False)
            engine = SuffixEuler(diagram.pd, order, max_states=10000)
            previous = 0
            for stage, index in enumerate(order, 1):
                scan.add_crossing(diagram.pd[index])
                bound, _ = component_euler_bound(scan, engine, stage)
                self.assertLessEqual(previous, bound)
                self.assertLessEqual(bound, rank)
                previous = bound
            self.assertEqual(previous, rank)
            verdict = euler_compressed_khovanov_decide(
                diagram.pd, order=order, check_d_squared=True, euler_max_states=10000)
            self.assertEqual(verdict["status"], "UNKNOT" if rank == 2 else "KNOTTED")

    def test_zero_budget_is_inconclusive(self):
        diagram = Diagram.from_braid(3, [1, 1, 1, 2, 2, 2])
        result = euler_compressed_khovanov_decide(diagram.pd, euler_max_states=0)
        self.assertEqual(result["status"], "KNOTTED")
        self.assertEqual(result["method"], "closed-rank")
        self.assertTrue(result["euler_exhausted"])
        self.assertEqual(result["rank_capped"], 3)

    def test_no_false_early_knot_on_unlinking_cancellations(self):
        diagram = Diagram.from_braid(3, [1, 2, -2, -1, 1, 2])
        self.assertEqual(khovanov_rank(diagram.pd)["rank"], 2)
        result = euler_compressed_khovanov_decide(diagram.pd, check_d_squared=True)
        self.assertEqual(result["status"], "UNKNOT")

    def test_large_sum_has_early_certificate(self):
        examples = Path(os.environ.get("FASTUNKNOT_EXAMPLES", str(Path(__file__).resolve().parents[1] / "examples")))
        source = examples / "conway_sum_8.json"
        if not source.exists():
            self.skipTest("set FASTUNKNOT_EXAMPLES for the large-sum check")
        diagram = Diagram.from_pd(json.loads(source.read_text())["pd"])
        result = euler_compressed_khovanov_decide(diagram.pd, check_d_squared=True)
        self.assertEqual(result["status"], "KNOTTED")
        self.assertEqual(result["method"], "component-euler")
        self.assertLess(result["stage"], len(diagram.pd))
        self.assertEqual(result["rank_lower_bound_capped"], 3)
        self.assertNotIn("rank", result)
        self.assertNotIn("rank_capped", result)

    def test_signed_euler_values_are_not_saturated(self):
        diagram = Diagram.from_braid(2, [1, 1, 1])
        order = list(range(3))
        engine = SuffixEuler(diagram.pd, order, max_states=100)
        self.assertEqual(engine.evaluate(0, ()), -2)
        self.assertIn(4, engine.cache.values())
        with self.assertRaises(EulerBudget):
            SuffixEuler(diagram.pd, order, max_states=0).evaluate(0, ())

    def test_mirror_pairs_follow_raw_scanner_grading(self):
        rng = random.Random(3260107)
        for strands, word in [(2, [1] * 5), (3, [1, 2] * 5),
                              (3, [1, -2] * 4), (4, [1, 2, 3] * 3)]:
            for sign in (-1, 1):
                diagram = Diagram.from_braid(strands, [sign * g for g in word])
                order = list(range(len(word)))
                rng.shuffle(order)
                result = khovanov_rank(diagram.pd, order=order)
                expected = sum((-1) ** h * rank for h, rank in result["by_degree"].items())
                engine = SuffixEuler(diagram.pd, order, max_states=20000)
                self.assertEqual(engine.evaluate(0, ()), expected)
                self.assertEqual(abs(expected), 2)
                verdict = euler_compressed_khovanov_decide(diagram.pd, order=order)
                self.assertEqual(verdict["status"], "KNOTTED")

    def test_iterative_stack_handles_long_orders(self):
        # A 1201-crossing two-strand torus knot gives a deep but narrow DAG.
        diagram = Diagram.from_braid(2, [1] * 1201)
        order = list(range(1201))
        engine = SuffixEuler(diagram.pd, order, max_states=5000)
        self.assertEqual(abs(engine.evaluate(0, ())), 2)


if __name__ == "__main__":
    unittest.main(verbosity=2)
