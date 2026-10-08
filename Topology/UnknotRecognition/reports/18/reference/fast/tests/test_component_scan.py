"""Regression tests; run with the baseline fast/ directory on PYTHONPATH."""
import json
import os
from pathlib import Path
import random
import unittest

from fastunknot import Diagram
from fastunknot.diagram import DiagramError
from fastunknot.geometry import ScanLimit
from fastunknot.scan import khovanov_rank
from fastunknot.component_scan import (ComponentScan, component_key, compressed_khovanov_decide,
                            compressed_khovanov_rank)


class ComponentTests(unittest.TestCase):
    def assert_same(self, diagram, order=None, reference=False):
        old = khovanov_rank(diagram.pd, order=order, check_d_squared=True,
                            **({"pivot": "lifo", "algebra": "sets"} if reference else {}))
        new = compressed_khovanov_rank(diagram.pd, order=order, check_d_squared=True)
        self.assertEqual(old["rank"], new["rank"])
        self.assertEqual(old["reduced_rank"], new["reduced_rank"])
        self.assertEqual(old["by_degree"], new["by_degree"])
        decision = compressed_khovanov_decide(diagram.pd, order=order, check_d_squared=True)
        self.assertEqual(decision["rank_capped"], min(3, old["rank"]))
        self.assertEqual(decision["status"], "UNKNOT" if old["rank"] == 2 else "KNOTTED")

    def test_crossing_free_circle(self):
        self.assert_same(Diagram.from_pd([]))

    def test_torus_knots_and_mirrors(self):
        for strands, repeats in [(2, 3), (2, 9), (3, 4), (3, 8), (4, 3)]:
            for sign in [1, -1]:
                word = [sign * i for i in range(1, strands)] * repeats
                self.assert_same(Diagram.from_braid(strands, word))

    def test_random_closures_and_scan_orders(self):
        rng = random.Random(260107)
        accepted = 0
        while accepted < 200:
            strands = rng.randrange(2, 6)
            length = rng.randrange(2, 14)
            word = [rng.choice([-1, 1]) * rng.randrange(1, strands) for _ in range(length)]
            try:
                diagram = Diagram.from_braid(strands, word)
            except DiagramError:
                continue
            order = list(range(length)) if accepted % 2 else None
            if order is not None:
                rng.shuffle(order)
            self.assert_same(diagram, order=order, reference=accepted < 20)
            accepted += 1

    def test_multiplicities_are_integers(self):
        scan = ComponentScan(shape_cache=False)
        scan.mid = [0, 0, 0, 0]
        scan.deg = [0, 1, 0, 1]
        scan.out = [{}, {}, {}, {}]
        scan.inc = [set(), set(), set(), set()]
        scan.live = 4
        scan._compress([0, 0, 0, 0])
        self.assertEqual(scan.live, 1)
        self.assertEqual(scan.weights, [{0: 2, 1: 2}])
        self.assertEqual(scan.total_rank(), 4)
        self.assertEqual(scan.ranks_by_degree(), {0: 2, 1: 2})

    def test_existing_weights_are_shifted_and_added(self):
        scan = ComponentScan(shape_cache=False)
        scan.mid = [0, 0]
        scan.deg = [2, 3]
        scan.out = [{}, {}]
        scan.inc = [set(), set()]
        scan.live = 2
        scan.weights = [{0: 5, 1: 7}, {0: 11}]
        scan._compress([0, 1])
        self.assertEqual(scan.weights, [{2: 5, 3: 18}])
        self.assertEqual(scan.total_rank(), 23)

    def test_saturated_weights_do_not_cancel_or_keep_grading(self):
        scan = ComponentScan(shape_cache=False, rank_cap=3)
        scan.mid = [0, 0, 0, 0]
        scan.deg = [0, 1, 2, 3]
        scan.out = [{}, {}, {}, {}]
        scan.inc = [set(), set(), set(), set()]
        scan.live = 4
        scan._compress([0, 0, 0, 0])
        self.assertEqual(scan.weights, [{0: 3}])
        self.assertEqual(scan.total_rank(), 3)
        with self.assertRaises(ValueError):
            scan.ranks_by_degree()

    def test_key_records_every_morphism(self):
        scan = ComponentScan(shape_cache=False)
        scan.mid = [1, 1, 1, 1]
        scan.deg = [0, 1, 3, 4]
        scan.out = [{1: 2}, {}, {3: 4}, {}]
        scan.inc = [set(), {0}, set(), {2}]
        key1, shift1 = component_key(scan, [0, 1])
        key2, shift2 = component_key(scan, [2, 3])
        self.assertNotEqual(key1, key2)
        self.assertEqual((shift1, shift2), (0, 3))
        scan.out[2][3] = 2
        self.assertEqual(key1, component_key(scan, [2, 3])[0])

    def test_invalid_order_and_limits(self):
        pd = Diagram.from_braid(2, [1, 1, 1]).pd
        with self.assertRaises(ValueError):
            compressed_khovanov_rank(pd, order=[0, 1, 1])
        with self.assertRaises(ScanLimit):
            compressed_khovanov_rank(pd, max_objects=1)
        with self.assertRaises(ScanLimit):
            compressed_khovanov_rank(pd, seconds=0)

    def test_large_visible_sum_with_exact_rank_formula(self):
        # Geometric factoring is intentionally NOT used by this backend test.
        examples = Path(os.environ.get("FASTUNKNOT_EXAMPLES", str(Path(__file__).resolve().parents[1] / "examples")))
        source = examples / "conway_sum_8.json"
        if not source.exists():
            self.skipTest("set FASTUNKNOT_EXAMPLES to baseline/fast/examples for the large-sum check")
        diagram = Diagram.from_pd(json.loads(source.read_text())["pd"])
        result = compressed_khovanov_rank(diagram.pd, check_d_squared=True)
        self.assertEqual(result["rank"], 2 * 33 ** 8)
        self.assertLess(result["stats"]["max_representative_objects"], 1000)
        self.assertGreater(result["stats"]["max_expanded_after_elimination"], 10 ** 12)


if __name__ == "__main__":
    unittest.main(verbosity=2)

