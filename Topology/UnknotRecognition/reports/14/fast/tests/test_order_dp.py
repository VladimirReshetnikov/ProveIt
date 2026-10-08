"""Independent exact checks of the subset-DP scan order optimizer."""
from itertools import permutations
from pathlib import Path
import json
import random
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from fastunknot import Diagram, khovanov_rank
from fastunknot.order_dp import frontier_sizes, improve_scan_order, optimize_window
from fastunknot.ordering import best_scan_order


def score(pd, order, objective):
    widths = frontier_sizes(pd, order)
    costs = widths if objective == "sum" else [1 << (w // 2) for w in widths]
    return max(widths, default=0), sum(costs)


def random_pairing_pd(rng, n):
    # A 4-regular multigraph need not be a spherical knot: this independently
    # tests the graph optimization theorem on its broader natural domain.
    labels = list(range(2 * n)) * 2
    rng.shuffle(labels)
    return [tuple(labels[4*i:4*i+4]) for i in range(n)]


class TestOrderDP(unittest.TestCase):
    def test_full_order_exhaustive(self):
        rng = random.Random(260710)
        for n in range(1, 7):
            for _ in range(8):
                pd = random_pairing_pd(rng, n)
                initial = list(range(n))
                rng.shuffle(initial)
                for objective in ("sum", "mass"):
                    found, record = optimize_window(pd, initial, 0, n, objective=objective)
                    expected = min(score(pd, p, objective) for p in permutations(range(n)))
                    self.assertEqual(score(pd, found, objective), expected)
                    self.assertEqual(sorted(found), list(range(n)))

    def test_window_exhaustive_with_outside_peak(self):
        rng = random.Random(744)
        for _ in range(70):
            pd = random_pairing_pd(rng, 10)
            initial = list(range(10))
            rng.shuffle(initial)
            start = rng.randrange(0, 5)
            stop = start + 6
            for objective in ("sum", "mass"):
                found, _ = optimize_window(pd, initial, start, stop, objective=objective)
                expected = min(
                    score(pd, initial[:start] + list(p) + initial[stop:], objective)
                    for p in permutations(initial[start:stop]))
                self.assertEqual(score(pd, found, objective), expected)
                self.assertEqual(found[:start], initial[:start])
                self.assertEqual(found[stop:], initial[stop:])

    def test_passes_monotone(self):
        rng = random.Random(8191)
        for _ in range(30):
            pd = random_pairing_pd(rng, 18)
            initial = list(range(18))
            rng.shuffle(initial)
            result = improve_scan_order(pd, order=initial, window=7, passes=3)
            self.assertLessEqual(result["score"], result["initial_score"])
            for window in result["windows"]:
                self.assertLessEqual(window["new_score"], window["old_score"])

    def test_real_knots_have_same_homology(self):
        for name in ("trefoil", "figure_eight", "conway", "hard_unknot_8"):
            d = Diagram.from_json(json.loads((ROOT / "examples" / (name + ".json")).read_text()))
            initial = best_scan_order(d.pd, tries=min(d.crossings, 12))
            result = improve_scan_order(d.pd, order=initial, window=8, passes=2)
            a = khovanov_rank(d.pd, order=initial)
            b = khovanov_rank(d.pd, order=result["order"], check_d_squared=True)
            self.assertEqual(a["by_degree"], b["by_degree"])

    def test_budget_and_errors(self):
        pd = [(0, 1, 0, 1)]
        self.assertEqual(improve_scan_order([], window=3)["order"], [])
        pd2 = [(0, 1, 2, 3), (0, 1, 2, 3)]
        result = improve_scan_order(pd2, order=[0, 1], seconds=0)
        self.assertFalse(result["complete"])
        self.assertEqual(result["order"], [0, 1])
        for kwargs in ({"window": 0}, {"passes": -1}, {"objective": "invalid"}):
            with self.assertRaises(ValueError):
                improve_scan_order(pd, **kwargs)
        with self.assertRaises(ValueError):
            optimize_window(pd, [0], 0, 2)


if __name__ == "__main__":
    unittest.main()
