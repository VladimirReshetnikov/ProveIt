"""Semantic cross-checks of suffix-aware homological windows."""
from __future__ import annotations

import json
from pathlib import Path
import random
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from fastunknot.diagram import Diagram, DiagramError
from fastunknot.geometry import ScanLimit
from fastunknot.scan import khovanov_rank
from fastunknot.window_scan import WindowScan, khovanov_window


def selected(ranks, lower, upper):
    return {h: rank for h, rank in ranks.items() if lower <= h <= upper}


class WindowScanTests(unittest.TestCase):
    def test_empty_diagram_and_validation(self):
        self.assertEqual(khovanov_window([], 0, 0)["by_degree"], {0: 2})
        self.assertEqual(khovanov_window([], 1, 2)["by_degree"], {})
        for lower, upper in ((2, 1), (True, 1), (0, 1.0)):
            with self.assertRaises(ValueError):
                khovanov_window([], lower, upper)
        with self.assertRaises(ValueError):
            khovanov_window([], 0, 0, max_objects=-1)
        d = Diagram.from_braid(2, [1, 1, 1])
        for order in ([0, 0, 1], [0, 1], [0, 1, 3]):
            with self.assertRaises(ValueError):
                khovanov_window(d.pd, 0, 1, order=order)
        with self.assertRaises(ScanLimit):
            khovanov_window(d.pd, 0, 1, seconds=0)

    def test_curl_normalization_and_both_guards(self):
        # The repository's signs() convention is authoritative; generator
        # signs must not be substituted for these oriented crossing signs.
        positive_word = Diagram.from_braid(2, [1])
        negative_word = Diagram.from_braid(2, [-1])
        self.assertEqual(positive_word.signs(), [-1])
        self.assertEqual(negative_word.signs(), [1])
        for d in (positive_word, negative_word):
            shift = d.signs().count(-1)
            self.assertEqual(khovanov_window(d.pd, shift, shift)["by_degree"],
                             {shift: 2})
        # The first zero needs the outgoing guard, the second the incoming
        # guard: one cannot simply retain the queried chain group alone.
        self.assertEqual(khovanov_window(positive_word.pd, 0, 0)["by_degree"], {})
        self.assertEqual(khovanov_window(negative_word.pd, 1, 1)["by_degree"], {})

    def test_every_window_and_mirror_of_small_diagrams(self):
        diagrams = [
            Diagram.from_braid(2, [1] * 5),
            Diagram.from_braid(3, [1, -2] * 2),
            Diagram.from_braid(3, [1, 2] * 4),
        ]
        for d in diagrams:
            n = d.crossings
            full = khovanov_rank(d.pd)["by_degree"]
            mirror = d.mirror()
            for h in range(-1, n + 2):
                for upper in (h, h + 1):
                    result = khovanov_window(d.pd, h, upper, check_d_squared=True)
                    self.assertEqual(result["by_degree"], selected(full, h, upper))
                reflected = khovanov_window(mirror.pd, n - h, n - h,
                                            check_d_squared=True)
                self.assertEqual(reflected["by_degree"],
                                 {n - k: v for k, v in full.items() if k == h})

    def test_random_orders_windows_and_cache_modes(self):
        rng = random.Random(20261007)
        checked = 0
        while checked < 32:
            strands = rng.choice((3, 4))
            word = [rng.choice((-1, 1)) * rng.randrange(1, strands)
                    for _ in range(rng.randrange(4, 10))]
            try:
                d = Diagram.from_braid(strands, word)
            except DiagramError:
                continue
            full = khovanov_rank(d.pd)["by_degree"]
            order = list(range(d.crossings))
            rng.shuffle(order)
            lower = rng.randrange(-1, d.crossings + 2)
            upper = lower + rng.randrange(3)
            for cached in (False, True):
                result = khovanov_window(
                    d.pd, lower, upper, order=order, check_d_squared=True,
                    shape_cache=cached,
                )
                self.assertEqual(result["by_degree"], selected(full, lower, upper),
                                 (word, order, lower, upper, cached))
            checked += 1

    def test_unreduced_cube_with_pruning_is_still_a_complex(self):
        d = Diagram.from_braid(3, [1, -2] * 2)
        full = khovanov_rank(d.pd)["by_degree"]
        for lower, upper in ((0, 0), (1, 2), (4, 4)):
            for order in (list(range(4)), [2, 0, 3, 1]):
                state = WindowScan(4, lower, upper)
                for i in order:
                    state.add_crossing(d.pd[i], reduce_now=False)
                    state.check_d_squared()
                state.eliminate()
                self.assertEqual(state.requested_ranks(), selected(full, lower, upper))

    def test_named_alexander_trivial_knots_and_unknot(self):
        for name, expected in (("conway", 10), ("kinoshita_terasaka", 10),
                               ("hard_unknot_8", 2)):
            d = Diagram.from_json(json.loads((ROOT / "examples" / f"{name}.json").read_text()))
            h = d.signs().count(-1)
            result = khovanov_window(d.pd, h, h, check_d_squared=True)
            self.assertEqual(result["window_rank"], expected)
            full = khovanov_rank(d.pd, order=result["order"])
            self.assertEqual(result["by_degree"], selected(full["by_degree"], h, h))

    def test_limits_apply_before_allocation(self):
        d = Diagram.from_braid(2, [-1] * 31)
        order = list(range(31))
        unbounded = khovanov_window(d.pd, 0, 0, order=order)
        ceiling = unbounded["stats"]["max_objects_before_elimination"]
        self.assertLess(ceiling,
                        unbounded["stats"]["max_unfiltered_expansion_of_retained_prefix"])
        bounded = khovanov_window(d.pd, 0, 0, order=order, max_objects=ceiling)
        self.assertEqual(bounded["by_degree"], {0: 2})
        with self.assertRaises(ScanLimit):
            khovanov_rank(d.pd, order=order, max_objects=ceiling)
        with self.assertRaises(ScanLimit):
            khovanov_window(d.pd, 0, 0, order=order, max_objects=ceiling - 1)

    def test_guard_pruning_ablation_and_full_window(self):
        d = Diagram.from_braid(3, [-1, -2] * 5)
        for lower, upper in ((0, 0), (0, 2), (4, 7), (-2, 12)):
            first = khovanov_window(d.pd, lower, upper, prune_isolated_guards=True)
            second = khovanov_window(d.pd, lower, upper, prune_isolated_guards=False)
            self.assertEqual(first["by_degree"], second["by_degree"])
        full = khovanov_rank(d.pd)
        wide = khovanov_window(d.pd, 0, d.crossings, order=full["order"])
        self.assertEqual(wide["by_degree"], full["by_degree"])
        self.assertTrue(wide["complete_rank"])
        self.assertEqual(wide["window_rank"], full["rank"])
        self.assertEqual(wide["stats"]["discarded_before_allocation"], 0)


if __name__ == "__main__":
    unittest.main()
