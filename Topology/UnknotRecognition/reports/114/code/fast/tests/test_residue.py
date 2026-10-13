"""Check the survivor theorem and degree-gap shortcut against actual scans."""
from collections import Counter
import copy
import json
import random
import subprocess
import sys
import unittest

from fastunknot import Diagram, recognize
from fastunknot.diagram import DiagramError
from fastunknot.geometry import ScanLimit
from fastunknot.ordering import best_scan_order
from fastunknot.residue import AdaptiveScan, ResidueScan, survivor_profile
from fastunknot.scan import khovanov_rank
from fastunknot.scan_fast import FastScan


def actual_profile(scan):
    return dict(Counter((matching, scan.deg[a]) for a, matching in enumerate(scan.mid)
                        if matching is not None))


def example(scan_type, degrees, rows):
    scan = scan_type(shape_cache=False)
    matching = scan.algebra.intern(((0, 1),))
    scan.points = frozenset((0, 1))
    scan.mid = [matching] * len(degrees)
    scan.deg = list(degrees)
    scan.out = copy.deepcopy(rows)
    scan.inc = [set() for _ in degrees]
    for a, row in enumerate(rows):
        for b in row:
            scan.inc[b].add(a)
    scan.live = len(degrees)
    return scan


class ResidueTests(unittest.TestCase):
    def test_prediction_is_not_a_zero_differential_certificate(self):
        # A dot has zero residue but is a nonzero map between surviving objects.
        scan = example(ResidueScan, [0, 1], [{1: 2}, {}])
        scan.check_d_squared()
        self.assertEqual(sum(survivor_profile(scan).values()), 2)
        scan.eliminate()
        self.assertEqual(scan.out[0], {1: 2})
        self.assertEqual(scan.stats["residue_shortcuts"], 0)

    def test_gap_shortcut_avoids_cobordism_composition(self):
        # A nontrivial unit 1+x contracts two objects, leaving degrees 0 and 2.
        scan = example(ResidueScan, [0, 0, 1, 2], [{}, {2: 3}, {}, {}])
        scan.check_d_squared()
        expected = survivor_profile(scan)
        scan._compose = lambda key: self.fail("shortcut should not compose cobordisms")
        scan.eliminate()
        self.assertEqual(actual_profile(scan), expected)
        self.assertEqual(scan.stats["residue_skipped_pairs"], 1)
        self.assertFalse(any(scan.out))
        # The reduced complex remains usable for subsequent gluing.
        scan.add_crossing((0, 1, 2, 2))
        scan.check_d_squared()

    def test_adjacent_survivors_can_acquire_a_radical_map(self):
        # Cancelling a scalar pivot creates x between the two other objects.
        scan = example(ResidueScan, [0, 0, 1, 1], [{2: 1, 3: 2}, {2: 1}, {}, {}])
        scan.check_d_squared()
        expected = survivor_profile(scan)
        scan.eliminate()
        self.assertEqual(actual_profile(scan), expected)
        self.assertEqual(scan.stats["residue_shortcuts"], 0)
        self.assertTrue(any(scan.out))
        self.assertEqual(sum(len(row) for row in scan.out if row), 1)

    def test_typed_residue_and_dead_slots(self):
        scan = example(FastScan, [0, 1, 3], [{1: 1}, {}, {}])
        scan.mid[0] = scan.algebra.intern(((0, 1), (2, 3)))
        other = scan.algebra.intern(((0, 2), (1, 3)))
        # Different matching types: coefficient 1 is not a scalar identity.
        scan.mid[1] = other
        scan.mid[2] = None
        scan.out[2] = scan.inc[2] = None
        before = copy.deepcopy((scan.mid, scan.deg, scan.out, scan.inc))
        self.assertEqual(sum(survivor_profile(scan).values()), 2)
        self.assertEqual((scan.mid, scan.deg, scan.out, scan.inc), before)

    def test_contractible_complex(self):
        scan = example(ResidueScan, [0, 1], [{1: 3}, {}])
        scan.eliminate()
        self.assertEqual(scan.live, 0)
        self.assertEqual(scan.mid, [])

    def test_invalid_residue_complex(self):
        scan = example(FastScan, [0, 1, 2], [{1: 1}, {2: 1}, {}])
        with self.assertRaises(ArithmeticError):
            survivor_profile(scan)

    def test_profile_deadline_and_hooks(self):
        scan = FastScan(deadline=0)
        with self.assertRaises(ScanLimit):
            survivor_profile(scan)
        scan = FastScan()
        def stop():
            raise ScanLimit("hook")
        scan.hook = stop
        with self.assertRaisesRegex(ScanLimit, "hook"):
            survivor_profile(scan)

    def test_random_profiles_and_every_degree(self):
        rng = random.Random(2026100721)
        accepted = stages = 0
        while accepted < 120:
            strands = rng.randrange(2, 6)
            length = rng.randrange(1, 13)
            word = [rng.choice((-1, 1)) * rng.randrange(1, strands) for _ in range(length)]
            try:
                diagram = Diagram.from_braid(strands, word)
            except DiagramError:
                continue
            order = best_scan_order(diagram.pd)
            if accepted % 2:
                rng.shuffle(order)
            scan = FastScan(shape_cache=False)
            for crossing in order:
                scan.add_crossing(diagram.pd[crossing], reduce_now=False)
                scan.check_d_squared()
                predicted = survivor_profile(scan)
                scan.eliminate()
                self.assertEqual(actual_profile(scan), predicted, (strands, word, order, crossing))
                scan.check_d_squared()
                stages += 1
            changed = khovanov_rank(diagram.pd, order=order, reduction="residue", check_d_squared=True)
            self.assertEqual(changed["by_degree"], scan.ranks_by_degree(), (strands, word, order))
            adaptive = khovanov_rank(diagram.pd, order=order, reduction="adaptive", check_d_squared=True)
            self.assertEqual(adaptive["by_degree"], scan.ranks_by_degree(), (strands, word, order))
            if accepted < 20:
                independent = khovanov_rank(diagram.pd, order=order, pivot="lifo", algebra="sets")
                self.assertEqual(changed["by_degree"], independent["by_degree"])
            accepted += 1
        self.assertGreater(stages, 600)

    def test_tail_composition_and_option_guards(self):
        pd = Diagram.from_braid(3, [1, -2] * 4).pd
        baseline = khovanov_rank(pd)["by_degree"]
        for options in ({"tail": 3}, {"composition": "component"}, {"composition": "component-dense"}):
            self.assertEqual(khovanov_rank(pd, reduction="residue", **options)["by_degree"], baseline)
        for options in ({"pivot": "lifo"}, {"algebra": "sets"}, {"self_inverse": False}, {"race": 2}):
            with self.assertRaises(ValueError):
                khovanov_rank(pd, reduction="residue", **options)
        with self.assertRaises(ValueError):
            khovanov_rank(pd, reduction="unknown")
        with self.assertRaises(ScanLimit):
            khovanov_rank(pd, reduction="residue", max_objects=1)
        with self.assertRaises(ScanLimit):
            khovanov_rank(pd, reduction="residue", seconds=0)

    def test_cli(self):
        data = json.dumps({"braid": {"strands": 2, "word": [1, 1, 1]}})
        command = [sys.executable, "-m", "fastunknot", "khovanov", "-", "--reduction", "residue"]
        result = subprocess.run(command, input=data, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout)["rank"], 6)
        for flag in ("--shared", "--twist"):
            result = subprocess.run(command + [flag], input=data, capture_output=True, text=True)
            self.assertEqual(result.returncode, 2)

    def test_pause_and_resume_preserve_a_valid_complex(self):
        from benchmark_residue import dense_two_term
        scan = dense_two_term(FastScan, 16)
        expected = survivor_profile(scan)
        self.assertFalse(scan.eliminate(update_budget=256))
        self.assertGreater(scan.stats["eliminations"], 0)
        self.assertGreater(scan.live, 1)
        self.assertFalse(any(scan.small))
        scan.check_d_squared()
        self.assertEqual(survivor_profile(scan), expected)
        self.assertTrue(scan.eliminate())
        self.assertEqual(actual_profile(scan), expected)
        self.assertEqual(scan.live, 1)

    def test_adaptive_switch_and_declined_shortcut(self):
        from benchmark_residue import dense_two_term
        scan = dense_two_term(AdaptiveScan, 32)
        scan.eliminate()
        self.assertEqual(scan.live, 1)
        self.assertEqual(scan.stats["adaptive_switches"], 1)
        self.assertEqual(scan.stats["adaptive_shortcuts"], 1)
        self.assertEqual(scan.stats["adaptive_fallbacks"], 0)
        # Add a disjoint dot differential: its adjacent survivors must remain.
        scan = dense_two_term(AdaptiveScan, 32)
        a = len(scan.mid)
        scan.mid.extend([scan.mid[0], scan.mid[0]])
        scan.deg.extend([0, 1])
        scan.out.extend([{a + 1: 2}, {}])
        scan.inc.extend([set(), {a}])
        scan.live += 2
        scan.check_d_squared()
        expected = survivor_profile(scan)
        scan.eliminate()
        scan.check_d_squared()
        self.assertEqual(actual_profile(scan), expected)
        self.assertEqual(scan.live, 3)
        self.assertEqual(scan.stats["adaptive_fallbacks"], 1)
        self.assertEqual(scan.stats["adaptive_shortcuts"], 0)
        self.assertTrue(any(scan.out))

    def test_adaptive_pipeline_and_resource_handling(self):
        diagram = Diagram.from_braid(2, [1, 1, 1])
        options = dict(use_braid=False, use_seifert=False, use_reduction=False,
                       use_descending=False, use_alexander=False, use_jones=False,
                       use_factorization=False, reduction="adaptive")
        result = recognize(diagram, **options)
        self.assertEqual(result.status, "KNOTTED")
        self.assertEqual(result.evidence["khovanov"]["reduction"], "adaptive")
        self.assertEqual(result.evidence["khovanov"]["scan_stats"]["residue_profiles"], 0)
        self.assertEqual(recognize(diagram, max_objects=1, **options).status, "UNKNOWN")
        self.assertEqual(recognize(diagram, seconds=0, **options).status, "UNKNOWN")
        for mode in ("residue", "adaptive"):
            with self.assertRaises(ValueError):
                recognize(diagram, reduction=mode, backend="shared")
        with self.assertRaises(ValueError):
            recognize(diagram, reduction="invalid")


if __name__ == "__main__":
    unittest.main()
