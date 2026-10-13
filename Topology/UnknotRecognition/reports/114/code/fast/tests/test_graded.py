"""Typed quantum profiles and the support-only reduction reference."""
from collections import Counter, defaultdict
import copy
import random
import unittest

from fastunknot import Diagram
from fastunknot.diagram import DiagramError
from fastunknot.geometry import ScanLimit
from fastunknot.graded import (GradedScan, GradedResidueScan, GradedAdaptiveScan,
    graded_survivor_profile, radical_hom_dimension, support_has_no_differential)
from fastunknot.ordering import best_scan_order
from fastunknot.residue import survivor_profile
from fastunknot.scan import khovanov_rank


def make_complex(scan_type, degrees, quantum, rows, pairs=((0, 1),)):
    scan = scan_type(shape_cache=False)
    matching = scan.algebra.intern(pairs)
    scan.points = frozenset(x for pair in pairs for x in pair)
    scan.mid = [matching] * len(degrees)
    scan.deg, scan.qshift = list(degrees), list(quantum)
    scan.out = copy.deepcopy(rows)
    scan.inc = [set() for _ in degrees]
    for a, row in enumerate(rows):
        for b in row:
            scan.inc[b].add(a)
    scan.live = len(degrees)
    return scan


def live_profile(scan):
    return dict(Counter((matching, scan.deg[a], scan.qshift[a])
                        for a, matching in enumerate(scan.mid) if matching is not None))


class GradedTests(unittest.TestCase):
    def test_hom_dimension_including_matching_distance(self):
        scan = make_complex(GradedScan, [0], [0], [{}], ((0, 1), (2, 3)))
        matching = scan.mid[0]
        other = scan.algebra.intern(((0, 3), (1, 2)))
        self.assertEqual([radical_hom_dimension(scan, matching, 0, matching, q)
                          for q in range(-1, 6)], [0, 0, 0, 2, 0, 1, 0])
        self.assertEqual([radical_hom_dimension(scan, matching, 0, other, q)
                          for q in range(-1, 6)], [0, 0, 1, 0, 1, 0, 0])

    def test_support_can_certify_adjacent_degrees(self):
        scan = make_complex(GradedResidueScan, [0, 0, 1, 1], [2, 0, 0, 0],
                            [{}, {2: 1}, {}, {}])
        scan.check_grading()
        scan.check_d_squared()
        expected = graded_survivor_profile(scan)
        self.assertEqual({h for _, h, _ in expected}, {0, 1})
        self.assertTrue(support_has_no_differential(scan, expected))
        scan._compose = lambda key: self.fail("certified shortcut must not compose")
        scan.eliminate()
        self.assertEqual(live_profile(scan), expected)
        self.assertEqual(scan.stats["graded_skipped_pairs"], 1)
        self.assertEqual(scan.stats["graded_adjacent_shortcuts"], 1)
        self.assertFalse(any(scan.out))
        scan.add_crossing((0, 1, 2, 2))
        scan.check_grading()
        scan.check_d_squared()

    def test_survivors_do_not_determine_the_differential(self):
        scan = make_complex(GradedResidueScan, [0, 1], [0, 2], [{1: 2}, {}])
        scan.check_grading()
        scan.check_d_squared()
        profile = graded_survivor_profile(scan)
        self.assertFalse(support_has_no_differential(scan, profile))
        scan.eliminate()
        self.assertEqual(scan.out, [{1: 2}, {}])
        self.assertEqual(scan.stats["graded_shortcuts"], 0)

    def test_undotted_map_between_distinct_matchings_is_radical(self):
        scan = make_complex(GradedResidueScan, [0, 1], [0, 1], [{1: 1}, {}],
                            ((0, 1), (2, 3)))
        scan.mid[1] = scan.algebra.intern(((0, 3), (1, 2)))
        scan.check_grading()
        profile = graded_survivor_profile(scan)
        self.assertEqual(sum(profile.values()), 2)
        self.assertFalse(support_has_no_differential(scan, profile))
        scan.eliminate()
        self.assertEqual(scan.out, [{1: 1}, {}])

    def test_profile_preserves_state_and_handles_dead_slots(self):
        scan = make_complex(GradedScan, [0, 1, 3], [0, 0, 7], [{1: 1}, {}, {}])
        scan.eliminate()
        before = copy.deepcopy((scan.mid, scan.deg, scan.qshift, scan.out, scan.inc))
        self.assertEqual(graded_survivor_profile(scan), live_profile(scan))
        self.assertEqual((scan.mid, scan.deg, scan.qshift, scan.out, scan.inc), before)

    def test_invalid_grading_and_noncomplex_are_rejected(self):
        scan = make_complex(GradedScan, [0, 1], [0, 0], [{1: 3}, {}])
        with self.assertRaises(ArithmeticError):
            scan.check_grading()
        with self.assertRaises(ArithmeticError):
            graded_survivor_profile(scan)
        scan = make_complex(GradedScan, [0, 2], [0, 0], [{1: 1}, {}])
        with self.assertRaises(ArithmeticError):
            scan.check_grading()
        scan = make_complex(GradedScan, [0, 1, 2], [0, 0, 0],
                            [{1: 1}, {2: 1}, {}])
        with self.assertRaises(ArithmeticError):
            graded_survivor_profile(scan)

    def test_profile_resource_hooks(self):
        scan = GradedScan(deadline=0)
        with self.assertRaises(ScanLimit):
            graded_survivor_profile(scan)
        scan = GradedScan()
        def stop():
            raise ScanLimit("hook")
        scan.hook = stop
        with self.assertRaisesRegex(ScanLimit, "hook"):
            graded_survivor_profile(scan)

    def test_every_quantum_profile_across_seeded_actual_scans(self):
        rng = random.Random(2026100818)
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
            baseline = GradedScan(shape_cache=False)
            for crossing in order:
                baseline.add_crossing(diagram.pd[crossing], reduce_now=False)
                baseline.check_grading()
                baseline.check_d_squared()
                profile = graded_survivor_profile(baseline)
                erased = defaultdict(int)
                for (matching, degree, _), multiplicity in profile.items():
                    erased[matching, degree] += multiplicity
                self.assertEqual(dict(erased), survivor_profile(baseline))
                baseline.eliminate()
                self.assertEqual(live_profile(baseline), profile)
                baseline.check_grading()
                baseline.check_d_squared()
                stages += 1
            expected = baseline.ranks_by_bidegree()
            for scan_type in (GradedResidueScan, GradedAdaptiveScan):
                changed = scan_type(shape_cache=False)
                for crossing in order:
                    changed.add_crossing(diagram.pd[crossing])
                    changed.check_grading()
                    changed.check_d_squared()
                self.assertEqual(changed.ranks_by_bidegree(), expected,
                                 (strands, word, order, scan_type.__name__))
            if accepted < 12:
                independent = khovanov_rank(diagram.pd, order=order,
                                            pivot="lifo", algebra="sets")
                self.assertEqual(baseline.ranks_by_degree(), independent["by_degree"])
            accepted += 1
        self.assertGreater(stages, 300)


if __name__ == "__main__":
    unittest.main()
