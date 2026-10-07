"""Direct reduced scanner and decision-only direct-summand checks."""
from itertools import product
import json
from pathlib import Path
import random
import unittest

from fastunknot import Diagram, DiagramError, khovanov_rank
from fastunknot.geometry import ScanLimit
from fastunknot.planar import Planar
from fastunknot.reduced_scan import (
    ReducedPlanar, ReducedScan, cut_edge, reduced_khovanov_decision,
    reduced_khovanov_rank,
)


ROOT = Path(__file__).resolve().parents[1]


def load(name):
    return Diagram.from_json(json.loads((ROOT / "examples" / (name + ".json")).read_text()))


def matchings(points):
    if not points:
        yield ()
        return
    for k in range(1, len(points), 2):
        for inside in matchings(points[1:k]):
            for outside in matchings(points[k + 1:]):
                yield tuple(sorted(((points[0], points[k]),) + inside + outside))


def lift(value):
    out = 0
    while value:
        low = value & -value
        out |= 1 << (2 * (low.bit_length() - 1))
        value ^= low
    return out


def project(value):
    out = 0
    while value:
        low = value & -value
        monomial = low.bit_length() - 1
        if not monomial & 1:
            out |= 1 << (monomial >> 1)
        value ^= low
    return out


class PointedAlgebraTests(unittest.TestCase):
    def test_exhaustive_quotient_compositions(self):
        """All polynomial inputs on all triples of planar matchings through 6 ends."""
        checked = 0
        for pairs in (1, 2, 3):
            points = tuple(range(2 * pairs))
            ordinary = Planar(shape_cache=False)
            pointed = ReducedPlanar(0, shape_cache=False)
            pointed.stage(frozenset(points), (0, 0, 0, 0))
            ids = []
            for m in matchings(points):
                a, b = ordinary.intern(m), pointed.intern(m)
                self.assertEqual(a, b)
                ids.append(a)
            for a, b, c in product(ids, repeat=3):
                k1, k2 = ordinary.basis(a, b)[1], ordinary.basis(b, c)[1]
                for f in range(1 << (1 << (k1 - 1))):
                    for g in range(1 << (1 << (k2 - 1))):
                        actual = pointed.compose(a, b, c, f, g)
                        expected = project(ordinary.compose(a, b, c, lift(f), lift(g)))
                        self.assertEqual(actual, expected, (pairs, a, b, c, f, g))
                        checked += 1
        self.assertGreater(checked, 1000)


class PointedScannerTests(unittest.TestCase):
    def test_named_ranks_and_caches(self):
        for name in ("trefoil", "figure_eight", "conway", "kinoshita_terasaka",
                     "torus_3_5", "hard_unknot_8", "unknot_braid40"):
            d = load(name)
            full = khovanov_rank(d.pd)
            expected = {h: dim // 2 for h, dim in full["by_degree"].items()}
            for cache in (False, True):
                reduced = reduced_khovanov_rank(d.pd, order=full["order"],
                                                shape_cache=cache, check_d_squared=True)
                self.assertEqual(reduced["by_degree"], expected, (name, cache))
                self.assertEqual(reduced["rank"], full["reduced_rank"])

    def test_exhaustive_small_braids_and_decisions(self):
        # The larger portable exhaustive run also invokes the independent
        # reduced cube oracle on all 2,898 diagrams through 6 crossings.
        rng = random.Random(7291107)
        for word in product((-2, -1, 1, 2), repeat=4):
            try:
                d = Diagram.from_braid(3, word)
            except DiagramError:
                continue
            full = khovanov_rank(d.pd)
            order = rng.sample(range(4), 4)
            edge = rng.randrange(8)
            reduced = reduced_khovanov_rank(d.pd, order=order, edge=edge,
                                            check_d_squared=True)
            self.assertEqual(reduced["rank"], full["reduced_rank"], word)
            decision = reduced_khovanov_decision(d.pd, order=order, edge=edge,
                                                 check_d_squared=True)
            self.assertEqual(decision["status"], "UNKNOT" if reduced["rank"] == 1 else "KNOTTED")
            self.assertLessEqual(decision["lower_bound"], reduced["rank"])

    def test_last_edge_preserves_every_proper_frontier(self):
        d = load("conway")
        rng = random.Random(827)
        for _ in range(40):
            order = rng.sample(range(d.crossings), d.crossings)
            cut, ends, _ = cut_edge(d.pd, order)
            old, new = set(), set()
            for position, index in enumerate(order):
                for label in d.pd[index]:
                    old.symmetric_difference_update((label,))
                for label in cut[index]:
                    new.symmetric_difference_update((label,))
                if position < len(order) - 1:
                    self.assertEqual(len(old), len(new))
                else:
                    self.assertEqual(old, set())
                    self.assertEqual(new, set(ends))

    def test_before_closure_stop_and_replay(self):
        d = load("conway_sum_2")
        order = list(range(d.crossings))
        result = reduced_khovanov_decision(d.pd, order=order, check_d_squared=True)
        self.assertEqual(result["status"], "KNOTTED")
        self.assertIsNone(result["reduced_rank"])
        certificate = result["certificate"]
        self.assertEqual(certificate["stage"], 11)
        self.assertEqual(certificate["remaining_crossings"], 11)
        cut, ends, _ = cut_edge(d.pd, order, edge=result["marked_edge"])
        scan = ReducedScan(ends[0], shape_cache=False)
        for i in order[:certificate["stage"]]:
            scan.add_crossing(cut[i])
        for obj in certificate["objects"]:
            ident = obj["object_id"]
            self.assertIsNotNone(scan.mid[ident])
            self.assertFalse(scan.out[ident])
            self.assertFalse(scan.inc[ident])
            self.assertEqual(scan.deg[ident], obj["homological_degree"])
            self.assertEqual([list(p) for p in scan.algebra.pairs[scan.mid[ident]]], obj["matching"])

    def test_limits_are_not_verdicts(self):
        d = load("trefoil")
        for function in (reduced_khovanov_rank, reduced_khovanov_decision):
            with self.assertRaises(ScanLimit):
                function(d.pd, max_objects=0)
            with self.assertRaises(ScanLimit):
                function(d.pd, seconds=0)
            with self.assertRaises(ValueError):
                function(d.pd, order=[0, 0, 1])
            self.assertEqual(function(())["reduced_rank"], 1)


if __name__ == "__main__":
    unittest.main()
