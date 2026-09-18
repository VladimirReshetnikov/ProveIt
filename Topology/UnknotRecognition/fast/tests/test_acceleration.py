"""Tests for the 0.2 accelerations.  Each new code path is checked against the
0.1 reference implementation or an independent computation."""
from __future__ import annotations

import json
import os
import random
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

from fastunknot import (Diagram, alexander_obstruction, alexander_polynomial, factored_khovanov_rank,  # noqa: E402
                        jones_obstruction, khovanov_rank, recognize, visible_factors)
from fastunknot import ordering, scan_reference  # noqa: E402
from fastunknot.algebra import BitAlgebra  # noqa: E402
from fastunknot.filters import FilterLimit  # noqa: E402
from fastunknot.simplify import (descending_start, descending_start_quadratic, legal_moves, replay,  # noqa: E402
                                 simplify, simplify_reference)

EXAMPLES = os.path.join(ROOT, "examples")


def load(name):
    with open(os.path.join(EXAMPLES, name), encoding="utf-8") as handle:
        return Diagram.from_json(json.load(handle))


def random_knot_braids(seed, count, strands=(3, 4, 5), lengths=(4, 12)):
    rng = random.Random(seed)
    found = 0
    while found < count:
        s = rng.choice(strands)
        word = [rng.choice([-1, 1]) * rng.randint(1, s - 1) for _ in range(rng.randint(*lengths))]
        try:
            yield Diagram.from_braid(s, word)
        except ValueError:
            continue
        found += 1


def matchings(points):
    """All crossingless matchings of points in convex position (the algebra needs planarity)."""
    if not points:
        yield frozenset()
        return
    first = points[0]
    for i in range(1, len(points), 2):
        for inner in matchings(points[1:i]):
            for outer in matchings(points[i + 1:]):
                yield inner | outer | {frozenset((first, points[i]))}


class AlgebraTests(unittest.TestCase):
    def test_bit_composition_equals_set_composition(self):
        rng = random.Random(4)
        all_matchings = list(matchings(list(range(6))))
        algebra = BitAlgebra()
        for _ in range(400):
            a, b, c = (rng.choice(all_matchings) for _ in range(3))

            def random_morphism(x, y):
                keys = algebra.basis(x, y).keys
                return {frozenset(k for k in keys if rng.random() < 0.4) for _ in range(rng.randint(1, 3))}

            f, g = random_morphism(a, b), random_morphism(b, c)
            expected = scan_reference.compose(set(f), set(g), a, b, c)
            got = algebra.decode(algebra.compose(algebra.encode(f, a, b), algebra.encode(g, b, c), a, b, c), a, c)
            self.assertEqual(got, expected)

    def test_units_are_involutions(self):
        m = next(iter(matchings(list(range(6)))))
        for self_inverse in (True, False):
            algebra = BitAlgebra(self_inverse=self_inverse)
            for unit in range(1, 1 << 8, 2):           # all units of End(m): 3 circles, constant term 1
                inv = algebra.inverse(unit, m)
                self.assertEqual(inv, unit)
                self.assertEqual(algebra.compose(unit, inv, m, m, m), 1)
        with self.assertRaises(ValueError):
            BitAlgebra().inverse(2, m)


class ScannerTests(unittest.TestCase):
    def test_all_configurations_agree_with_reference(self):
        configs = [dict(), dict(pivot="lifo"), dict(algebra="sets"), dict(tail=1), dict(tail=3),
                   dict(algebra="sets", pivot="lifo", self_inverse=False), dict(check_d_squared=True)]
        for d in random_knot_braids(21, 25):
            expected = scan_reference.khovanov_rank(d.pd)
            for config in configs:
                got = khovanov_rank(d.pd, **config)
                self.assertEqual((got["rank"], got["by_degree"]), (expected["rank"], expected["by_degree"]), config)

    def test_orders_are_identical_to_reference(self):
        for d in random_knot_braids(22, 40, lengths=(1, 20)):
            pd = list(d.pd)
            for start in range(len(pd)):
                self.assertEqual(ordering.scan_order(pd, start), scan_reference.scan_order(pd, start))
            self.assertEqual(ordering.best_scan_order(pd, 12), scan_reference.best_scan_order(pd, 12))
        with self.assertRaises(ValueError):
            khovanov_rank(Diagram.from_braid(2, [1, 1, 1]).pd, order=[0, 1])

    def test_shape_cache_is_transparent(self):
        configs = [dict(shape_cache=False), dict(shape_cache=True, check_d_squared=True), dict(shape_cache=True, tail=2)]
        inputs = list(random_knot_braids(23, 25)) + [Diagram.from_braid(3, [1, 2] * 7), Diagram.from_braid(4, [1, 2, 3] * 5),
                                                     Diagram.from_braid(9, list(range(1, 9)))]
        for d in inputs:
            expected = scan_reference.khovanov_rank(d.pd)
            for config in configs:
                got = khovanov_rank(d.pd, **config)
                self.assertEqual((got["rank"], got["by_degree"]), (expected["rank"], expected["by_degree"]), config)
        torus = Diagram.from_braid(3, [1, 2] * 11).pd
        self.assertGreater(khovanov_rank(torus)["stats"]["shape_hits"], 0)          # chosen automatically and used
        self.assertGreater(khovanov_rank(torus)["stats"]["result_hits"], 0)
        self.assertEqual(khovanov_rank(torus, shape_cache=False)["stats"]["shape_hits"], 0)
        self.assertEqual(khovanov_rank(load("conway.json").pd)["stats"]["shape_hits"], 0)      # no repeats: left off
        conway = [tuple(c) for c in load("conway.json").pd]
        self.assertEqual(ordering.repeated_stages(conway, ordering.best_scan_order(conway, 12)), 0)
        self.assertGreaterEqual(ordering.repeated_stages(torus, ordering.best_scan_order(torus, 12)), 8)
        # a chain of kinks settles into one picture once the boundary has its steady size:
        # n kinks repeat n - 3 times (none for three kinks, whose three stages all differ)
        for n, expected in ((3, 0), (5, 2), (8, 5), (12, 9)):
            kinks = [tuple(c) for c in Diagram.from_braid(n + 1, list(range(1, n + 1))).pd]
            self.assertEqual(ordering.repeated_stages(kinks, ordering.best_scan_order(kinks, 12)), expected)

    def test_circle_numbering_is_canonical(self):
        # The cross-stage plan cache needs: numbering by minimal label, whichever matching is walked
        # first, and compatible with monotone relabelling.
        from fastunknot.planar import Planar
        rng = random.Random(24)

        def matching(labels):
            if not labels:
                return []
            j = rng.randrange(1, len(labels), 2)
            return [(labels[0], labels[j])] + matching(labels[1:j]) + matching(labels[j + 1:])

        for _ in range(400):
            labels = sorted(rng.sample(range(60), rng.choice((2, 4, 6, 8, 10))))
            a, b = tuple(sorted(matching(labels))), tuple(sorted(matching(labels)))
            first, second, moved = Planar(), Planar(), Planar()
            owner, count = first.basis(first.intern(a), first.intern(b))
            self.assertEqual(second.basis(second.intern(b), second.intern(a)), (owner, count))
            minima = [min(p for p in owner if owner[p] == c) for c in range(count)]
            self.assertEqual(minima, sorted(minima))
            f = {p: 5 * p + 3 for p in labels}
            shifted, _ = moved.basis(moved.intern(tuple((f[p], f[q]) for p, q in a)),
                                     moved.intern(tuple((f[p], f[q]) for p, q in b)))
            self.assertEqual(shifted, {f[p]: c for p, c in owner.items()})

    def test_tie_rules_and_race(self):
        for d in random_knot_braids(29, 30, strands=(3, 4, 5), lengths=(6, 18)):
            pd = [tuple(c) for c in d.pd]
            expected = khovanov_rank(pd)
            for rule in ordering.TIE_RULES:
                order = ordering.best_scan_order(pd, 12, ties=rule)
                self.assertEqual(sorted(order), list(range(len(pd))))
                got = khovanov_rank(pd, order=order)
                self.assertEqual((got["rank"], got["by_degree"]), (expected["rank"], expected["by_degree"]))
            self.assertEqual(ordering.best_scan_order(pd, 12, ties="index"), ordering.best_scan_order(pd, 12))
        with self.assertRaises(ValueError):
            ordering.best_scan_order([(0, 1, 1, 0)], 1, ties="newest")
        with self.assertRaises(ValueError):
            khovanov_rank(load("conway.json").pd, race=0)
        # no competitor is started within the head start, and the result says who won
        quiet = khovanov_rank(load("conway.json").pd, race=3, race_after=60.0)
        self.assertEqual((quiet["race_winner"], quiet["reduced_rank"]), ("index", 33))
        self.assertNotIn("race_winner", khovanov_rank(load("conway.json").pd))
        # competitors started at once: whoever wins, the result is the same, and nothing is left running
        pd = load("stress_braid5_36.json").pd
        expected = khovanov_rank(pd)
        raced = khovanov_rank(pd, race=3, race_after=0.0)
        self.assertIn(raced["race_winner"], ordering.TIE_RULES)
        self.assertEqual((raced["rank"], raced["by_degree"]), (expected["rank"], expected["by_degree"]))
        # a competitor wins when the default order is handicapped by a deliberately bad explicit order
        bad = list(range(len(pd)))[::2] + list(range(len(pd)))[1::2]
        raced = khovanov_rank(pd, order=bad, race=2, race_after=0.0, seconds=120)
        self.assertEqual((raced["rank"], raced["by_degree"]), (expected["rank"], expected["by_degree"]))
        self.assertEqual(raced["race_winner"], "oldest")
        self.assertEqual(recognize(load("hard_unknot_8.json"), use_r3=False, race=2, race_after=0.0).status, "UNKNOT")

    def test_stress_case_that_timed_out_in_0_1(self):
        result = khovanov_rank(load("stress_braid5_36.json").pd)
        self.assertEqual(result["reduced_rank"], 2949)
        self.assertEqual(khovanov_rank(load("stress_braid5_36.json").pd, tail=1)["by_degree"], result["by_degree"])


class SignTests(unittest.TestCase):
    def test_half_turned_rows(self):
        for d in random_knot_braids(23, 30):
            rng = random.Random(d.crossings)
            turned = Diagram.from_pd([row[2:] + row[:2] if rng.random() < 0.5 else row for row in d.pd])
            self.assertEqual(turned.signs(), d.signs())
            self.assertEqual(alexander_polynomial(turned), alexander_polynomial(d))
            self.assertEqual(jones_obstruction(turned) is None, jones_obstruction(d) is None)


class FilterTests(unittest.TestCase):
    def test_filters_never_flag_unknots(self):
        unknots = [Diagram.from_braid(2, [1]), Diagram.from_braid(2, [-1]), Diagram.from_braid(3, [-1, 2]),
                   load("hard_unknot_8.json"), load("unknot_braid40.json"), load("grid_scrambled_unknot.json"),
                   Diagram.from_braid(4, [1, -2, 3, 2, -2, -3, 3]), Diagram.from_braid(3, [-2, -2, 1, 2, 2, 2])]
        for d in unknots:
            for x in (d, d.mirror()):
                self.assertIsNone(jones_obstruction(x))
                self.assertIsNone(alexander_obstruction(x))

    def test_filters_agree_with_khovanov(self):
        """A filter may only fire on knots whose reduced Khovanov rank exceeds one."""
        fired = 0
        for d in random_knot_braids(24, 60):
            knotted = khovanov_rank(d.pd)["reduced_rank"] > 1
            for witness in (jones_obstruction(d), alexander_obstruction(d)):
                if witness is not None:
                    fired += 1
                    self.assertTrue(knotted)
            if alexander_polynomial(d) != [1]:
                self.assertTrue(knotted)
        self.assertGreater(fired, 10)

    def test_known_knots_and_budget(self):
        for name in ("conway.json", "kinoshita_terasaka.json"):
            self.assertIsNone(alexander_obstruction(load(name)))
            self.assertIsNotNone(jones_obstruction(load(name)))
        self.assertIsNotNone(alexander_obstruction(load("torus_3_5.json")))
        with self.assertRaises(FilterLimit):
            jones_obstruction(load("conway.json"), max_states=1)
        r = recognize(load("conway.json"), jones_max_states=1)      # skipped filter, exact fallback
        self.assertEqual((r.status, r.method), ("KNOTTED", "reduced-khovanov-F2-scan"))


class CommandLineTests(unittest.TestCase):
    def test_fast_parser_agrees_with_argparse_or_declines(self):
        from fastunknot.__main__ import OPTIONS, _fast_parse, _parser
        parser = _parser()
        accepted = [["recognize", "f.json"], ["khovanov", "f.json"], ["jones", "f.json"], ["alexander", "f.json"],
                    ["recognize", "--tail", "2", "f.json", "--pivot", "lifo", "--algebra", "sets", "--output", "o.json"],
                    ["khovanov", "f.json", "--factor", "--race", "2", "--race-after", "0.5", "--check-d2"]]
        everything = ["recognize", "f.json"]              # every option of the table once
        for flag, kind, default, choices, _ in OPTIONS["recognize"]:
            everything += [flag] if kind is None else [flag, str(choices[-1] if choices else kind(3))]
        accepted.append(everything)
        for argv in accepted:
            fast = _fast_parse(argv)
            self.assertIsNotNone(fast, argv)
            self.assertEqual(vars(fast), vars(parser.parse_args(argv)), argv)
        declined = [[], ["recognise", "f"], ["recognize"], ["recognize", "a", "b"], ["recognize", "f", "--help"],
                    ["recognize", "f", "-h"], ["recognize", "f", "--tail"], ["recognize", "f", "--tail", "x"],
                    ["recognize", "f", "--tail=2"], ["recognize", "f", "--pivot", "fifo"], ["recognize", "f", "--tai", "2"],
                    ["recognize", "f", "--seconds", "-1"], ["khovanov", "f", "--no-jones"], ["jones", "f", "--tail", "1"]]
        for argv in declined:                             # these go to argparse, with its own messages
            self.assertIsNone(_fast_parse(argv), argv)

    def test_start_up_stays_light(self):
        import subprocess
        code = ("import sys, fastunknot, fastunknot.__main__; "
                "print([m for m in ('argparse', 'dataclasses', 'typing', 'subprocess', 'inspect', "
                "'fastunknot.scan_reference') if m in sys.modules])")
        out = subprocess.run([sys.executable, "-c", code], capture_output=True, text=True, cwd=ROOT).stdout.strip()
        self.assertEqual(out, "[]")


class ExactAlexanderTests(unittest.TestCase):
    def test_exact_polynomial_only_when_the_modular_test_did_not_run(self):
        import hard_unknots
        # an unknot diagram of 27 crossings that Reidemeister I/II cannot reduce and no filter decides
        d = simplify(Diagram.from_braid(4, hard_unknots.make(4, seed=38)), r3=False)[0]
        self.assertEqual(d.crossings, 27)
        default = recognize(d, use_reduction=False)
        forced = recognize(d, use_reduction=False, use_exact_alexander=True)
        self.assertEqual((default.status, default.method), ("UNKNOT", "reduced-khovanov-F2-scan"))
        self.assertEqual((forced.status, forced.method), ("UNKNOT", "reduced-khovanov-F2-scan"))
        self.assertTrue(default.evidence["alexander_polynomial"].startswith("not computed"))
        self.assertEqual((forced.evidence["alexander_polynomial"], forced.evidence["determinant"]), ("1", 1))
        trefoil = Diagram.from_braid(2, [1, 1, 1])
        self.assertEqual(recognize(trefoil, use_modular=False, use_jones=False).method, "alexander-polynomial")
        self.assertNotIn("alexander_polynomial", recognize(trefoil, use_alexander=False, use_jones=False).evidence)
        for other in random_knot_braids(31, 40, lengths=(4, 16)):
            self.assertEqual(recognize(other).status, recognize(other, use_exact_alexander=True).status)


class FactorTests(unittest.TestCase):
    def test_conway_sums(self):
        for k in (2, 3, 8):
            d = load(f"conway_sum_{k}.json")
            factors, cuts = visible_factors(d)
            self.assertEqual(sorted(f.crossings for f in factors), [11] * k)
            self.assertEqual(len(cuts), k - 1)
            self.assertEqual(factored_khovanov_rank(d)["reduced_rank"], 33 ** k)
        d = load("conway_sum_2.json")
        self.assertEqual(factored_khovanov_rank(d)["by_degree"], khovanov_rank(d.pd)["by_degree"])
        self.assertEqual(visible_factors(load("conway.json"))[0][0].pd, load("conway.json").pd)

    def test_recognition_of_sums(self):
        r = recognize(load("conway_sum_3.json"), use_jones=False)
        self.assertEqual(r.status, "KNOTTED")
        self.assertTrue(r.method.startswith("connected-sum-factor"))
        self.assertEqual(recognize(load("conway_sum_3.json"), use_jones=False, use_factorization=False,
                                   max_objects=500).status, "UNKNOWN")
        # a connected sum of two unknot diagrams that R1/R2 cannot reduce; R3 help undoes it entirely
        hard = [-2, -2, -2, 2, 1, 1, 2, 1]
        double = Diagram.from_braid(5, hard + [g + 2 * (1 if g > 0 else -1) for g in hard])
        self.assertEqual(len(visible_factors(simplify(double, r3=False)[0])[0]), 2)
        self.assertEqual(simplify(double)[0].crossings, 0)
        r = recognize(double)       # factored first; each factor then falls to the late Reidemeister III search
        self.assertEqual((r.status, r.method), ("UNKNOT", "connected-sum-all-factors-trivial"))
        self.assertEqual([f["method"] for f in r.evidence["factors"]], ["reidemeister-reduction"] * 2)
        self.assertEqual(recognize(double, use_r3=False).evidence["factors"][0]["method"], "reduced-khovanov-F2-scan")
        # ... and of two unknot diagrams that survive Reidemeister I, II and the III search
        easy = [2, -1, 2, -3, -1, 3, -1, -2, -1, 1, 3, -2, 3]          # falls to two III moves in a row
        self.assertEqual([simplify(Diagram.from_braid(4, easy), r3_depth=k)[0].crossings for k in (1, 2)], [9, 0])
        tough = [-3, -2, 3, 3, 1, 2, -2, 2, -3, 1, 1, -2, -2, -2, -2, -1, 3, 2, 2]
        self.assertEqual(simplify(Diagram.from_braid(4, tough))[0].crossings, 9)
        double = Diagram.from_braid(7, tough + [g + 3 * (1 if g > 0 else -1) for g in tough])
        self.assertEqual(len(visible_factors(simplify(double, r3=False)[0])[0]), 2)     # what recognize factors
        r = recognize(double)
        self.assertEqual((r.status, r.method), ("UNKNOT", "connected-sum-all-factors-trivial"))
        self.assertEqual([f["method"] for f in r.evidence["factors"]], ["reduced-khovanov-F2-scan"] * 2)


class SimplifyTests(unittest.TestCase):
    def test_incremental_reduction(self):
        for d in random_knot_braids(25, 120, strands=(2, 3, 4, 5), lengths=(1, 12)):
            plain, plain_trace = simplify(d, r3=False)
            self.assertEqual(plain.crossings == 0, simplify_reference(d)[0].crossings == 0)
            self.assertTrue(all(m.kind in ("R1", "R2") for m in plain_trace))
            for reduced, trace in ((plain, plain_trace), simplify(d)):
                self.assertEqual(legal_moves(reduced), [])
                self.assertEqual(replay(d, trace).pd, reduced.pd)
                self.assertEqual(reduced.crossings,
                                 d.crossings - sum(len(m.crossings) for m in trace if m.kind != "R3"))
                self.assertEqual(alexander_polynomial(reduced), alexander_polynomial(d))
                self.assertLessEqual(reduced.crossings, plain.crossings)
        d = Diagram.from_braid(2, [1, 1, 1])
        with self.assertRaises(ValueError):
            replay(d, [{"kind": "R1", "crossings": [0]}])
        with self.assertRaises(ValueError):
            replay(d, [{"kind": "R3", "crossings": [0, 1, 2]}])          # a bigon chain has no triangle
        with self.assertRaises(ValueError):
            simplify(d, r3_depth=0)
        # the search is budgeted: no budget, the default and a tiny one agree where a sequence exists,
        # and a budget of zero trials is the plain I/II reduction
        for d in random_knot_braids(28, 60, strands=(4, 5), lengths=(12, 24)):
            self.assertEqual(simplify(d, r3_budget=None)[0].crossings, simplify(d)[0].crossings)
            self.assertEqual(simplify(d, r3_budget=0)[0].pd, simplify(d, r3=False)[0].pd)

    def test_reidemeister_three(self):
        from fastunknot.simplify import _Darts
        rng = random.Random(27)
        moves = 0
        for d in random_knot_braids(27, 150, strands=(3, 4, 5), lengths=(6, 16)):
            state = _Darts(d)
            triangles = [t for t in (state.triangle_at(x) for x in range(4 * d.crossings)) if t]
            if not triangles:
                continue
            triangle, before = rng.choice(triangles), None
            before = list(state.alpha)
            self.assertIsNotNone(state.apply_r3(triangle))
            moved = state.rebuild()                       # validates: one component, spherical
            moves += 1
            self.assertEqual(alexander_polynomial(moved), alexander_polynomial(d))
            self.assertEqual(moved.writhe(), d.writhe())
            self.assertEqual(khovanov_rank(moved.pd)["by_degree"], khovanov_rank(d.pd)["by_degree"])
            inverted = state.triangle_at(triangle[0] ^ 2)
            self.assertEqual(set(inverted), {x ^ 2 for x in triangle})
            state.apply_r3(inverted)
            self.assertEqual(state.alpha, before)         # the move is an involution
        self.assertGreater(moves, 60)
        # the 8-crossing example needs a Reidemeister III move; the helped reduction finds it
        self.assertEqual(simplify(load("hard_unknot_8.json"), r3=False)[0].crossings, 6)
        reduced, trace = simplify(load("hard_unknot_8.json"))
        self.assertEqual((reduced.crossings, sum(m.kind == "R3" for m in trace) > 0), (0, True))

    def test_long_chain(self):
        d = Diagram.from_braid(513, list(range(1, 513)))
        reduced, trace = simplify(d)
        self.assertEqual((reduced.crossings, len(trace)), (0, 512))

    def test_linear_descending_test(self):
        for d in random_knot_braids(26, 200, strands=(2, 3, 4), lengths=(1, 8)):
            self.assertEqual(descending_start(d) is None, descending_start_quadratic(d) is None)


if __name__ == "__main__":
    unittest.main()
