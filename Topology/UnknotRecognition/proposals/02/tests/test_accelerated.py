"""Additional checks for the new algorithms, independent of method-name compatibility."""
from __future__ import annotations

from importlib.util import module_from_spec, spec_from_file_location
from itertools import combinations, product
import json
from pathlib import Path
import random
import sys
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from fastunknot import Diagram, recognize
from fastunknot.alexander import alexander_polynomial, evaluate
from fastunknot.filters import (PRIME, FilterLimit, determinant_residue, jones_evaluation,
                               oriented_writhe)
from fastunknot.scan import (ScanLimit, circles, compose, glue, inverse, khovanov_rank,
                            scan_order, best_scan_order)
from fastunknot.simplify import apply_move, descending_start, legal_moves, simplify
from test_legacy import reference_reduced_rank, one_component

spec = spec_from_file_location("baseline_fastunknot", ROOT / "baseline/fastunknot/__init__.py",
                              submodule_search_locations=[str(ROOT / "baseline/fastunknot")])
baseline = module_from_spec(spec)
sys.modules[spec.name] = baseline
spec.loader.exec_module(baseline)
from baseline_fastunknot import scan as old_scan
from baseline_fastunknot import simplify as old_simplify


def random_diagrams(count, seed=1903, max_length=10):
    rng = random.Random(seed)
    result = []
    while len(result) < count:
        strands = rng.randint(2, 5)
        length = rng.randint(strands - 1, max_length)
        word = [rng.choice((-1, 1)) * rng.randint(1, strands - 1) for _ in range(length)]
        if one_component(strands, word):
            result.append(Diagram.from_braid(strands, word))
    return result


def canonical_pd(diagram):
    labels = {}
    return tuple(tuple(labels.setdefault(x, len(labels)) for x in row) for row in diagram.pd)


def cube_bracket(diagram, value=2):
    """Independent full state sum: graph DFS, no scan/glue/pairing code."""
    n = diagram.crossings
    inverse = pow(value, -1, PRIME)
    delta = -(value * value + inverse * inverse) % PRIME
    if not n:
        return delta
    total = 0
    for state in range(1 << n):
        adjacency = [[] for _ in range(2 * n)]
        for i, (a, b, c, d) in enumerate(diagram.pd):
            pairs = ((a, d), (b, c)) if state >> i & 1 else ((a, b), (c, d))
            for x, y in pairs:
                adjacency[x].append(y)
                adjacency[y].append(x)
        seen = set()
        components = 0
        for start in range(2 * n):
            if start in seen:
                continue
            components += 1
            stack = [start]
            seen.add(start)
            while stack:
                for neighbor in adjacency[stack.pop()]:
                    if neighbor not in seen:
                        seen.add(neighbor)
                        stack.append(neighbor)
        total += pow(value, n - 2 * state.bit_count(), PRIME) * pow(delta, components, PRIME)
    return total % PRIME


def pairings(labels):
    if not labels:
        yield frozenset()
        return
    a, *rest = labels
    for b in rest:
        for tail in pairings([x for x in rest if x != b]):
            yield tail | {frozenset((a, b))}


class DifferentialTests(unittest.TestCase):
    def test_incremental_scan_orders_exactly_match_baseline(self):
        for d in random_diagrams(100, max_length=30):
            for start in range(d.crossings):
                self.assertEqual(scan_order(d.pd, start), old_scan.scan_order(d.pd, start))
            self.assertEqual(best_scan_order(d.pd, tries=12), old_scan.best_scan_order(d.pd, tries=12))

    def test_incremental_simplification_and_replay(self):
        for d in random_diagrams(250, seed=71, max_length=40):
            a, ta = simplify(d)
            b, tb = old_simplify.simplify(d)
            self.assertEqual([x.to_json() for x in ta], [x.to_json() for x in tb])
            self.assertEqual(canonical_pd(a), canonical_pd(b))
            replay = d
            for move in ta:
                replay = apply_move(replay, move)
            self.assertEqual(canonical_pd(a), canonical_pd(replay))

    def test_linear_descending_matches_bruteforce(self):
        for d in random_diagrams(300, seed=96, max_length=30):
            start = descending_start(d)
            self.assertEqual(start is None, old_simplify.descending_start(d) is None)
            if start is not None:
                alpha, seen, current = d.alpha(), set(), start
                for _ in range(2 * d.crossings):
                    if current // 4 not in seen:
                        self.assertEqual(current % 2, 1)
                        seen.add(current // 4)
                    current = alpha[4 * (current // 4) + (current + 2) % 4]

    def test_composition_plans_against_uncached_algebra(self):
        rng = random.Random(19)
        # A common cyclic boundary: only planar (noncrossing) matchings belong
        # to this cobordism category. Arbitrary pairings can be nonorientable.
        def planar(m):
            pairs = [tuple(sorted(p)) for p in m]
            return not any(a < c < b < d or c < a < d < b
                           for (a, b), (c, d) in combinations(pairs, 2))
        matchings = [m for m in pairings(list(range(6))) if planar(m)]
        self.assertEqual(len(matchings), 5)
        for _ in range(400):
            a, b, c = [rng.choice(matchings) for _ in range(3)]
            def morphism(x, y):
                keys = sorted(set(circles(x, y).values()), key=sorted)
                terms = [frozenset(keys[i] for i in range(len(keys)) if bits >> i & 1)
                         for bits in range(1 << len(keys))]
                return {term for term in terms if rng.randrange(2)}
            f, g = morphism(a, b), morphism(b, c)
            self.assertEqual(compose(f, g, a, b, c), old_scan.compose(f, g, a, b, c))

    def test_every_unit_in_three_arc_endomorphism_ring_is_self_inverse(self):
        m = frozenset(frozenset((2 * i, 2 * i + 1)) for i in range(3))
        keys = sorted(m, key=sorted)
        terms = [frozenset(keys[i] for i in range(3) if bits >> i & 1) for bits in range(8)]
        for mask in range(128):
            f = {frozenset()} | {terms[i + 1] for i in range(7) if mask >> i & 1}
            self.assertEqual(inverse(f, m), f)
            self.assertEqual(compose(f, f, m, m, m), {frozenset()})
            self.assertEqual(old_scan.compose(f, f, m, m, m), {frozenset()})


class FilterTests(unittest.TestCase):
    def test_jones_matches_independent_cube(self):
        rng = random.Random(17)
        for d in random_diagrams(100, seed=25, max_length=9):
            for value in (2, 3):
                order = list(range(d.crossings))
                rng.shuffle(order)
                result = jones_evaluation(d, value=value, order=order)
                self.assertEqual(result["bracket"], cube_bracket(d, value))
                self.assertEqual(result["bracket"], jones_evaluation(d, value=value)["bracket"])

    def test_modular_determinant_matches_symbolic(self):
        for d in random_diagrams(120, seed=18, max_length=14):
            residue = determinant_residue(d)["residue"]
            value = evaluate(alexander_polynomial(d), -1) % PRIME
            self.assertIn(residue, (value, -value % PRIME))

    def test_writhe_is_invariant_under_half_rotations(self):
        rng = random.Random(55)
        for d in random_diagrams(80, seed=5, max_length=14):
            pd = [row[2:] + row[:2] if rng.randrange(2) else row for row in d.pd]
            changed = Diagram.from_pd(pd)
            self.assertEqual(oriented_writhe(d), oriented_writhe(changed))
            self.assertEqual(oriented_writhe(d.mirror()), -oriented_writhe(d))
            self.assertEqual(jones_evaluation(d)["bracket"], jones_evaluation(changed)["bracket"])
            self.assertEqual(jones_evaluation(d.mirror())["bracket"],
                             jones_evaluation(d, value=pow(2, -1, PRIME))["bracket"])

    def test_normalized_jones_is_preserved_by_reidemeister_moves(self):
        def normalized(d):
            r = jones_evaluation(d)
            return r["bracket"] * pow(-8, -r["writhe"], PRIME) % PRIME
        for d in random_diagrams(80, seed=217, max_length=12):
            value = normalized(d)
            for move in legal_moves(d):
                self.assertEqual(normalized(apply_move(d, move)), value)

    def test_conjugated_stabilized_unknots_are_not_rejected(self):
        rng = random.Random(142)
        for _ in range(60):
            strands = rng.randint(2, 6)
            word = [rng.choice((-1, 1)) * i for i in range(1, strands)]
            conjugator = [rng.choice((-1, 1)) * rng.randint(1, strands - 1)
                          for _ in range(rng.randint(0, 10))]
            word = conjugator + word + [-g for g in reversed(conjugator)]
            d = Diagram.from_braid(strands, word)
            self.assertFalse(jones_evaluation(d)["obstructs"])
            self.assertEqual(recognize(d).status, "UNKNOT")

    def test_named_examples(self):
        unknots = {"unknot", "unknot_braid40", "grid_scrambled_unknot", "hard_unknot_8"}
        for path in (ROOT / "examples").glob("*.json"):
            d = Diagram.from_json(json.loads(path.read_text()))
            self.assertEqual(jones_evaluation(d)["obstructs"], path.stem not in unknots)
            r = recognize(d)
            self.assertEqual(r.status, "UNKNOT" if path.stem in unknots else "KNOTTED")
            if path.stem in {"conway", "kinoshita_terasaka"}:
                self.assertEqual(r.method, "modular-jones")

    def test_collision_cannot_create_an_unknot_verdict(self):
        d = Diagram.from_braid(2, [1, 1, 1])
        with patch("fastunknot.recognize.determinant_residue", return_value={"obstructs": False}), \
             patch("fastunknot.recognize.jones_evaluation", return_value={"obstructs": False}):
            result = recognize(d, use_alexander=False)
        self.assertEqual((result.status, result.method), ("KNOTTED", "reduced-khovanov-F2-scan"))


class ExhaustiveTests(unittest.TestCase):
    def test_all_three_braid_words_through_length_four(self):
        count = 0
        for length in (2, 4):
            for word in product((-2, -1, 1, 2), repeat=length):
                if not one_component(3, word):
                    continue
                d = Diagram.from_braid(3, word)
                rank = reference_reduced_rank(d)
                self.assertEqual(khovanov_rank(d.pd, check_d_squared=True)["reduced_rank"], rank)
                self.assertEqual(recognize(d).is_unknot, rank == 1)
                self.assertEqual(jones_evaluation(d)["bracket"], cube_bracket(d))
                count += 1
        self.assertEqual(count, 168)

    def test_random_ranks_with_independent_dense_cube(self):
        for d in random_diagrams(100, seed=3008, max_length=9):
            rank = reference_reduced_rank(d)
            self.assertEqual(khovanov_rank(d.pd, check_d_squared=True)["reduced_rank"], rank)
            self.assertEqual(recognize(d).is_unknot, rank == 1)


class ResourceTests(unittest.TestCase):
    def test_bad_orders_are_rejected(self):
        d = Diagram.from_braid(2, [1, 1, 1])
        for order in ([], [0, 1], [0, 1, 1], [0, 1, 3], [False, 1, 2]):
            with self.assertRaises(ValueError):
                khovanov_rank(d.pd, order=order)
            with self.assertRaises(ValueError):
                jones_evaluation(d, order=order)

    def test_invalid_budgets(self):
        d = Diagram.from_braid(2, [1])
        for seconds in (-1, float('nan'), float('inf')):
            with self.assertRaises(ValueError):
                recognize(d, seconds=seconds)
            with self.assertRaises(ValueError):
                khovanov_rank(d.pd, seconds=seconds)
        for cap in (-1, 0, 1.5, True):
            with self.assertRaises(ValueError):
                recognize(d, max_objects=cap)

    def test_filter_work_limit_and_global_limit_are_distinct(self):
        d = Diagram.from_json(json.loads((ROOT / "examples/conway.json").read_text()))
        with self.assertRaises(FilterLimit):
            jones_evaluation(d, max_transitions=1)
        r = recognize(d, jones_max_transitions=1)
        self.assertEqual((r.status, r.method), ("KNOTTED", "reduced-khovanov-F2-scan"))
        self.assertIn("jones_skipped", r.evidence)
        self.assertEqual(recognize(d, jones_max_transitions=1, max_objects=1).status, "UNKNOWN")
        self.assertEqual(recognize(d, seconds=0).status, "UNKNOWN")
        self.assertEqual(recognize(d, max_objects=1).status, "KNOTTED")

    def test_scan_caches_do_not_accumulate_across_requests(self):
        d = Diagram.from_braid(2, [1, 1, 1])
        khovanov_rank(d.pd)
        self.assertEqual(glue.cache_info().currsize, 0)
        self.assertEqual(circles.cache_info().currsize, 0)
        with self.assertRaises(ScanLimit):
            khovanov_rank(d.pd, max_objects=1)
        self.assertEqual(glue.cache_info().currsize, 0)
        self.assertEqual(circles.cache_info().currsize, 0)


if __name__ == "__main__":
    unittest.main()
