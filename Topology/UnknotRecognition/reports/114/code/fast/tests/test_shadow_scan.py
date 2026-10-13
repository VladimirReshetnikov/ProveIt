"""Independent cube, phase, prefix-provenance and resource checks for report 26."""
import copy
import itertools
import json
from pathlib import Path
import random
import subprocess
import sys
import unittest
from unittest.mock import patch

from fastunknot import Diagram, recognize
from fastunknot.component_scan import ComponentScan
from fastunknot.euler_scan import EulerBudget, euler_compressed_khovanov_decide
from fastunknot.geometry import ScanLimit
from fastunknot.scan_fast import FastScan
from fastunknot.shadow_scan import (ClosureShadow, _bareiss, component_shadow_bound,
                                   shadow_compressed_khovanov_decide)

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "reports/26"))
from detshadow.diagram import Diagram as ReferenceDiagram, complete_matching
from detshadow.continuation import observe_scan
from detshadow.cube import reduced_homology


def diagrams(count, seed):
    rng = random.Random(seed)
    accepted = 0
    while accepted < count:
        strands = rng.randrange(2, 5)
        word = [rng.choice((-1, 1)) * rng.randrange(1, strands)
                for _ in range(rng.randrange(1, 9))]
        try:
            diagram = Diagram.from_braid(strands, word)
        except ValueError:
            continue
        order = list(range(diagram.crossings))
        rng.shuffle(order)
        accepted += 1
        yield diagram, order


class ShadowTests(unittest.TestCase):
    def test_integer_determinant_against_permutation_expansion(self):
        rng = random.Random(2602)
        for n in range(6):
            for _ in range(10):
                matrix = [[rng.randrange(-3, 4) for _ in range(n)] for _ in range(n)]
                expected = 0
                for p in itertools.permutations(range(n)):
                    value = (-1) ** sum(p[i] > p[j] for i in range(n) for j in range(i + 1, n))
                    for i, j in enumerate(p):
                        value *= matrix[i][j]
                    expected += value
                self.assertEqual(_bareiss(copy.deepcopy(matrix), lambda amount: None), expected)

    def test_all_live_matching_phases_against_independent_cubes(self):
        comparisons = 0
        for diagram, order in diagrams(35, 2603):
            for diagram in (diagram, diagram.mirror()):
                engine = ClosureShadow(diagram.pd, order, max_states=None, max_work=None)
                scan = FastScan(shape_cache=False)
                for stage, index in enumerate(order):
                    suffix = [diagram.pd[i] for i in order[stage:]]
                    for matching in set(scan.mid) - {None}:
                        pairs = scan.algebra.pairs[matching]
                        completed = complete_matching(suffix, pairs)
                        poly = completed.cube_polynomial()
                        expected = tuple(sum(c for q, c in poly.items() if q % 4 == residue)
                                         for residue in range(4))
                        self.assertEqual(engine.evaluate(stage, pairs), expected)
                        self.assertEqual(engine.evaluate_one(stage, pairs), 2 * sum(expected))
                        comparisons += 1
                    scan.add_crossing(diagram.pd[index])
        self.assertGreater(comparisons, 500)

    def test_marked_bounds_and_saturation_against_full_homology(self):
        for diagram, order in diagrams(25, 2604):
            rank = reduced_homology(ReferenceDiagram(diagram.pd))["rank"]
            for kind in ("ordinary", "shared", "saturated"):
                scan = (FastScan(shape_cache=False) if kind == "ordinary" else
                        ComponentScan(shape_cache=False, rank_cap=3 if kind == "saturated" else None))
                engine = ClosureShadow(diagram.pd, order, max_states=None, max_work=None)
                previous = 0
                for stage, index in enumerate(order):
                    fields = (scan.mid, scan.deg, scan.out, scan.inc,
                              getattr(scan, "weights", None), getattr(scan, "owner", None))
                    before = copy.deepcopy(fields)
                    bound, _ = component_shadow_bound(scan, engine, stage,
                                                      cap=2 if kind == "saturated" else None)
                    self.assertEqual(fields, before)
                    reference = observe_scan(scan, [diagram.pd[i] for i in order[stage:]],
                                             marked_label=diagram.pd[order[-1]][0])
                    expected = reference["reduced_rank_lower_bound"]
                    self.assertEqual(bound, min(2, expected) if kind == "saturated" else expected)
                    self.assertLessEqual(previous, bound)
                    self.assertLessEqual(bound, rank)
                    previous = bound
                    scan.add_crossing(diagram.pd[index])
                    scan.check_d_squared()

    def test_determinant_one_knot_exposes_a_stronger_partial_bound(self):
        diagram = Diagram.from_braid(3, [1, 2] * 5)
        order = list(range(10))
        engine = ClosureShadow(diagram.pd, order)
        self.assertEqual(sum(map(abs, engine.evaluate(0, ()))), 1)
        scan = ComponentScan(shape_cache=False)
        for i in range(9):
            scan.add_crossing(diagram.pd[i])
        bound, _ = component_shadow_bound(scan, engine, 9, cap=None)
        self.assertEqual(bound, 7)
        result = shadow_compressed_khovanov_decide(diagram.pd, order=order, check_d_squared=True)
        self.assertEqual((result["status"], result["method"], result["stage"]),
                         ("KNOTTED", "marked-residue-four", 9))
        self.assertEqual(euler_compressed_khovanov_decide(diagram.pd, order=order)["stage"], 10)

    def test_queries_share_one_state_budget_and_cache(self):
        diagram = Diagram.from_braid(2, [1, 1, 1])
        engine = ClosureShadow(diagram.pd, [0, 1, 2], max_states=1)
        self.assertEqual(engine.evaluate_one(0, ()), -2)
        vector = engine.evaluate(0, ())
        self.assertEqual(engine.stats["states"], 1)
        before = engine.stats["work_units"]
        self.assertEqual(engine.evaluate(0, ()), vector)
        self.assertEqual(engine.stats["work_units"], before)
        scan = FastScan()
        scan.add_crossing(diagram.pd[0])
        pairs = scan.algebra.pairs[next(m for m in scan.mid if m is not None)]
        with self.assertRaises(EulerBudget):
            engine.evaluate(1, pairs)

    def test_interrupted_determinant_never_enters_the_cache(self):
        diagram = Diagram.from_braid(3, [1, 2] * 5)
        engine = ClosureShadow(diagram.pd, list(range(10)), max_work=None)

        def limited(matrix, tick):
            size = len(matrix)
            self.assertGreater(size, 2)
            engine.max_work = engine.stats["work_units"] + size + size - 1
            return _bareiss(matrix, tick)

        with patch("fastunknot.shadow_scan._bareiss", side_effect=limited), self.assertRaises(EulerBudget):
            engine.evaluate(0, ())
        self.assertNotIn((0, ()), engine.shadow_cache)
        engine.max_work = None
        self.assertEqual(sum(map(abs, engine.evaluate(0, ()))), 1)
        self.assertEqual(engine.stats["determinants"], 2)

    def test_local_exhaustion_continues_exact_scanning(self):
        for diagram, _ in diagrams(12, 2605):
            rank = reduced_homology(ReferenceDiagram(diagram.pd))["rank"]
            expected = "UNKNOT" if rank == 1 else "KNOTTED"
            for options in ({"shadow_max_work": 0}, {"euler_max_states": 0}):
                result = shadow_compressed_khovanov_decide(diagram.pd, **options)
                self.assertEqual(result["status"], expected)
                if "euler_max_states" in options:
                    self.assertEqual(result["method"], "closed-rank")
                    self.assertTrue(result["euler_exhausted"])
                else:
                    self.assertIn(result["method"], ("closed-rank", "component-euler"))
                self.assertTrue(result["shadow_exhausted"])

    def test_global_deadline_precedes_local_budget_even_on_cache_hit(self):
        diagram = Diagram.from_braid(2, [1, 1, 1])
        engine = ClosureShadow(diagram.pd, [0, 1, 2])
        engine.evaluate(0, ())
        engine.deadline, engine.max_work = 0, 0
        with self.assertRaises(ScanLimit):
            engine.evaluate(0, ())
        with self.assertRaises(ScanLimit):
            shadow_compressed_khovanov_decide(diagram.pd, seconds=0)
        self.assertEqual(recognize(diagram, backend="shadow", seconds=0).status, "UNKNOWN")

    def test_invalid_budgets_and_final_unmarked_observation_rejected(self):
        diagram = Diagram.from_braid(2, [1, 1, 1])
        for value in (-1, True, 1.5):
            with self.assertRaises(ValueError):
                recognize(Diagram.from_pd([]), shadow_max_work=value)
            with self.assertRaises(ValueError):
                ClosureShadow(diagram.pd, [0, 1, 2], max_work=value)
        engine = ClosureShadow(diagram.pd, [0, 1, 2])
        with self.assertRaises(ValueError):
            engine.evaluate(3, ())
        with self.assertRaises(ValueError):
            engine.evaluate(1, ())
        scan = ComponentScan(rank_cap=1)
        with self.assertRaises(ValueError):
            component_shadow_bound(scan, engine, 0)
        with self.assertRaises(ValueError):
            component_shadow_bound(scan, engine, 3)

    def test_recognizer_and_cli_route_to_marked_backend(self):
        path = Path(__file__).resolve().parents[1] / "examples/trefoil.json"
        args = [sys.executable, "-B", "-m", "fastunknot", "recognize", str(path),
                "--backend", "shadow", "--no-braid", "--no-seifert", "--no-reduction",
                "--no-descending", "--no-factor", "--no-alexander", "--no-modular", "--no-jones"]
        run = subprocess.run(args, capture_output=True, text=True, check=True)
        result = json.loads(run.stdout)
        self.assertEqual((result["status"], result["method"]), ("KNOTTED", "marked-residue-four-bound"))
        bad = subprocess.run(args + ["--shadow-max-work", "-1"], capture_output=True, text=True)
        self.assertEqual(bad.returncode, 2)
        self.assertNotIn("Traceback", bad.stderr)


if __name__ == "__main__":
    unittest.main()
