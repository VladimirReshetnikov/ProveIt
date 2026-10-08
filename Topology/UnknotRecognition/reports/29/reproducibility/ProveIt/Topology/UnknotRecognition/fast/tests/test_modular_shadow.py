"""Independent integer/cube checks and resource contracts for modular shadows."""
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
from fastunknot.euler_scan import EulerBudget
from fastunknot.geometry import ScanLimit
from fastunknot.modular_lattice import (balanced, crt_vector, minimum_l1_lift,
                                       threshold_is_exact, validate_primes)
from fastunknot.modular_shadow import (ModularClosureShadow,
    component_modular_shadow_bound, modular_shadow_khovanov_decide)
from fastunknot.scan_fast import FastScan
from fastunknot.shadow_scan import (ClosureShadow, ShadowWorkBudget,
                                    component_shadow_bound)


def small_diagrams(count=20, seed=811031):
    rng = random.Random(seed)
    produced = 0
    while produced < count:
        strands = rng.randrange(2, 5)
        word = [rng.choice((-1, 1)) * rng.randrange(1, strands)
                for _ in range(rng.randrange(1, 10))]
        try:
            diagram = Diagram.from_braid(strands, word)
        except ValueError:
            continue
        order = list(range(diagram.crossings))
        rng.shuffle(order)
        produced += 1
        yield diagram, order


class LatticeTests(unittest.TestCase):
    def test_sum_constrained_minimum_against_exhaustive_integer_lifts(self):
        for modulus in (3, 5, 7):
            for residues in itertools.product(range(modulus), repeat=2):
                for total in range(-10, 11):
                    if (total - sum(residues)) % modulus:
                        continue
                    expected = min(abs(x) + abs(total - x)
                        for x in range(-30, 31)
                        if x % modulus == residues[0]
                        and (total - x) % modulus == residues[1])
                    actual, lift = minimum_l1_lift(residues, modulus, total)
                    self.assertEqual(actual, expected)
                    self.assertEqual(sum(lift), total)
                    self.assertEqual(tuple(x % modulus for x in lift), residues)

    def test_four_coordinate_lifts_and_monotonicity(self):
        rng = random.Random(812301)
        for _ in range(150):
            x = [rng.randrange(-20, 21) for _ in range(4)]
            previous = 0
            for modulus in (3, 15, 105):
                lower, lift = minimum_l1_lift(x, modulus, sum(x))
                self.assertLessEqual(previous, lower)
                self.assertLessEqual(lower, sum(map(abs, x)))
                self.assertEqual(sum(lift), sum(x))
                previous = lower
            self.assertEqual(previous, sum(map(abs, x)))
        # A mixed-direction choice cannot improve the exact sum-constrained
        # minimizer. Exhaust all candidate lifts for a nontrivial 4-vector.
        for residues in itertools.product(range(3), repeat=4):
            for total in (-3, 0, 3):
                if (total - sum(residues)) % 3:
                    continue
                expected = min(sum(abs(r + 3 * z) for r, z in zip(residues, shifts))
                    for shifts in itertools.product(range(-2, 3), repeat=4)
                    if sum(r + 3 * z for r, z in zip(residues, shifts)) == total)
                self.assertEqual(minimum_l1_lift(residues, 3, total)[0], expected)

    def test_crt_exposes_aliases_and_threshold_bound_is_sharp(self):
        self.assertEqual(crt_vector((0, 0), 3, (1, 4), 5), (6, 9))
        # x and -x are invisible modulo each divisor of x; neither zero is
        # an integer-zero certificate, despite the exactly known sum zero.
        true = (15, -15, 0, 0)
        self.assertEqual(minimum_l1_lift(true, 15, 0)[0], 0)
        self.assertFalse(threshold_is_exact(15, [15], [1]))
        self.assertTrue(threshold_is_exact(17, [15], [1]))
        self.assertGreater(minimum_l1_lift(true, 17, 0)[0], 1)
        for bound in range(1, 7):
            modulus = 2 * ((bound + 1) // 2) + 1
            for vector in itertools.product(range(-bound, bound + 1), repeat=2):
                lower, _ = minimum_l1_lift(vector, modulus, sum(vector))
                self.assertEqual(lower > 1, sum(map(abs, vector)) > 1)
        # Exact-sum information can strengthen general higher-threshold
        # bounds; threshold-one recognition uses it chiefly for termination.
        self.assertEqual(minimum_l1_lift((1, 1), 3)[0], 2)
        self.assertEqual(minimum_l1_lift((1, 1), 3, 5)[0], 5)

    def test_invalid_lattice_inputs_and_composite_primes(self):
        for values in ((), (3, 3), (2,), (9,), (True,), (1 << 31,), (65521, 21)):
            with self.assertRaises(ValueError):
                validate_primes(values)
        for modulus in (0, 2, 4):
            with self.assertRaises(ValueError):
                balanced(1, modulus)
        with self.assertRaises(ValueError):
            minimum_l1_lift((0, 0), 3, 1)


class ModularShadowTests(unittest.TestCase):
    def test_actual_prefix_vectors_equal_integer_completions_modulo_each_prime(self):
        count = 0
        for diagram, order in small_diagrams(24):
            for diagram in (diagram, diagram.mirror()):
                exact = ClosureShadow(diagram.pd, order, max_states=None, max_work=None)
                modular = ModularClosureShadow(diagram.pd, order, primes=(3, 5, 65521),
                                                max_states=None, max_work=None)
                scan = FastScan(shape_cache=False)
                for stage, index in enumerate(order):
                    for matching in set(scan.mid) - {None}:
                        pairs = scan.algebra.pairs[matching]
                        value = exact.evaluate(stage, pairs)
                        for prime in modular.primes:
                            self.assertEqual(modular.evaluate(stage, pairs, prime),
                                             tuple(x % prime for x in value))
                            count += 1
                    scan.add_crossing(diagram.pd[index])
        self.assertGreater(count, 700)

    def test_component_bounds_below_exact_and_equal_when_threshold_completed(self):
        for diagram, order in small_diagrams(18, 811044):
            scan = ComponentScan(shape_cache=False, rank_cap=3)
            exact = ClosureShadow(diagram.pd, order, max_states=None, max_work=None)
            modular = ModularClosureShadow(diagram.pd, order, primes=(3, 5, 7, 11, 13),
                                            max_states=None, max_work=None)
            for stage, index in enumerate(order):
                before = copy.deepcopy((scan.mid, scan.deg, scan.out, scan.inc,
                                        scan.weights, scan.owner))
                expected, _ = component_shadow_bound(scan, exact, stage)
                lower, records = component_modular_shadow_bound(scan, modular, stage)
                self.assertLessEqual(lower, expected)
                if modular.last_observation["threshold_exact"]:
                    self.assertEqual(lower, expected)
                for record in records:
                    self.assertEqual(sum(record["minimum_lift"]), record["exact_euler"])
                self.assertEqual(before, (scan.mid, scan.deg, scan.out, scan.inc,
                                           scan.weights, scan.owner))
                scan.add_crossing(diagram.pd[index])
                scan.check_d_squared()

    def test_determinant_one_knot_and_final_rank(self):
        diagram = Diagram.from_braid(3, [1, 2] * 5)
        result = modular_shadow_khovanov_decide(diagram.pd, order=list(range(10)),
                                               shadow_max_work=None)
        self.assertEqual((result["status"], result["method"], result["stage"]),
                         ("KNOTTED", "marked-residue-four-modular", 9))
        unknot = Diagram.from_braid(3, [1, 2])
        result = modular_shadow_khovanov_decide(unknot.pd)
        self.assertEqual((result["status"], result["method"]), ("UNKNOT", "closed-rank"))

    def test_interrupted_kernel_does_not_publish_partial_state(self):
        diagram = Diagram.from_braid(3, [1, 2] * 5)
        engine = ModularClosureShadow(diagram.pd, list(range(10)), max_work=None)
        from fastunknot.modular_response import ModularTerminalKernel
        original = ModularTerminalKernel.build

        def interrupted(*args, **kwargs):
            engine.max_work = engine.stats["work_units"] + 12
            return original(*args, **kwargs)

        with patch.object(ModularTerminalKernel, "build", side_effect=interrupted):
            with self.assertRaises(ShadowWorkBudget):
                engine.evaluate(0, ())
        self.assertFalse(engine.kernels)
        self.assertFalse(engine.shadow_cache)
        engine.max_work = None
        expected = ClosureShadow(diagram.pd, list(range(10))).evaluate(0, ())
        self.assertEqual(engine.evaluate(0, ()), tuple(x % 65521 for x in expected))

    def test_budget_cache_and_global_deadline(self):
        diagram = Diagram.from_braid(2, [1, 1, 1])
        engine = ModularClosureShadow(diagram.pd, [0, 1, 2], max_states=1, max_work=None)
        value = engine.evaluate(0, ())
        before = engine.stats["work_units"]
        self.assertEqual(engine.evaluate(0, ()), value)
        self.assertEqual(engine.stats["work_units"], before)
        scan = FastScan()
        scan.add_crossing(diagram.pd[0])
        pairs = scan.algebra.pairs[next(m for m in scan.mid if m is not None)]
        with self.assertRaises(EulerBudget):
            engine.evaluate(1, pairs)
        engine.deadline, engine.max_work = 0, 0
        with self.assertRaises(ScanLimit):
            engine.evaluate(0, ())
        self.assertEqual(recognize(diagram, backend="shadow-modular", seconds=0).status,
                         "UNKNOWN")
        for budget in ({"shadow_max_work": 0}, {"euler_max_states": 0}):
            out = modular_shadow_khovanov_decide(diagram.pd, **budget)
            self.assertEqual(out["status"], "KNOTTED")
            self.assertTrue(out["shadow_exhausted"])
            self.assertNotEqual(out["method"], "marked-residue-four-modular")

    def test_geometry_decline_falls_back_without_false_verdict(self):
        from fastunknot.boundary_tait import BoundaryDeclined, BoundaryTait
        diagram = Diagram.from_braid(3, [1, 2])
        with patch.object(BoundaryTait, "partition", side_effect=BoundaryDeclined("test decline")):
            out = modular_shadow_khovanov_decide(diagram.pd)
        self.assertEqual((out["status"], out["method"]), ("UNKNOT", "closed-rank"))
        self.assertEqual(out["shadow_stats"]["boundary_declines"], 1)

    def test_cli_and_invalid_options(self):
        path = Path(__file__).resolve().parents[1] / "examples/trefoil.json"
        args = [sys.executable, "-B", "-m", "fastunknot", "recognize", str(path),
                "--backend", "shadow-modular", "--no-braid", "--no-seifert", "--no-reduction",
                "--no-descending", "--no-factor", "--no-alexander", "--no-modular", "--no-jones"]
        run = subprocess.run(args, capture_output=True, text=True, check=True)
        out = json.loads(run.stdout)
        self.assertEqual((out["status"], out["method"]),
                         ("KNOTTED", "marked-residue-four-modular-bound"))
        bad = subprocess.run(args + ["--shadow-primes", "9"], capture_output=True, text=True)
        self.assertEqual(bad.returncode, 2)
        self.assertNotIn("Traceback", bad.stderr)


if __name__ == "__main__":
    unittest.main()
