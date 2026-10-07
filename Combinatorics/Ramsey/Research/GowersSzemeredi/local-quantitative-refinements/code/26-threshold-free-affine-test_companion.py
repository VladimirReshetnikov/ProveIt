#!/usr/bin/env python3
"""Quick exact identities, bounded CLI, rejection and regression tests for Report 275."""
import importlib.util
from fractions import Fraction as Q
from pathlib import Path
import json
import subprocess
import sys
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "companion" / "exact_checks.py"
SPEC = importlib.util.spec_from_file_location("report275_exact", SCRIPT)
EXACT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(EXACT)


class ExactCompanionTests(unittest.TestCase):
    def command(self, *args, optimize=False):
        return subprocess.run([sys.executable, *(["-O"] if optimize else []), str(SCRIPT), *args],
                              capture_output=True, text=True, timeout=15, check=False)

    def test_least_prime_factor_and_centered_convention(self):
        self.assertEqual([EXACT.least_prime_factor(n) for n in range(2, 13)],
                         [2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2])
        self.assertEqual(EXACT.centered(3, 6), 3)
        self.assertEqual(EXACT.centered(-3, 6), 3)
        self.assertEqual(EXACT.centered(5, 6), -1)
        self.assertEqual(EXACT.centered(0, 1), 0)

    def test_prime_and_composite_unit_pair_bijections(self):
        for n,length in ((7, 7), (9, 3), (15, 3), (16, 2)):
            for j in range(length):
                for k in range(j+1, length):
                    counts = EXACT.pair_counts(n, length, j, k)
                    self.assertEqual(set(counts), {(x,y) for x in range(n) for y in range(n) if x != y})
                    self.assertEqual(set(counts.values()), {1})

    def test_direct_exact_variance_for_all_small_subsets(self):
        for n in range(2, 7):
            for length in range(1, EXACT.least_prime_factor(n)+1):
                for mask in range(1 << n):
                    selected = {x for x in range(n) if mask & (1 << x)}
                    delta = Q(len(selected), n)
                    moments = EXACT.ensemble_moments(n, selected, length)
                    expected = delta*(1-delta)*Q(n-length, length*(n-1))
                    self.assertEqual(moments["mean"], delta)
                    self.assertEqual(moments["variance"], expected)
                    self.assertEqual(moments["proper_copies"], n*(n-1))
                    self.assertLessEqual(expected, delta*(moments["maximum"]-delta))

    def test_composite_cap_is_material(self):
        row = EXACT.composite_cap_regression()
        self.assertEqual(row["actual_variance"], "11/108")
        self.assertEqual(row["incorrect_uncapped_formula"], "1/36")
        self.assertEqual(row["proper_copies"], 8)
        self.assertEqual(row["copies"], 12)
        self.assertTrue(any(x == y for x,y in EXACT.pair_counts(4, 3, 0, 2)))

    def test_all_step_moments_against_expanded_multisets(self):
        for n in range(2, 7):
            for length in range(1, n+1):
                for selected in (set(), {0}, set(range(0, n, 2)), set(range(n))):
                    row = EXACT.all_step_moments(n, selected, length)
                    values = tuple(Q(sum((a+j*d) % n in selected for j in range(length)), length)
                                   for a in range(n) for d in range(n))
                    mean = sum(values)/len(values)
                    variance = sum((value-mean)**2 for value in values)/len(values)
                    self.assertEqual(mean, Q(len(selected), n))
                    self.assertEqual(row["mean"], mean)
                    self.assertEqual(row["variance"], variance)
                    self.assertEqual(row["coset_variance"], variance)
                    self.assertGreaterEqual(variance, mean*(1-mean)/length)
                    self.assertEqual(row["good_mean"], mean)
                    if row["bad_steps"]:
                        self.assertEqual(row["bad_mean"], mean)
                    self.assertEqual(row, EXACT.all_step_moments(n, selected, length))

    def test_all_step_composite_covariance_and_empty_set_endpoint(self):
        row = EXACT.all_step_moments(4, {0, 2}, 3)
        self.assertEqual(row["variance"], Q(5, 36))
        self.assertGreater(row["variance"], Q(1, 12))
        self.assertEqual(row["good_variance"], Q(1, 36))
        self.assertEqual(row["bad_variance"], Q(1, 4))
        self.assertEqual(row["bad_fraction"], Q(1, 2))
        self.assertEqual(row["discard_gain_lower_bound"], Q(-1, 6))
        singleton_length = EXACT.all_step_moments(8, {0, 2}, 1)
        self.assertEqual(singleton_length["bad_steps"], 0)
        self.assertIsNone(singleton_length["bad_mean"])
        self.assertIsNone(singleton_length["bad_variance"])
        empty = EXACT.all_step_moments(8, set(), 2)
        self.assertEqual(empty["variance"], 0)
        self.assertIsNone(empty["discard_gain_lower_bound"])
        self.assertFalse(empty["simplified_gain_applies"])

    def test_bad_step_discard_and_cubic_scale_gain(self):
        for n,length in ((8, 2), (27, 3), (64, 4)):
            selected = set(range(0, n, 2))
            row = EXACT.all_step_moments(n, selected, length)
            bad = sum(len({j*d % n for j in range(length)}) < length for d in range(n))
            self.assertEqual(row["bad_steps"], bad)
            self.assertLessEqual(Q(bad, n), Q(length*(length-1), 2*n))
            self.assertTrue(row["simplified_gain_applies"])
            delta = Q(len(selected), n)
            self.assertGreaterEqual(row["maximum_proper_gain"], row["discard_gain_lower_bound"])
            self.assertGreaterEqual(row["discard_gain_lower_bound"], (1-delta)/(2*length))
        coverage = EXACT.all_step_checks(3)
        self.assertEqual(coverage["exhaustive_subset_length_instances"], 32)
        self.assertEqual(len(coverage["larger_selected_cases"]), 5)

    def test_dirichlet_all_small_increments(self):
        for n in range(1, 17):
            for increment in range(n):
                for bound in range(1, n+1):
                    q,epsilon = EXACT.dirichlet_step(n, increment, bound)
                    self.assertLessEqual(1, q)
                    self.assertLessEqual(q, bound)
                    self.assertLessEqual(abs(epsilon), Q(1, bound+1))
                    self.assertEqual((Q(q*increment, n)-epsilon).denominator, 1)
                    self.assertEqual((q,epsilon), EXACT.dirichlet_step(n, increment, bound))

    def test_residue_cell_partition_and_reduced_lifts(self):
        # Nonunit parent step, wraparound, affine offset, remainder chunks.
        parameters = (30, 29, 4, 15, 7, 11, 4)
        result = EXACT.phase_refinement(*parameters)
        n,start,step,size,coefficient,offset,length = parameters
        self.assertEqual(result, EXACT.phase_refinement(*parameters))
        indices = [j for cell in result["cells"] for j in cell["indices"]]
        self.assertEqual(sorted(indices), list(range(size)))
        for cell in result["cells"]:
            points = cell["points"]
            self.assertTrue(length <= len(points) <= 2*length-1)
            self.assertEqual(len(points), len(set(points)))
            self.assertLess(cell["radius_turns"], Q(length*length, size))
            initial = -Q(coefficient*points[0]+offset, n)
            for j,point in enumerate(points):
                actual = -Q(coefficient*point+offset, n)
                lift = initial-result["epsilon"]*j
                self.assertEqual((actual-lift).denominator, 1)
                self.assertLessEqual(abs(lift-cell["midpoint_turns"]), cell["radius_turns"])

    def test_phase_singleton_and_zero_step(self):
        result = EXACT.phase_refinement(12, 11, 0, 1, 7, 3, 1)
        self.assertEqual(result["epsilon"], 0)
        self.assertEqual(result["cells"][0]["points"], (11,))
        self.assertEqual(result["cells"][0]["radius_turns"], 0)
        trivial = EXACT.phase_refinement(1, 0, 0, 1, 0, 0, 1)
        self.assertEqual(trivial["cells"][0]["points"], (0,))

    def test_explicit_unreduced_midpoint_regression(self):
        row = EXACT.midpoint_regression()
        self.assertEqual(row["parent_points"], [0, 2])
        self.assertEqual(row["raw_increment_turns"], "1")
        self.assertEqual(row["reduced_increment_turns"], "0")
        self.assertEqual(row["reduced_midpoint_mod_one"], "0")
        self.assertEqual(row["unreduced_midpoint_mod_one"], "1/2")
        self.assertEqual(row["unreduced_chord_error"], 2)
        self.assertEqual(row["reduced_chord_error"], 0)

    def test_cover_absolute_mass_and_positive_extraction(self):
        result = EXACT.cover_mass_checks(6)
        self.assertEqual(result["all_A_subset_U_pairs"], sum(3**n for n in range(2, 7)))
        self.assertGreater(result["positive_mass_partitions"], 0)
        self.assertEqual(result["mu_identity"], "delta*(1+tau-2*delta)")
        self.assertEqual(result["normalized_signed_mass"], "delta*(1-tau)")
        # Separate transparent instance A={0,2}, U={0,1,2}, N=5.
        delta,tau = Q(2, 5),Q(3, 5)
        values = (1-delta, -delta, 1-delta)
        self.assertEqual(sum(map(abs, values))/5, delta*(1+tau-2*delta))
        self.assertEqual(sum(values)/5, delta*(1-tau))

    def test_integer_rectification_and_product_mass(self):
        result = EXACT.rectify_box(97, 31, ((96, 40), (5, 47)), Q(1))
        self.assertEqual(result["length"], 2)
        self.assertEqual(result["delta"], 4)
        self.assertLessEqual(result["loss_fraction"], 1)
        for axis in result["axes"]:
            points = [x for chunk in axis["chunks"] for x in chunk]
            self.assertEqual(len(points), len(set(points)))
            for chunk in axis["chunks"]:
                self.assertTrue(2 <= len(chunk) <= 3)
                self.assertTrue(all(y-x == 4 for x,y in zip(chunk, chunk[1:])))
        # A genuinely nonzero exceptional set, and exact half-budget case.
        loss = EXACT.rectify_box(41, 13, ((39, 20),), Q(1))
        self.assertEqual(loss["loss_fraction"], Q(1, 20))
        half = EXACT.rectify_box(257, 73, ((255, 160), (127, 150)), Q(1, 2))
        self.assertEqual(half["length"], 2)
        self.assertLessEqual(half["loss_fraction"], Q(1, 2))

    def test_rectification_singletons_and_negative_orientation(self):
        singleton = EXACT.rectify_box(1, 0, ((0, 1),), Q(1))
        self.assertEqual(singleton["length"], 1)
        self.assertEqual(singleton["delta"], 1)
        self.assertEqual(singleton["retained_mass"], 1)
        positive = EXACT.rectify_box(97, 66, ((3, 40), (82, 42)), Q(1))
        self.assertEqual(positive["delta"], 4)
        self.assertEqual(positive, EXACT.rectify_box(97, 66, ((3, 40), (82, 42)), Q(1)))

    def test_quick_run_is_repeatable_and_scoped(self):
        first = EXACT.run_checks(3)
        self.assertEqual(first, EXACT.run_checks(3))
        self.assertTrue(first["finite_diagnostics_not_proofs"])
        self.assertEqual(first["parameters"], {"nmax": 3, "full": False, "hard_nmax_cap": 12})
        self.assertEqual(first["variance"]["subset_length_instances"], 32)
        self.assertEqual(len(first["box_rectification"]["cases"]), 5)
        self.assertTrue(any("No Lean" in text for text in first["limitations"]))

    def test_cli_default_and_full_override(self):
        default = self.command()
        self.assertEqual(default.returncode, 0, default.stderr)
        parsed = json.loads(default.stdout)
        self.assertEqual(parsed["parameters"]["nmax"], 8)
        self.assertFalse(parsed["parameters"]["full"])
        full = self.command("--full", "--nmax", "2")
        self.assertEqual(full.returncode, 0, full.stderr)
        parsed = json.loads(full.stdout)
        self.assertEqual(parsed["parameters"]["nmax"], 2)
        self.assertTrue(parsed["parameters"]["full"])
        self.assertEqual(len(parsed["box_rectification"]["cases"]), 8)
        help_result = self.command("--help")
        self.assertEqual(help_result.returncode, 0)
        self.assertIn("--full", help_result.stdout)
        self.assertIn("--nmax", help_result.stdout)

    def test_cli_rejects_outside_caps_and_malformed_flags(self):
        for value in ("0", "1", "13", "999999999999999999", "1"*65,
                      "-1", "+2", "2.0", "٢", "true"):
            with self.subTest(value=value):
                result = self.command("--nmax", value)
                self.assertEqual(result.returncode, 2)
                self.assertEqual(result.stdout, "")
        for flags in (("--full=true",), ("--unknown",), ("--nmax",)):
            self.assertEqual(self.command(*flags).returncode, 2)

    def test_ascii_parser_and_boolean_rejections(self):
        self.assertEqual(EXACT.parse_integer("0"*63+"2", "nmax", 2, 12), 2)
        for value in ("", " 2", "2 ", "0"*65, None, 2, True):
            with self.assertRaises(ValueError):
                EXACT.parse_integer(value, "nmax", 2, 12)
        calls = ((EXACT.run_checks, (True,)), (EXACT.run_checks, (13,)),
                 (EXACT.run_checks, (2, 1)), (EXACT.box_checks, (1,)),
                 (EXACT.variance_checks, (13,)), (EXACT.cover_mass_checks, (10,)),
                 (EXACT.phase_checks, (13,)), (EXACT.all_step_checks, (13,)),
                 (EXACT.all_step_checks, (2, 1)), (EXACT.all_step_moments, (65, {0}, 2)),
                 (EXACT.all_step_moments, (8, {0}, 9)), (EXACT.least_prime_factor, (True,)),
                 (EXACT.least_prime_factor, (513,)), (EXACT.centered, (1.0, 2)),
                 (EXACT.centered, (2**100, 2)), (EXACT.pair_counts, (17, 2, 0, 1)),
                 (EXACT.pair_counts, (4, 2, 0, 0)), (EXACT.dirichlet_step, (5, 1, 513)),
                 (EXACT.dirichlet_step, (5, -1, 2)))
        for function,args in calls:
            with self.subTest(function=function.__name__, args=args):
                with self.assertRaises(ValueError):
                    function(*args)

    def test_subset_properness_and_exact_parameter_rejections(self):
        for selected in ({4}, {True}, [0, 0], "01", None):
            with self.assertRaises(ValueError):
                EXACT.ensemble_moments(4, selected, 2)
        for parameters in ((6, 0, 2, 4, 1, 0, 2), (6, 0, 0, 2, 1, 0, 1),
                           (6, 0, 1, 4, 6, 0, 2), (6, 0, 1, 4, 1, 0, 5),
                           (6, 0, 1, 4, 1, 0, True)):
            with self.assertRaises(ValueError):
                EXACT.phase_refinement(*parameters)
        for epsilon in (True, 0.5, 0, -1, 2, Q(1, 2**65)):
            with self.assertRaises(ValueError):
                EXACT.rectify_box(5, 1, ((0, 4),), epsilon)
        for axes in (None, (), ((0, 1),)*5, ((0,),), ((0, 6),), ((True, 1),)):
            with self.assertRaises(ValueError):
                EXACT.rectify_box(5, 1, axes, Q(1))
        with self.assertRaises(ValueError):
            EXACT.rectify_box(6, 2, ((0, 4),), Q(1))

    def test_explicit_checks_survive_optimization(self):
        with self.assertRaises(EXACT.CheckFailure):
            EXACT.ensure(False, "explicit diagnostic failure")
        normal = self.command("--nmax", "3")
        optimized = self.command("--nmax", "3", optimize=True)
        self.assertEqual(optimized.returncode, 0, optimized.stderr)
        self.assertEqual(normal.stdout, optimized.stdout)
        self.assertEqual(self.command("--nmax", "13", optimize=True).returncode, 2)
        self.assertNotIn("assert ", SCRIPT.read_text())


if __name__ == "__main__":
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(ExactCompanionTests)
    result = unittest.TextTestRunner(stream=sys.stderr, verbosity=1).run(suite)
    if not result.wasSuccessful():
        raise SystemExit(1)
    print(f"Report 275 companion regression tests passed: {result.testsRun}")
