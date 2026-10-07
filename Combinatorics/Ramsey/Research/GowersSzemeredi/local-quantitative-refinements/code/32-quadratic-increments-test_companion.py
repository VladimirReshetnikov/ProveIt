"""Runtime, exactness, boundary and regression tests for the Report 276 companion.

Run with: python -m unittest discover -s tests -v
Also run under python -O. No third-party package is required.
"""
from __future__ import annotations

import ast
from fractions import Fraction as Q
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import unittest

sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parents[1]
COMPANION = ROOT / "companion" / "exact_checks.py"
SPEC = importlib.util.spec_from_file_location("report276_exact_checks", COMPANION)
e = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(e)


class ExactStructureTests(unittest.TestCase):
    def test_centered_tie_and_periodicity(self):
        self.assertEqual(e.centered(3, 6), 3)
        self.assertEqual(e.centered(-3, 6), 3)
        self.assertEqual(e.centered(11, 6), -1)
        self.assertEqual(e.centered(10**20+1, 5), 1)

    def test_dirichlet_step_is_reduced(self):
        q, epsilon = e.dirichlet_step(6, 3, 2)
        self.assertEqual((q, epsilon), (2, Q(0)))
        q, epsilon = e.dirichlet_step(7, 5, 3)
        self.assertLessEqual(abs(epsilon), Q(1, 4))
        self.assertEqual((Q(5*q, 7)-epsilon).denominator, 1)

    def test_affine_wrapping_nonunit_parent(self):
        result = e.phase_refinement(12, 11, 4, 3, 5, 7, 2)
        points = [x for cell in result["cells"] for x in cell["points"]]
        self.assertCountEqual(points, (11, 3, 7))
        self.assertTrue(all(2 <= len(cell["points"]) <= 3 for cell in result["cells"]))
        self.assertTrue(all(type(cell["radius_turns"]) is Q for cell in result["cells"]))

    def test_midpoint_regression(self):
        result = e.midpoint_regression()
        self.assertEqual(result["reduced_midpoint_mod_one"], "0")
        self.assertEqual(result["unreduced_midpoint_mod_one"], "1/2")
        self.assertEqual(result["unreduced_chord_error"], 2)
        self.assertEqual(result["reduced_chord_error"], 0)

    def test_quadratic_differencing_formal_histogram(self):
        result = e.quadratic_difference_counts(4, 1, 4)
        self.assertEqual(result["direct_counts"], (8, 4, 0, 4))
        self.assertEqual(result["difference_counts"], result["direct_counts"])
        self.assertEqual(result["ordered_pairs"], 16)
        self.assertEqual(e.quadratic_difference_counts(1, 0, 64)["direct_counts"], (4096,))

    def test_quadratic_restriction_integer_curvature(self):
        result = e.quadratic_refinement(6, 0, 2, 3, 3, 0, 0, 1, 3, 3)
        self.assertEqual(result["raw_quadratic_coefficient"], 2)
        self.assertEqual(result["quadratic_epsilon"], 0)
        self.assertEqual(result["maximum_radius_turns"], 0)
        self.assertEqual(result["cells"][0]["points"], (0, 2, 4))

    def test_quadratic_negative_reduced_curvature(self):
        result = e.quadratic_refinement(7, 6, 1, 7, 6, 4, 5, 1, 3, 2)
        self.assertEqual(result["quadratic_epsilon"], Q(-1, 7))
        indices = [j for cell in result["cells"] for j in cell["indices"]]
        self.assertEqual(sorted(indices), list(range(7)))
        self.assertTrue(all(len(cell["points"]) == len(set(cell["points"]))
                            for cell in result["cells"]))

    def test_quadratic_selected_toy_is_exact(self):
        result = e.quadratic_refinement(128, 127, 1, 128, 2, 0, 0, 8, 8, 2)
        self.assertEqual(result["maximum_radius_turns"], 0)
        self.assertEqual(sum(len(cell["points"]) for cell in result["cells"]), 128)
        self.assertTrue(all(len(cell["points"]) >= 2 for cell in result["cells"]))

    def test_quadratic_singleton_degenerate_step(self):
        result = e.quadratic_refinement(1, 0, 0, 1, 0, 0, 0, 1, 1, 1)
        self.assertEqual(result["cells"][0]["points"], (0,))
        self.assertEqual(result["maximum_radius_turns"], 0)

    def test_curvature_regression(self):
        result = e.curvature_regression()
        self.assertEqual(result["unreduced_lift_radius_turns"], "8")
        self.assertEqual(result["reduced_lift_radius_turns"], "0")

    def test_all_moduli_coset_covariance(self):
        nonunit = e.coset_pair_moment(4, {0, 2}, 2)
        self.assertEqual(nonunit["pair_expectation"], Q(1, 2))
        self.assertEqual(nonunit["covariance"], Q(1, 4))
        self.assertEqual(nonunit["coset_subset_counts"], (2, 0))
        unit = e.coset_pair_moment(4, {0, 2}, 1)
        self.assertEqual(unit["pair_expectation"], Q(1, 4))
        self.assertEqual(unit["covariance"], 0)

    def test_all_step_moments_include_zero_and_repeated_points(self):
        result = e.all_step_moments(4, {0, 2}, 3)
        self.assertEqual(result["variance"], Q(5, 36))
        self.assertEqual(result["coset_variance"], Q(5, 36))
        self.assertEqual(result["good_steps"], 2)
        self.assertEqual(result["bad_steps"], 2)
        self.assertEqual(result["bad_variance"], Q(1, 4))
        self.assertEqual(result["maximum_proper_gain"], Q(1, 6))
        self.assertFalse(result["simplified_gain_applies"])

    def test_singleton_length_has_no_bad_steps(self):
        result = e.all_step_moments(4, {0, 2}, 1)
        self.assertEqual(result["bad_steps"], 0)
        self.assertIsNone(result["bad_variance"])
        self.assertIsNone(result["bad_mean"])
        self.assertEqual(result["variance"], Q(1, 4))

    def test_empty_subset_moments(self):
        result = e.all_step_moments(8, set(), 2)
        self.assertEqual(result["mean"], 0)
        self.assertEqual(result["variance"], 0)
        self.assertIsNone(result["discard_gain_lower_bound"])
        self.assertFalse(result["simplified_gain_applies"])

    def test_simplified_variance_gain_boundary(self):
        result = e.all_step_moments(8, {0, 4}, 2)
        self.assertTrue(result["simplified_gain_applies"])
        self.assertLess(result["bad_fraction"], Q(1, 4))
        self.assertGreaterEqual(result["maximum_proper_gain"], Q(3, 16))
        self.assertEqual(result["good_mean"], Q(1, 4))
        self.assertEqual(result["bad_mean"], Q(1, 4))

    def test_strict_recurrence_boundary(self):
        result = e.recurrence_witness(2, 1, 2)
        self.assertEqual(result["p"], 2)
        self.assertEqual(result["norm"], 0)
        self.assertEqual(result["unconditional_bound"], 1024*2**5)

    def test_recurrence_largest_allowed_rational_denominator(self):
        result = e.recurrence_witness(512, 511, 4096)
        self.assertLessEqual(result["p"], 512)
        self.assertLess(result["norm"], Q(1, 4096))

    def test_budget_identities_without_enumeration(self):
        result = e.budget_constants(2, 2)
        self.assertEqual(result["minimum_parent_size"], 2**154)
        self.assertEqual(result["minimum_parent_size"], result["T"]*result["H"])
        self.assertEqual(result["R"], 2**20*2**7)
        self.assertEqual(result["curvature_radius_majorant_turns"], Q(1, 128))
        self.assertLess(result["combined_chord_majorant_using_pi_lt_22_over_7"], Q(1, 8))
        self.assertLess(result["maximum_conditional_contradiction_p"], result["unconditional_recurrence_T"])

    def test_exact_root_ceiling_boundaries(self):
        for k in (1, 2, 17, 4096):
            for m in (1, 7):
                boundary = m*(17*k)**39
                self.assertEqual(e.target_length(boundary-1, m), k)
                self.assertEqual(e.target_length(boundary, m), k)
                self.assertEqual(e.target_length(boundary+1, m), k+1)
        self.assertEqual(e.target_length(1, 1), 1)

    def test_largest_ratio_input_cap(self):
        n = 2**1024-1
        length = e.target_length(n, 1)
        self.assertGreaterEqual((17*length)**39, n)
        self.assertLess((17*(length-1))**39, n)

    def test_finite_cover_mass_count(self):
        result = e.cover_mass_checks(4)
        self.assertEqual(result["all_A_subset_U_pairs"], 3**2+3**3+3**4)

    def test_finite_pair_and_kernel_counts(self):
        result = e.coset_and_bad_step_checks(4)
        self.assertEqual(result["all_subset_difference_cases"], 4+16+48)
        self.assertEqual(result["kernel_size_cases"], 1+2+3)
        self.assertEqual(result["bad_direction_length_cases"], 2+3+4)


class GuardrailTests(unittest.TestCase):
    def test_implementation_contains_no_assert_or_float_literal(self):
        tree = ast.parse(COMPANION.read_text(encoding="utf-8"))
        self.assertFalse(any(isinstance(node, ast.Assert) for node in ast.walk(tree)))
        self.assertFalse(any(isinstance(node, ast.Constant) and isinstance(node.value, (float, complex))
                             for node in ast.walk(tree)))

    def test_explicit_failure_is_runtime_exception(self):
        with self.assertRaises(e.CheckFailure):
            e._ensure(False, "sentinel")

    def test_invalid_public_inputs(self):
        cases = (
            (e.centered, (0, 0)), (e.centered, (True, 4)),
            (e.centered, (2**128, 4)),
            (e.dirichlet_step, (5, 1, 0)), (e.dirichlet_step, (513, 1, 1)),
            (e.phase_refinement, (6, 0, 2, 4, 1, 0, 1)),
            (e.phase_refinement, (6, 0, 1, 6, 1, 0, 0)),
            (e.quadratic_refinement, (6, 0, 2, 4, 1, 0, 0, 1, 2, 2)),
            (e.quadratic_refinement, (6, 0, 1, 6, 1, 0, 0, 4, 2, 2)),
            (e.quadratic_refinement, (6, 0, 1, 6, 1, 0, 0, 1, 1, 2)),
            (e.quadratic_refinement, (6, 0, 1, 6, 6, 0, 0, 1, 2, 2)),
            (e.all_step_moments, (65, {0}, 2)),
            (e.all_step_moments, (4, [0, 0], 2)),
            (e.all_step_moments, (4, {True}, 2)),
            (e.all_step_moments, (4, {4}, 2)),
            (e.all_step_moments, (4, (x for x in (0, 1)), 2)),
            (e.quadratic_difference_counts, (4, 1, 65)),
            (e.quadratic_difference_counts, (513, 1, 1)),
            (e.coset_pair_moment, (4, {0}, 0)),
            (e.coset_pair_moment, (4, {0}, 4)),
            (e.recurrence_witness, (513, 1, 2)),
            (e.recurrence_witness, (7, 7, 2)),
            (e.recurrence_witness, (7, 1, 1)),
            (e.budget_constants, (1,)), (e.budget_constants, (4097,)),
            (e.budget_constants, (2, True)),
            (e.target_length, (2**1024, 1)), (e.target_length, (1, 2)),
            (e.target_length, (1.0, 1)), (e.target_length, (True, 1)),
            (e.run_checks, (13,)), (e.run_checks, (2, 1)),
            (e.cover_mass_checks, (10,)), (e.all_step_checks, (2, 1)),
            (e.quadratic_checks, (13,)), (e.recurrence_checks, (13,)),
            (e.assembly_checks, (13,)), (e.coset_and_bad_step_checks, (13,)),
        )
        for function, args in cases:
            with self.subTest(function=function.__name__, arguments=str(args)):
                with self.assertRaises(ValueError):
                    function(*args)

    def test_ascii_and_digit_parse_guards(self):
        for value in ("", "１２", "-1", "+2", " 2", "2.0", "1"*65, "9999"):
            with self.subTest(value=value):
                with self.assertRaises(ValueError):
                    e._parse_integer(value, "nmax", 2, 12)
        self.assertEqual(e._parse_integer("0008", "nmax", 2, 12), 8)

    def test_cli_argument_collection_bound(self):
        with self.assertRaises(ValueError):
            e.main(["--full"]*4)
        with self.assertRaises(ValueError):
            e.main(["1"*65])
        with self.assertRaises(ValueError):
            e.main("--full")

    def test_normal_and_optimized_json_match(self):
        normal = subprocess.run([sys.executable, str(COMPANION), "--nmax", "2"],
                                check=True, capture_output=True, text=True, timeout=30)
        optimized = subprocess.run([sys.executable, "-O", str(COMPANION), "--nmax", "2"],
                                   check=True, capture_output=True, text=True, timeout=30)
        self.assertEqual(normal.stdout, optimized.stdout)
        data = json.loads(normal.stdout)
        self.assertEqual(data["report"], 276)
        self.assertTrue(data["finite_diagnostics_not_proofs"])
        self.assertFalse(data["quadratic_phase_partitions"]["theorem_scale_partition_enumerated"])
        self.assertFalse(data["rational_recurrence_samples"]["all_real_certificate"])

    def test_runtime_guards_survive_optimization(self):
        program = '''
import importlib.util, json, sys
sys.dont_write_bytecode = True
s = importlib.util.spec_from_file_location("e", sys.argv[1])
e = importlib.util.module_from_spec(s)
s.loader.exec_module(e)
cases = [lambda: e._ensure(False, "sentinel"), lambda: e.run_checks(13),
         lambda: e.run_checks(2, 1), lambda: e.target_length(2**1024, 1),
         lambda: e.quadratic_refinement(6, 0, 2, 4, 1, 0, 0, 1, 2, 2),
         lambda: e.recurrence_witness(7, 1, 1), lambda: e.all_step_moments(4, [0, 0], 2)]
results = []
for call in cases:
    try:
        call()
    except (ValueError, e.CheckFailure) as exc:
        results.append(type(exc).__name__)
    else:
        raise RuntimeError("guard did not reject invalid input")
print(json.dumps(results))
'''
        normal = subprocess.run([sys.executable, "-c", program, str(COMPANION)],
                                check=True, capture_output=True, text=True, timeout=30)
        optimized = subprocess.run([sys.executable, "-O", "-c", program, str(COMPANION)],
                                   check=True, capture_output=True, text=True, timeout=30)
        self.assertEqual(normal.stdout, optimized.stdout)
        self.assertEqual(json.loads(normal.stdout), ["CheckFailure"]+["ValueError"]*6)

    def test_json_has_no_inexact_number(self):
        data = e.run_checks(2)
        def visit(value):
            self.assertNotIsInstance(value, (float, complex, Q))
            if isinstance(value, dict):
                for child in value.values():
                    visit(child)
            elif isinstance(value, (tuple, list)):
                for child in value:
                    visit(child)
        visit(data)


if __name__ == "__main__":
    unittest.main()
