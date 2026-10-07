"""Exact, boundary, regression and resource-guard tests for Report 277.

Run: python3 -I -B -X int_max_str_digits=640 -m unittest discover -s tests -v
Repeat with -O. Tests use only the Python standard library.
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
SPEC = importlib.util.spec_from_file_location("report277_exact_checks", COMPANION)
e = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(e)
PYTHON = [sys.executable, "-I", "-B", "-X", "int_max_str_digits=640"]


class BudgetTests(unittest.TestCase):
    def test_affine_and_audited_quadratic_are_distinct_bases(self):
        self.assertEqual((e.partition_budget(1)["c"], e.partition_budget(1)["e"]), (6, 3))
        self.assertEqual((e.partition_budget(2)["c"], e.partition_budget(2)["e"]), (116, 38))
        self.assertEqual(e.source_constant(1), 16)
        self.assertEqual(e.source_constant(2), 2048)
        self.assertEqual(e.source_constant(3), 2359296)

    def test_density_exponents_and_source_interface(self):
        self.assertEqual(e.density_exponent(1), 4)
        self.assertEqual(e.density_exponent(2), 513)
        self.assertEqual(e.density_exponent(3), 589825)
        for k in range(1, 33):
            self.assertLessEqual(e.density_exponent(k), e.source_constant(k))

    def test_source_bridge_exact_ceil_boundaries(self):
        for L in (1, 2, 17, 4096):
            for M in (1, 7):
                boundary = M*(8*L)**4
                self.assertEqual(e.source_bridge_length(boundary - 1, M, 1), L)
                self.assertEqual(e.source_bridge_length(boundary, M, 1), L)
                self.assertEqual(e.source_bridge_length(boundary + 1, M, 1), L + 1)
        self.assertEqual(e.source_bridge_length(e.MAX_RATIO, 1, 32), 1)
        self.assertEqual(e.source_bridge_length(1, 1, 1), 1)

    def test_rounding_and_assembly_diagnostics(self):
        result = e.rounding_and_assembly_diagnostics()
        self.assertEqual(result["exact_floor_boundary_cases"], 27)
        self.assertEqual(result["source_ceiling_boundary_cases"], 18)
        self.assertEqual(result["scalar_large_correlation_cases"], 3)
        self.assertTrue(result["scalar_correlation_premises_are_examples_only"])

    def test_general_and_sharper_cubic_recurrence(self):
        general, sharp = e.recurrence_parameters(3), e.recurrence_parameters(3, True)
        self.assertEqual((general["A"], general["B"]), (3280, 16))
        self.assertEqual((sharp["A"], sharp["B"]), (128, 16))
        self.assertEqual(general["divisor_c"], 192)

    def test_general_and_sharper_cubic_partition(self):
        general, sharp = e.partition_budget(3), e.partition_budget(3, True)
        self.assertEqual((general["c"], general["e"]), (10986, 1878))
        self.assertEqual((sharp["c"], sharp["e"]), (7834, 1878))
        self.assertEqual((e.partition_budget(4)["c"], e.partition_budget(4)["e"]), (1563384, 182190))

    def test_finite_degree_range_budget_diagnostics(self):
        for k in range(2, e.MAX_K + 1):
            with self.subTest(k=k):
                result = e.budget_diagnostic(k)
                self.assertTrue(result["checks_passed"])
                self.assertLessEqual(4*result["U"], result["K"])
                if k >= 3:
                    self.assertEqual(tuple(a + b for a, b in zip(result["T_exponents"], result["H_exponents"])),
                                     (result["c"], result["e"]))
                    self.assertEqual(result["uniform_induction_coefficient"], Q(7, 96))

    def test_degree_cap_outputs_fit_restricted_decimal_conversion(self):
        result = e.budget_diagnostic(e.MAX_K)
        for key in ("c", "e", "K", "U", "recurrence_A", "recurrence_B"):
            self.assertLess(len(str(result[key])), 640)

    def test_exact_budget_floor_boundaries(self):
        for c, exponent in ((0, 2), (6, 3), (116, 38)):
            for target in (2, 3, 17):
                boundary = 8*2**c*target**(exponent + 1)
                self.assertEqual(e.exact_budget_length(boundary - 1, 3, c, exponent), target - 1)
                self.assertEqual(e.exact_budget_length(boundary, 3, c, exponent), target)
                self.assertEqual(e.exact_budget_length(boundary + 1, 3, c, exponent), target)

    def test_exact_budget_singleton_and_symbolic_shortcuts(self):
        self.assertEqual(e.exact_budget_length(1, 1, 0, 2), 1)
        self.assertEqual(e.exact_budget_length(e.MAX_RATIO, 1, e.MAX_SYMBOLIC_EXPONENT, 2), 1)
        self.assertEqual(e.exact_budget_length(e.MAX_RATIO, 1, 0, e.MAX_SYMBOLIC_EXPONENT), 1)
        cubic = e.partition_budget(3)
        self.assertEqual(e.exact_budget_length(e.MAX_RATIO, 1, cubic["c"], cubic["e"]), 1)
        self.assertEqual(e.exact_budget_length(2**1023, 2**1023, 0, 2), 1)

    def test_largest_root_input_is_exact(self):
        N = e.MAX_RATIO
        target = e.exact_budget_length(N, 1, 0, 2)
        self.assertLessEqual(8*target**3, 3*N)
        self.assertGreater(8*(target + 1)**3, 3*N)

    def test_small_exact_roots_exhaustively(self):
        for N in range(1, 257):
            for c in (0, 1, 6):
                for exponent in (2, 3, 7):
                    L = e.exact_budget_length(N, 1, c, exponent)
                    self.assertGreater(8*2**c*(L + 1)**(exponent + 1), 3*N)
                    if L > 1:
                        self.assertLessEqual(8*2**c*L**(exponent + 1), 3*N)


class CompactBudgetTests(unittest.TestCase):
    def test_compact_scale_base_ratio_and_squared_source_identity(self):
        self.assertEqual(e.compact_budget_scale(2), 16)
        self.assertEqual(e.compact_budget_scale(3), 384)
        for k in range(2, 33):
            P = e.compact_budget_scale(k)
            self.assertEqual(P*P*2**(k + 1), e.source_constant(k))
            if k >= 3:
                self.assertEqual(P, k*2**k*e.compact_budget_scale(k - 1))

    def test_exact_finite_certificate_table(self):
        result = e.compact_budget_diagnostics(3)
        table = result["finite_certificate_table"]
        self.assertEqual([row["z"] for row in table],
                         [6693877, 6633957, 5268450, 2832889, 954144, 191498, 22175, 1450])
        self.assertEqual((table[0]["A"], table[0]["Pi"]), (3280, 49))
        self.assertEqual((table[1]["A"], table[1]["Pi"]), (315312, 4753))
        for row in table:
            self.assertLessEqual(row["z"]*row["Pi"], 100000*row["A"])
            self.assertLess(100000*row["A"], (row["z"] + 1)*row["Pi"])

    def test_normalized_initial_values_use_general_cubic(self):
        rows = e.compact_budget_diagnostics(3)["finite_degree_rows"]
        self.assertEqual(rows[0]["normalized_product"], Q(1, 16))
        self.assertEqual(rows[0]["normalized_exponent"], 38)
        self.assertEqual(rows[0]["normalized_deficit"], 226)
        self.assertEqual(rows[1]["normalized_exponent"], Q(1878, 49))
        self.assertEqual(rows[1]["normalized_deficit"], Q(7794, 49))
        self.assertNotEqual(rows[1]["normalized_deficit"],
                            Q(10*e.partition_budget(3, True)["e"] - e.partition_budget(3, True)["c"], 49))

    def test_q7_and_exact_product_majorants(self):
        result = e.compact_budget_diagnostics(12)
        self.assertEqual(result["q7"], Q(18772640957, 64424509440))
        self.assertLess(result["q7"], Q(7, 24))
        self.assertEqual(result["normalized_product_majorant"], Q(896, 2877))
        self.assertLess(result["normalized_exponent_majorant"], Q(115, 3))
        self.assertEqual(result["combined_exponent_majorant"], Q(103040, 8631))
        self.assertLess(result["combined_exponent_majorant"], 12)

    def test_certificate_sums_and_conditional_limit_constants(self):
        result = e.compact_budget_diagnostics(10)
        self.assertEqual(result["certificate_upper_sum_through_nine"], Q(22596997, 100000))
        self.assertEqual(result["certificate_lower_sum_through_ten"], Q(22598440, 100000))
        self.assertEqual(result["limiting_deficit_constants_requiring_written_tail_proof"],
                         (Q(9, 700), Q(1, 50)))
        self.assertFalse(result["universal_tail_proved_by_program"])

    def test_finite_deficit_bounds_and_monotonicity(self):
        rows = e.compact_budget_diagnostics(32)["finite_degree_rows"]
        previous = None
        for row in rows:
            deficit = row["normalized_deficit"]
            self.assertGreater(deficit, Q(9, 700))
            if row["k"] >= 10:
                self.assertLess(deficit, Q(1, 50))
            if previous is not None:
                self.assertLess(deficit, previous)
            previous = deficit
            self.assertLess(row["e_over_P"], 12)
            self.assertLess(len(str(deficit)), 640)

    def test_finite_tail_sample_counts_are_not_a_universal_claim(self):
        for kmax, expected in ((2, 0), (9, 0), (10, 1), (12, 3), (32, 23)):
            result = e.compact_budget_diagnostics(kmax)
            self.assertEqual(len(result["finite_degree_rows"]), kmax - 1)
            self.assertEqual(result["finite_certificate_rows"], 8)
            self.assertEqual(result["finite_tail_ratio_samples"], expected)
            self.assertFalse(result["universal_tail_proved_by_program"])


class AlgebraTests(unittest.TestCase):
    def test_ordered_divisors(self):
        self.assertEqual(e.ordered_divisor_count(1, 4096), 1)
        self.assertEqual(e.ordered_divisor_count(2, 12), 6)
        self.assertEqual(e.ordered_divisor_count(3, 12), 18)
        self.assertEqual(e.ordered_divisor_count(8, 1), 1)
        self.assertEqual(e.divisor_diagnostics(4, 24)["ordered_factor_cases"], 96)

    def test_prime_power_divisor_formula(self):
        from math import comb
        for r in range(1, 9):
            for a in range(13):
                self.assertEqual(e.ordered_divisor_count(r, 2**a), comb(a + r - 1, r - 1))

    def test_affine_composition(self):
        self.assertEqual(e.compose_polynomial((1, 2, 3), 4, -2), (Q(57), Q(-52), Q(12)))
        self.assertEqual(e.compose_polynomial((1, Q(1, 2), Q(-2, 7)), 0, 0), (Q(1), Q(0), Q(0)))

    def test_all_degree_difference_coefficients(self):
        from math import factorial
        for k in range(2, 9):
            coefficients = (Q(3, 5),) + (0,)*(k - 1) + (Q(2, 7),)
            shifts = (-2,) + (3,)*(k - 2)
            difference = e.difference_polynomial(coefficients, shifts)
            self.assertEqual(difference[1], factorial(k)*Q(2, 7)*(-2)*3**(k - 2))
            self.assertTrue(all(c == 0 for c in difference[2:]))

    def test_zero_shift_annihilates_and_difference_order_commutes(self):
        coefficients = (3, Q(-2, 7), 4, Q(5, 9), 2)
        self.assertTrue(all(c == 0 for c in e.difference_polynomial(coefficients, (2, 0, -3))))
        self.assertEqual(e.difference_polynomial(coefficients, (2, -3, 1)),
                         e.difference_polynomial(coefficients, (1, 2, -3)))
        self.assertTrue(all(c == 0 for c in e.difference_polynomial((0, 1), (1, 2))))

    def test_independent_subset_difference_expansion_count(self):
        result = e.differencing_diagnostics(8)
        self.assertEqual(result["coefficient_cases"], 28)
        self.assertEqual(result["subset_expansion_evaluations"], 84)
        self.assertEqual(result["differencing_prefactor_cases"], 28)

    def test_rational_recurrence_is_strict_and_degree_general(self):
        for k in (2, 3, 4, 8, 32):
            result = e.rational_recurrence_witness(k, 2, 1, 2)
            self.assertEqual(result["p"], 2)
            self.assertEqual(result["norm"], 0)
            self.assertFalse(result["all_real_certificate"])
        self.assertEqual(e.rational_recurrence_witness(3, 1, 0, 4096)["p"], 1)

    def test_largest_rational_sample_remains_bounded(self):
        result = e.rational_recurrence_witness(32, 512, 511, 4096)
        self.assertLessEqual(result["p"], 512)
        self.assertLess(result["norm"], Q(1, 4096))


class LocalizationTests(unittest.TestCase):
    def test_chunk_endpoint_no_empty_or_short_tail(self):
        self.assertEqual(e.chunk_lengths(2, 2), (2,))
        self.assertEqual(e.chunk_lengths(3, 2), (3,))
        self.assertEqual(e.chunk_lengths(4, 2), (2, 2))
        self.assertEqual(e.chunk_lengths(7, 2), (2, 2, 3))
        self.assertEqual(e.chunk_lengths(4096, 4096), (4096,))
        for target in range(1, 17):
            for size in range(target, 65):
                cells = e.chunk_lengths(size, target)
                self.assertEqual(sum(cells), size)
                self.assertTrue(all(target <= cell < 2*target for cell in cells))

    def test_residue_chains_at_and_above_exact_threshold(self):
        self.assertEqual(e.residue_chunks(6, 2, 3), ((0, 2, 4), (1, 3, 5)))
        for n in (6, 7, 8, 11, 12, 13):
            cells = e.residue_chunks(n, 2, 3)
            self.assertEqual(sorted(x for cell in cells for x in cell), list(range(n)))
            self.assertTrue(all(3 <= len(cell) <= 5 for cell in cells))

    def test_target_two_L_refinement_then_resplitting(self):
        result = e.localization_structure(47, 3, 8, 4)
        self.assertEqual(sorted(x for cell in result["cells"] for x in cell), list(range(47)))
        self.assertTrue(all(8 <= size <= 15 for size in result["inner_lengths"]))
        self.assertTrue(all(4 <= len(cell) <= 7 for cell in result["cells"]))
        self.assertFalse(result["phase_error_certified"])

    def test_largest_toy_partition_stays_bounded(self):
        result = e.localization_structure(4096, 64, 64, 16)
        self.assertEqual(sum(map(len, result["cells"])), 4096)
        self.assertEqual(len(result["cells"]), 256)

    def test_integer_leading_coefficient_must_be_reduced(self):
        result = e.restriction_diagnostic((0, 0, 0, Q(1, 8)), 5, 2, 7)
        self.assertEqual(result["raw_leading_coefficient"], 1)
        self.assertEqual(result["epsilon"], 0)
        self.assertEqual(result["integer_part"], 1)
        self.assertEqual(result["turn_error_majorant"], 0)

    def test_negative_and_tie_centering(self):
        negative = e.restriction_diagnostic((0, 0, Q(6, 7)), 0, 1, 3)
        self.assertEqual(negative["epsilon"], Q(-1, 7))
        self.assertEqual(negative["turn_error_majorant"], Q(4, 7))
        self.assertEqual(e.restriction_diagnostic((0, Q(-1, 2)), 0, 1, 1)["epsilon"], Q(1, 2))

    def test_lower_terms_are_retained_after_translation(self):
        result = e.restriction_diagnostic((0, 0, 0, 1), 2, 3, 4)
        self.assertEqual(result["lower_coefficients"], (Q(8), Q(36), Q(54)))
        self.assertEqual(result["raw_leading_coefficient"], 27)

    def test_wrapping_nonunit_modular_parent(self):
        result = e.modular_restriction_diagnostic(12, 11, 4, 3, (5, 7, 3, 2, 11))
        self.assertEqual(result["points"], (11, 3, 7))
        self.assertTrue(result["proper"])
        self.assertTrue(result["nonunit_step"])

    def test_singleton_modulus_one_and_zero_step(self):
        result = e.modular_restriction_diagnostic(1, 0, 0, 1, (0, 0, 0))
        self.assertEqual(result["points"], (0,))
        self.assertTrue(result["proper"])
        self.assertEqual(e.modular_restriction_diagnostic(8, 3, 0, 1, (1, 2))["points"], (3,))


class VarianceAndAssemblyTests(unittest.TestCase):
    def test_nonunit_covariance(self):
        result = e.coset_pair_moment(4, {0, 2}, 2)
        self.assertEqual(result["pair_expectation"], Q(1, 2))
        self.assertEqual(result["covariance"], Q(1, 4))
        self.assertEqual(result["coset_counts"], (2, 0))
        self.assertEqual(e.coset_pair_moment(4, {0, 2}, 1)["covariance"], 0)

    def test_all_step_multiset_regression(self):
        result = e.all_step_moments(4, {0, 2}, 3)
        self.assertEqual(result["variance"], Q(5, 36))
        self.assertEqual(result["coset_variance"], Q(5, 36))
        self.assertEqual((result["good_steps"], result["bad_steps"]), (2, 2))
        self.assertEqual(result["bad_variance"], Q(1, 4))
        self.assertEqual(result["maximum_proper_gain"], Q(1, 6))
        self.assertFalse(result["simplified_gain_applies"])

    def test_singleton_length_and_empty_subset(self):
        result = e.all_step_moments(4, {0, 2}, 1)
        self.assertEqual(result["bad_steps"], 0)
        self.assertIsNone(result["bad_variance"])
        self.assertEqual(result["variance"], Q(1, 4))
        empty = e.all_step_moments(8, set(), 2)
        self.assertIsNone(empty["discard_gain_lower_bound"])
        self.assertFalse(empty["simplified_gain_applies"])
        self.assertEqual(empty["variance"], 0)

    def test_exact_variance_threshold_and_full_set(self):
        for n, L in ((8, 2), (27, 3), (64, 4)):
            result = e.all_step_moments(n, {0}, L)
            self.assertTrue(result["simplified_gain_applies"])
            self.assertLess(result["bad_fraction"], Q(1, 2*L))
            self.assertGreaterEqual(result["maximum_proper_gain"], (1 - Q(1, n))/(2*L))
        full = e.all_step_moments(8, set(range(8)), 2)
        self.assertEqual(full["variance"], 0)
        self.assertEqual(full["maximum_proper_gain"], 0)

    def test_cover_mass_partial_and_full_union(self):
        partial = e.cover_mass(6, {0, 2}, {0, 1, 2, 3})
        self.assertEqual(partial["mu"], Q(1, 3))
        self.assertEqual(partial["signed_mass"], Q(2, 3))
        full = e.cover_mass(6, {0, 2}, set(range(6)))
        self.assertEqual(full["mu"], Q(4, 9))
        self.assertEqual(full["signed_mass"], 0)

    def test_named_regressions(self):
        result = e.regression_diagnostics()
        self.assertTrue(result["dirichlet_first_comparison_can_be_equality"])
        self.assertTrue(result["target_2L_guard_active"])
        self.assertTrue(result["conditional_p_lt_T_over_R_squared_is_not_the_unconditional_statement"])
        self.assertEqual(result["wrapped_nonunit_points"], (11, 3, 7))

    def test_small_diagnostic_counts_and_scope(self):
        result = e.run_checks(3, 3)
        self.assertEqual(result["report"], 277)
        self.assertEqual(result["finite_variance"]["all_subset_length_instances"], 4*2 + 8*3)
        self.assertEqual(result["finite_variance"]["all_subset_difference_instances"], 4*1 + 8*2)
        self.assertEqual(result["finite_variance"]["kernel_cases"], 3)
        self.assertEqual(result["cover_mass"]["all_A_subset_U_pairs"], 9 + 27)
        self.assertEqual(result["rational_recurrence_samples"]["cases"], (2 + 3)*2)
        self.assertTrue(result["finite_diagnostics_not_proofs"])
        self.assertFalse(result["residue_localization"]["theorem_scale_partition_enumerated"])
        self.assertFalse(result["rational_recurrence_samples"]["all_real_certificate"])


class GuardrailTests(unittest.TestCase):
    def test_no_assert_no_float_no_nonstandard_import(self):
        tree = ast.parse(COMPANION.read_text(encoding="utf-8"))
        allowed = {"__future__", "argparse", "fractions", "functools", "itertools", "json", "math", "re", "sys"}
        for node in ast.walk(tree):
            self.assertNotIsInstance(node, ast.Assert)
            if isinstance(node, ast.Constant):
                self.assertNotIsInstance(node.value, (float, complex))
            if isinstance(node, ast.Import):
                self.assertTrue(all(alias.name in allowed for alias in node.names))
            if isinstance(node, ast.ImportFrom):
                self.assertIn(node.module, allowed)

    def test_invalid_public_inputs(self):
        cases = [
            (e.recurrence_parameters, (1,)), (e.recurrence_parameters, (33,)),
            (e.recurrence_parameters, (True,)), (e.recurrence_parameters, (3, 1)),
            (e.recurrence_parameters, (4, True)), (e.source_constant, (0,)),
            (e.source_constant, (33,)), (e.partition_budget, (0,)),
            (e.partition_budget, (3, 1)), (e.partition_budget, (4, True)),
            (e.budget_diagnostic, (1,)), (e.budget_diagnostic, (33,)),
            (e.density_exponent, (0,)), (e.density_exponent, (33,)),
            (e.compact_budget_scale, (1,)), (e.compact_budget_scale, (33,)),
            (e.compact_budget_scale, (True,)), (e.compact_budget_diagnostics, (1,)),
            (e.compact_budget_diagnostics, (33,)), (e.compact_budget_diagnostics, (True,)),
            (e.source_bridge_length, (2**1024, 1, 1)),
            (e.source_bridge_length, (1, 2, 1)), (e.source_bridge_length, (1, 1, 33)),
            (e.exact_budget_length, (2**1024, 1, 6, 3)),
            (e.exact_budget_length, (1, 2, 6, 3)), (e.exact_budget_length, (1, True, 6, 3)),
            (e.exact_budget_length, (1, 1, -1, 3)), (e.exact_budget_length, (1, 1, 0, 1)),
            (e.exact_budget_length, (1, 1, 2**1024, 3)),
            (e.exact_budget_length, (1, 1, 0, 2**1024)),
            (e.ordered_divisor_count, (0, 1)), (e.ordered_divisor_count, (9, 1)),
            (e.ordered_divisor_count, (2, 4097)), (e.divisor_diagnostics, (9, 2)),
            (e.divisor_diagnostics, (2, 129)), (e.differencing_diagnostics, (9,)),
            (e.compose_polynomial, ((0,)*10, 0, 1)),
            (e.compose_polynomial, ((True, 1), 0, 1)),
            (e.compose_polynomial, ((1.0, 1), 0, 1)),
            (e.compose_polynomial, ((Q(1, 2**128), 1), 0, 1)),
            (e.compose_polynomial, ((2**128, 1), 0, 1)),
            (e.compose_polynomial, ((1, 2), 4097, 1)),
            (e.compose_polynomial, ((1, 2), 0, -4097)),
            (e.compose_polynomial, ((x for x in (1, 2)), 0, 1)),
            (e.difference_polynomial, ((1, 2), ())),
            (e.difference_polynomial, ((1, 2), (1,)*9)),
            (e.difference_polynomial, ((1, 2), (17,))),
            (e.difference_polynomial, ((1, 2), (True,))),
            (e.chunk_lengths, (4097, 2)), (e.chunk_lengths, (1, 2)),
            (e.chunk_lengths, (1, 0)), (e.residue_chunks, (5, 2, 3)),
            (e.residue_chunks, (1, 0, 1)), (e.localization_structure, (11, 1, 6, 4)),
            (e.localization_structure, (16, 1, 8, 0)),
            (e.restriction_diagnostic, ((1,), 0, 1, 1)),
            (e.restriction_diagnostic, ((1, 2), 0, 1, 4097)),
            (e.modular_restriction_diagnostic, (65, 0, 1, 1, (0,))),
            (e.modular_restriction_diagnostic, (12, 11, 4, 4, (0, 1))),
            (e.modular_restriction_diagnostic, (12, 11, 4, 3, (0, 12))),
            (e.modular_restriction_diagnostic, (12, 11, 4, 3, (0, Q(1, 2)))),
            (e.rational_recurrence_witness, (1, 2, 1, 2)),
            (e.rational_recurrence_witness, (3, 513, 1, 2)),
            (e.rational_recurrence_witness, (3, 2, 2, 2)),
            (e.rational_recurrence_witness, (3, 2, 1, 1)),
            (e.rational_recurrence_witness, (3, 2, 1, 4097)),
            (e.coset_pair_moment, (4, {0}, 0)), (e.coset_pair_moment, (4, {0}, 4)),
            (e.coset_pair_moment, (4, [0, 0], 1)),
            (e.all_step_moments, (65, {0}, 2)), (e.all_step_moments, (4, {True}, 2)),
            (e.all_step_moments, (4, {4}, 2)), (e.all_step_moments, (4, {0}, 5)),
            (e.all_step_moments, (4, (x for x in (0, 1)), 2)),
            (e.cover_mass, (4, {0}, {1})), (e.cover_mass, (1, set(), set())),
            (e.run_checks, (9, 3)), (e.run_checks, (2, 33)), (e.run_checks, (2, 2)),
            (e.run_checks, (True, 3)),
        ]
        for function, arguments in cases:
            with self.subTest(function=function.__name__, arguments=repr(arguments)):
                with self.assertRaises(ValueError):
                    function(*arguments)

    def test_parse_ascii_digit_and_collection_guards(self):
        for value in ("", "１２", "-2", "+2", " 2", "2.0", "1"*65, "999"):
            with self.subTest(value=value), self.assertRaises(ValueError):
                e._parse(value, "nmax", 2, 8)
        self.assertEqual(e._parse("0008", "nmax", 2, 8), 8)
        for argv in (["--full"]*6, ["1"*65], "--full", [1]):
            with self.subTest(argv=argv), self.assertRaises(ValueError):
                e.main(argv)

    def test_runtime_check_failure(self):
        with self.assertRaises(e.CheckFailure):
            e._ensure(False, "sentinel")

    def test_normal_optimized_json_match(self):
        command = [str(COMPANION), "--nmax", "2", "--kmax", "32"]
        normal = subprocess.run(PYTHON + command, capture_output=True, text=True, check=True, timeout=30)
        optimized = subprocess.run(PYTHON + ["-O"] + command, capture_output=True, text=True, check=True, timeout=30)
        self.assertEqual(normal.stdout, optimized.stdout)
        data = json.loads(normal.stdout)
        self.assertEqual(data["parameters"]["kmax"], 32)
        self.assertEqual(len(data["budgets"]), 31)
        self.assertEqual(data["report"], 277)

    def test_guard_rejections_under_optimization(self):
        program = '''
import importlib.util, json, sys
s = importlib.util.spec_from_file_location("e", sys.argv[1])
e = importlib.util.module_from_spec(s)
s.loader.exec_module(e)
calls = [lambda: e._ensure(False, "sentinel"), lambda: e.run_checks(9, 3),
         lambda: e.recurrence_parameters(33), lambda: e.partition_budget(4, True),
         lambda: e.exact_budget_length(2**1024, 1, 0, 2),
         lambda: e.exact_budget_length(1, 1, 0, 2**1024),
         lambda: e.ordered_divisor_count(8, 4097),
         lambda: e.compose_polynomial((0, 2**128), 0, 1),
         lambda: e.difference_polynomial((1, 2), (17,)),
         lambda: e.residue_chunks(5, 2, 3),
         lambda: e.localization_structure(11, 1, 6, 4),
         lambda: e.all_step_moments(4, [0, 0], 2),
         lambda: e.rational_recurrence_witness(3, 513, 1, 2),
         lambda: e.compact_budget_scale(33), lambda: e.compact_budget_diagnostics(33)]
results = []
for call in calls:
    try:
        call()
    except (ValueError, e.CheckFailure) as exc:
        results.append(type(exc).__name__)
    else:
        raise RuntimeError("invalid input was accepted")
print(json.dumps(results))
'''
        normal = subprocess.run(PYTHON + ["-c", program, str(COMPANION)],
                                capture_output=True, text=True, check=True, timeout=30)
        optimized = subprocess.run(PYTHON + ["-O", "-c", program, str(COMPANION)],
                                   capture_output=True, text=True, check=True, timeout=30)
        self.assertEqual(normal.stdout, optimized.stdout)
        self.assertEqual(json.loads(normal.stdout), ["CheckFailure"] + ["ValueError"]*14)

    def test_json_no_float_or_fraction_object(self):
        def visit(value):
            self.assertNotIsInstance(value, (float, complex, Q))
            if isinstance(value, dict):
                for child in value.values():
                    visit(child)
            elif isinstance(value, (tuple, list)):
                for child in value:
                    visit(child)
        visit(e.run_checks(2, 3))

    def test_cli_rejects_unsafe_ranges_and_long_strings(self):
        for args in (["--nmax", "9"], ["--kmax", "33"], ["--kmax", "1"*65],
                     ["--nmax", "１２"]):
            result = subprocess.run(PYTHON + ["-O", str(COMPANION)] + args,
                                    capture_output=True, text=True, timeout=10)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")


if __name__ == "__main__":
    unittest.main()
