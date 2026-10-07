"""Independent regressions and bounded-interface tests for Report 278."""
import ast
from fractions import Fraction as Q
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import unittest

COMPANION = Path(__file__).resolve().parents[1]/"companion"/"exact_checks.py"
SPEC = importlib.util.spec_from_file_location("report278_checks", COMPANION)
e = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(e)
PYTHON = [sys.executable, "-I", "-B", "-X", "int_max_str_digits=640"]


class ArithmeticTests(unittest.TestCase):
    def test_prime_and_composite_parameters(self):
        self.assertEqual((e.arithmetic_parameters(7, 4)["m"], e.arithmetic_parameters(7, 4)["q"]), (1, 7))
        self.assertEqual(e.arithmetic_parameters(7, 4)["arithmetic_coefficient"], Q(1, 2))
        p = e.arithmetic_parameters(12, 5)
        self.assertEqual((p["m"], p["q"], p["D"]), (4, 3, 2))
        self.assertEqual(p["arithmetic_coefficient"], 0)
        self.assertEqual(p["geometric_coefficient"], 0)

    def test_divisor_search_against_direct_definition(self):
        for n in range(2, 65):
            for length in range(2, n + 1):
                p = e.arithmetic_parameters(n, length)
                self.assertEqual(p["m"], max(h for h in range(1, length) if n % h == 0))
                self.assertGreaterEqual(p["q"] - 1, p["D"])
                self.assertGreaterEqual(p["arithmetic_coefficient"], p["geometric_coefficient"])

    def test_support_nonunits_and_short_orders(self):
        self.assertTrue(e.proper_support(12, 3, (0, 4, 8)))
        self.assertFalse(e.proper_support(12, 4, (0, 4, 8)))
        self.assertTrue(e.proper_support(12, 12, (0, 1)))
        self.assertTrue(e.proper_support(4, 4, ()))
        self.assertTrue(e.proper_support(4, 4, (2,)))

    def test_maximum_density_against_independent_windows(self):
        from math import gcd
        for n, selected, length in ((4, {0, 2}, 3), (7, {0}, 4), (12, {0, 7, 11}, 3),
                                    (8, set(), 4), (8, set(range(8)), 8)):
            counts = [sum((a + j*d) % n in selected for j in range(length))
                      for a in range(n) for d in range(1, n) if n//gcd(n, d) >= length]
            self.assertEqual(e.maximum_density(n, selected, length), Q(max(counts), length))
        self.assertEqual(e.maximum_density(20, {0, 5, 10, 15}, 5), Q(1, 5))

    def test_exhaustive_counts_and_support_maximality(self):
        for nmax in (2, 4, 8, 12):
            result = e.exhaustive_theorem(nmax)
            self.assertEqual(result["nontrivial_subset_length_triples"],
                             sum((n - 1)*((1 << n) - 2) for n in range(2, nmax + 1)))
            self.assertEqual(result["parameter_pairs"], nmax*(nmax - 1)//2)
        result = e.maximal_support_diagnostics(8)
        self.assertEqual(result["candidate_supports"], 3076)
        self.assertEqual(result["admissible_supports"], 1598)
        self.assertEqual(result["parameter_pairs"], 28)


class MomentTests(unittest.TestCase):
    def test_exact_triangular_law_and_modular_aliasing(self):
        self.assertEqual(e.difference_law(5, (Q(1, 3), Q(1, 3), Q(1, 3), 0, 0)),
                         (Q(1, 3), Q(2, 9), Q(1, 9), Q(1, 9), Q(2, 9)))
        # Integer representatives +2 and -2 coincide modulo four; add weights.
        self.assertEqual(e.difference_law(4, (Q(1, 3), Q(1, 3), Q(1, 3), 0)),
                         (Q(1, 3), Q(2, 9), Q(2, 9), Q(2, 9)))
        self.assertEqual(e.difference_law(2, (1, 0)), (1, 0))

    def test_nonunit_negative_and_zero_covariance(self):
        f = (Q(1, 2), Q(-1, 2), Q(1, 2), Q(-1, 2))
        p = (Q(1, 2), Q(1, 2), 0, 0)
        for h in (0, 2, -2, 4, -4):
            self.assertEqual(e.square_covariance(4, f, p, h)["square"], Q(1, 4))
        for h in (1, -1, 3):
            self.assertEqual(e.square_covariance(4, f, p, h)["square"], 0)

    def test_square_identity_against_direct_triple_sum(self):
        n, h = 5, -2
        f = (Q(1, 3), Q(-1, 2), 1, 0, Q(-2, 7))
        p = (Q(1, 6), Q(1, 3), Q(1, 2), 0, 0)
        independent = sum((p[s]*p[t]*f[a]*f[(a + h*(s - t)) % n]
                           for a in range(n) for s in range(n) for t in range(n)), Q(0))/n
        result = e.square_covariance(n, f, p, h)
        self.assertEqual(result["direct"], independent)
        self.assertEqual(result["square"], independent)

    def test_indicator_and_nonindicator_function(self):
        uniform = (Q(1, 7),)*7
        indicator = e.function_diagnostic(7, 4, (1, 0, 0, 0, 0, 0, 0), uniform)
        self.assertEqual(indicator["mean"], Q(1, 7))
        self.assertEqual(indicator["function_variance"], Q(6, 49))
        self.assertEqual(indicator["maximum_supported_gain"], Q(3, 28))
        self.assertEqual(indicator["raw_gain_lower_bound"], Q(3, 28))
        self.assertTrue(indicator["iid_support_bound_attained"])
        g = (Q(1, 4), Q(1, 2), 0, 1)
        result = e.function_diagnostic(4, 2, g, (Q(1, 4),)*4)
        mean = sum(g)/4
        self.assertEqual(result["function_variance"], sum((value - mean)**2 for value in g)/4)
        self.assertGreaterEqual(result["maximum_supported_gain"], result["clamped_gain_lower_bound"])

    def test_constant_and_nonpositive_regimes(self):
        constant = e.function_diagnostic(4, 4, (Q(1, 3),)*4, (Q(1, 2), Q(1, 2), 0, 0))
        self.assertEqual(constant["function_variance"], 0)
        self.assertEqual(constant["window_variance"], 0)
        self.assertEqual(constant["maximum_supported_gain"], 0)
        result = e.function_diagnostic(12, 5, (1,)+(0,)*11, (Q(1, 3),)*3+(0,)*9)
        self.assertLess(result["raw_gain_lower_bound"], 0)
        self.assertEqual(result["clamped_gain_lower_bound"], 0)

    def test_unequal_iid_collision_is_larger(self):
        g = (1, 0, 0, 0, 0)
        uniform = e.function_diagnostic(5, 3, g, (Q(1, 5),)*5)
        weighted = e.function_diagnostic(5, 3, g, (Q(1, 15), Q(2, 15), Q(3, 15), Q(4, 15), Q(5, 15)))
        self.assertGreater(weighted["collision_probability"], uniform["collision_probability"])
        self.assertFalse(weighted["iid_support_bound_attained"])
        self.assertLess(weighted["raw_gain_lower_bound"], uniform["raw_gain_lower_bound"])

    def test_exact_positive_definite_autocorrelation_mixture(self):
        uniform = (Q(1, 5),)*5
        weighted = (Q(1, 15), Q(2, 15), Q(3, 15), Q(4, 15), Q(5, 15))
        result = e.positive_definite_mixture(5, 3, (1, 0, 0, 0, 0),
                                            (uniform, weighted), (Q(1, 3), Q(2, 3)))
        self.assertEqual(result["zero_mass"], Q(1, 3)*Q(1, 5) + Q(2, 3)*Q(11, 45))
        self.assertGreaterEqual(result["zero_mass"], Q(1, 5))
        self.assertLessEqual(result["raw_gain_lower_bound"], result["method_best_raw_gain"])
        self.assertFalse(result["general_positive_definiteness_solver"])

    def test_derived_fractions_need_not_obey_input_part_cap(self):
        # Valid rational inputs can have an lcm above the individual part cap.
        large = 2**63 - 1
        values = (Q(1, large), Q(1, large - 1), Q(1, large - 2))
        result = e.function_diagnostic(3, 2, values, (Q(1, 3),)*3)
        self.assertGreater(result["mean"].denominator, e.MAX_FRACTION_PART)
        self.assertGreaterEqual(result["maximum_supported_gain"], 0)

    def test_moment_diagnostic_counts(self):
        result = e.moment_diagnostics(8)
        self.assertEqual(result["function_cases"], 168)
        self.assertEqual(result["function_covariance_cases"], 672)
        self.assertEqual(result["iid_collision_cases"], 56)
        self.assertEqual(result["positive_definite_mixture_cases"], 28)
        self.assertEqual(result["signed_square_identity_cases"], 280)


class ExtremizerAndRoundingTests(unittest.TestCase):
    def test_extremizers_and_zero_gain_boundary(self):
        for prime, length in ((2, 2), (5, 3), (5, 5), (13, 11), (23, 23)):
            result = e.prime_extremizer(prime, length)
            self.assertEqual(result["N"], prime*(length - 1))
            self.assertEqual(result["maximum_density"], Q(1, length))
            self.assertEqual(result["gain"], Q(prime - length, prime*length))
            self.assertEqual(result["gain_ratio"], Q(prime - length, prime - 1))
        self.assertEqual(e.prime_extremizer(5, 5)["gain"], 0)

    def test_exact_half_gain_integer_roots(self):
        for n in range(1, 2000):
            length = e.half_gain_length(n)
            self.assertLessEqual(2*(length - 1)**2 + 1, n)
            self.assertGreater(2*length*length + 1, n)
        length = e.half_gain_length(2**128 - 1)
        self.assertLessEqual(2*(length - 1)**2 + 1, 2**128 - 1)
        self.assertGreater(2*length*length + 1, 2**128 - 1)
        self.assertEqual(e.half_gain_length(7), 2)
        self.assertEqual(e.arithmetic_parameters(7, 4)["arithmetic_coefficient"], Q(1, 2))

    def test_coefficient_ceiling_not_floor(self):
        self.assertEqual(e.coefficient_budget(4, Q(2, 7))["D"], 5)
        self.assertEqual(e.coefficient_budget(4, Q(2, 7))["sufficient_N"], 16)
        for length in range(2, 33):
            result = e.coefficient_budget(length, Q(1, 2))
            self.assertEqual(result["D"], 2*(length - 1))
            self.assertEqual(result["sufficient_N"], 2*(length - 1)**2 + 1)

    def test_rational_constant_at_integer_boundary(self):
        result = e.rational_constant_bound(24, 4, Q(3, 2))
        self.assertEqual(result["D"], 7)
        self.assertEqual(result["target_coefficient"], Q(1, 3))
        self.assertGreaterEqual(result["certified_coefficient"], Q(1, 3))
        largest = e.rational_constant_bound(2**128 - 1, 10**6, Q(3, 2))
        self.assertGreater(largest["D"], 10**6)

    def test_affine_sparse_cover_and_three_branches(self):
        singleton = e.affine_scalar_assembly(8, 1, Q(1, 2), 1, Q(1, 4))
        low = e.affine_scalar_assembly(10**9, 10**6, Q(1, 8), Q(1, 4), Q(1, 10**6))
        high = e.affine_scalar_assembly(10**9, 10**6, Q(1, 8), Q(1, 4), Q(1, 8))
        self.assertEqual(singleton["branch"], "singleton")
        self.assertEqual(low["branch"], "variance")
        self.assertEqual(high["branch"], "refinement")
        self.assertEqual(high["mu"], Q(1, 8))
        self.assertFalse(high["actual_cover_or_phase_correlation_certified"])

    def test_affine_exact_cube_boundary_and_branch_equality(self):
        for length in (2, 3, 8):
            alpha = Q(3, 4*length)
            result = e.affine_scalar_assembly(10**8, 128*length**3, Q(1, 2), 1, alpha)
            self.assertEqual(result["ceiling_length"], length)
            self.assertEqual(result["branch"], "variance")
            self.assertEqual(result["H"], 128*length**3)
            result = e.affine_scalar_assembly(10**8, 128*length**3+1, Q(1, 2), 1, Q(1, 1000))
            self.assertEqual(result["ceiling_length"], length + 1)

    def test_named_regressions_and_rounding_counts(self):
        result = e.regression_diagnostics()
        self.assertEqual(result["wrapped_nonunit_points"], (11, 3, 7))
        self.assertEqual(result["nonunit_covariance"], Q(1, 4))
        self.assertFalse(result["quadratic_scale_coefficient_fixed_density_sharpness_proved"])
        self.assertFalse(result["finite_checks_prove_asymptotics"])
        result = e.rounding_diagnostics()
        for key, count in (("half_gain_boundary_cases", 189), ("coefficient_ceiling_cases", 252),
                           ("rational_C_cases", 315), ("root_ceiling_cases", 192), ("affine_scalar_cases", 13)):
            self.assertEqual(result[key], count)


class EndpointTests(unittest.TestCase):
    def test_endpoint_sliding_and_coset_identity(self):
        selected = {0, 1, 3, 6}
        row = e.endpoint_diagnostic(9, selected, 3)
        self.assertEqual(row["density"], Q(4, 9))
        self.assertEqual(row["bad_direction_proportion_beta"], Q(1, 9))
        self.assertEqual(row["image_subgroup_order"], 3)
        self.assertTrue(row["arithmetic_hypotheses_hold"])
        self.assertTrue(row["strict_size_hypothesis_holds"])
        self.assertTrue(row["square_size_hypothesis_holds"])
        # Cosets mod gcd(9,3) have densities 1,1/3,0 in this example.
        self.assertEqual(row["coset_impurity"], Q(2, 27))
        self.assertEqual(row["sliding_window_identities"], 72)
        self.assertEqual(row["density_gain_H"], row["count_gain_eta"]/3)
        self.assertEqual(row["refined_density_gain_lower_bound"],
                         row["density"]*(1-row["density"])/(3*(1+row["bad_direction_proportion_beta"])+row["density"]))
        self.assertGreater(row["count_gain_eta"], row["density"]*(1-row["density"])/2)

    def test_endpoint_arithmetic_hypotheses_are_separate(self):
        general = e.endpoint_diagnostic(5, {0, 1}, 4)
        self.assertTrue(general["arithmetic_hypotheses_hold"])
        self.assertFalse(general["strict_size_hypothesis_holds"])
        self.assertGreaterEqual(general["count_gain_eta"], general["refined_count_gain_lower_bound"])
        no_majority = e.endpoint_diagnostic(12, {0, 1}, 5)
        self.assertFalse(no_majority["proper_direction_majority"])
        self.assertTrue(no_majority["image_subgroup_direction_proper"])
        self.assertIsNone(no_majority["refined_count_gain_lower_bound"])
        short_image = e.endpoint_diagnostic(6, {0, 3}, 3)
        self.assertTrue(short_image["proper_direction_majority"])
        self.assertFalse(short_image["image_subgroup_direction_proper"])
        self.assertEqual(short_image["count_gain_eta"], 0)
        self.assertIsNone(short_image["refined_count_gain_lower_bound"])

    def test_dense_prime_boundary_for_irregular_quotient_subset(self):
        row = e.dense_prime_boundary(7, {0, 2, 4})
        self.assertEqual(row["N"], 42)
        self.assertEqual(row["L"], 7)
        self.assertEqual(row["density"], Q(3, 7))
        self.assertEqual(row["count_gain_eta"], 0)
        self.assertEqual(row["image_subgroup_order"], 6)
        selected = {a for a in range(42) if a % 7 in {0, 2, 4}}
        direct = e.endpoint_diagnostic(42, selected, 7)
        self.assertEqual(direct["maximum_count"], 3)
        self.assertEqual(direct["count_gain_eta"], 0)
        self.assertFalse(direct["arithmetic_hypotheses_hold"])

    def test_endpoint_exhaustive_and_identity_counts(self):
        for nmax, expected in ((8, (1310, 872, 486, 80, 2216, 18)),
                               (12, (34038, 16216, 15830, 194, 10850, 30))):
            result = e.endpoint_diagnostics(nmax)
            keys = ("nontrivial_arithmetic_subset_length_triples", "strict_size_subset_length_triples",
                    "square_size_subset_length_triples", "proof_identity_subset_length_samples",
                    "sliding_window_identity_cases", "dense_prime_boundary_cases")
            self.assertEqual(tuple(result[key] for key in keys), expected)
            self.assertFalse(result["quantitative_constant_claimed_optimal"])

    def test_endpoint_input_guards(self):
        calls = [
            (e.endpoint_diagnostic, (65, {0}, 2)), (e.endpoint_diagnostic, (4, set(), 2)),
            (e.endpoint_diagnostic, (4, set(range(4)), 2)), (e.endpoint_diagnostic, (4, {0}, 5)),
            (e.endpoint_diagnostic, (4, {True}, 2)), (e.endpoint_diagnostic, (4, (x for x in (0,)), 2)),
            (e.endpoint_diagnostic, (4.0, {0}, 2)), (e.endpoint_diagnostic, (4, {0}, True)),
            (e.dense_prime_boundary, (4, {0})), (e.dense_prime_boundary, (29, {0})),
            (e.dense_prime_boundary, (3, set())), (e.dense_prime_boundary, (3, {0, 1, 2})),
            (e.dense_prime_boundary, (3, [0, 0])), (e.dense_prime_boundary, (3, {True})),
            (e.dense_prime_boundary, (3, {3})), (e.dense_prime_boundary, (True, {0})),
            (e.endpoint_diagnostics, (13,)), (e.endpoint_diagnostics, (True,)),
        ]
        for function, args in calls:
            with self.subTest(function=function.__name__, args=repr(args)), self.assertRaises(ValueError):
                function(*args)


class GuardrailTests(unittest.TestCase):
    def test_no_assert_float_or_nonstandard_import(self):
        tree = ast.parse(COMPANION.read_text(encoding="utf-8"))
        allowed = {"__future__", "argparse", "fractions", "json", "math", "re", "sys"}
        for node in ast.walk(tree):
            self.assertNotIsInstance(node, ast.Assert)
            if isinstance(node, ast.Constant):
                self.assertNotIsInstance(node.value, (float, complex))
            if isinstance(node, ast.Import):
                self.assertTrue(all(alias.name in allowed for alias in node.names))
            if isinstance(node, ast.ImportFrom):
                self.assertIn(node.module, allowed)
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and not node.name.startswith("_"):
                self.assertIsNotNone(ast.get_docstring(node), node.name)

    def test_invalid_public_numerical_inputs(self):
        calls = [
            (e.arithmetic_parameters, (True, 2)), (e.arithmetic_parameters, (4.0, 2)),
            (e.arithmetic_parameters, (10**6 + 1, 2)), (e.arithmetic_parameters, (4, 5)),
            (e.arithmetic_parameters, (4, True)), (e.proper_support, (65, 2, ())),
            (e.proper_support, (4, 1, ())), (e.proper_support, (4, 2, (True,))),
            (e.proper_support, (4, 2, (0, 0))), (e.proper_support, (4, 2, (4,))),
            (e.proper_support, (4, 2, range(4))), (e.proper_support, (4, 2, [0]*5)),
            (e.maximum_density, (65, {0}, 2)), (e.maximum_density, (4, {0}, 5)),
            (e.maximum_density, (4, (x for x in range(4)), 2)),
            (e.exhaustive_theorem, (13,)), (e.exhaustive_theorem, (False,)),
            (e.maximal_support_diagnostics, (11,)), (e.maximal_support_diagnostics, (1,)),
            (e.difference_law, (25, ())), (e.difference_law, (2, (Q(1, 2),))),
            (e.difference_law, (2, (1, 1))), (e.difference_law, (2, (2, -1))),
            (e.difference_law, (2, (True, 0))), (e.difference_law, (2, (1.0, 0))),
            (e.difference_law, (2, (Q(1, 2**64), Q(2**64-1, 2**64)))),
            (e.difference_law, (2, (2**64, 0))), (e.difference_law, (2, iter((1, 0)))),
            (e.square_covariance, (2, (0, 1), (Q(1, 2),)*2, 9)),
            (e.square_covariance, (2, (0, 1), (Q(1, 2),)*2, True)),
            (e.square_covariance, (2, (0, 2), (Q(1, 2),)*2, 1)),
            (e.function_diagnostic, (2, 2, (0, 0), (Q(1, 2),)*2)),
            (e.function_diagnostic, (2, 2, (1, 0), (1, 0))),
            (e.function_diagnostic, (4, 4, (1, 0, 0, 0), (Q(1, 2), 0, Q(1, 2), 0))),
            (e.function_diagnostic, (4, 4, (-1, 0, 0, 0), (Q(1, 4),)*4)),
            (e.positive_definite_mixture, (2, 2, (1, 0), [], [])),
            (e.positive_definite_mixture, (2, 2, (1, 0), [(Q(1, 2),)*2]*5, [Q(1, 5)]*5)),
            (e.positive_definite_mixture, (2, 2, (1, 0), [(1, 0)], [1])),
            (e.positive_definite_mixture, (2, 2, (0, 0), [(Q(1, 2),)*2], [1])),
            (e.moment_diagnostics, (11,)), (e.moment_diagnostics, (True,)),
            (e.prime_extremizer, (4, 3)), (e.prime_extremizer, (29, 3)),
            (e.prime_extremizer, (5, 6)), (e.prime_extremizer, (True, 2)),
            (e.half_gain_length, (0,)), (e.half_gain_length, (2**128,)),
            (e.half_gain_length, (True,)), (e.half_gain_length, (2.0,)),
            (e.coefficient_budget, (1, Q(1, 2))), (e.coefficient_budget, (10**6 + 1, Q(1, 2))),
            (e.coefficient_budget, (4, 0)), (e.coefficient_budget, (4, 1)),
            (e.coefficient_budget, (4, True)), (e.coefficient_budget, (4, Q(1, 2**64))),
            (e.rational_constant_bound, (4, 2, 1)), (e.rational_constant_bound, (5, 2, Q(3, 2))),
            (e.rational_constant_bound, (2**128, 2, 2)),
            (e.rational_constant_bound, (10**20, 10**6 + 1, 2)),
            (e.affine_scalar_assembly, (8, 0, Q(1, 2), 1, Q(1, 4))),
            (e.affine_scalar_assembly, (8, 5, Q(1, 4), Q(1, 2), Q(1, 4))),
            (e.affine_scalar_assembly, (8, 1, 0, 1, Q(1, 4))),
            (e.affine_scalar_assembly, (8, 1, 1, 1, Q(1, 4))),
            (e.affine_scalar_assembly, (8, 1, Q(1, 2), Q(1, 4), Q(1, 4))),
            (e.affine_scalar_assembly, (8, 1, Q(1, 2), 1, 0)),
            (e.affine_scalar_assembly, (8, 1, Q(1, 2), 1, Q(3, 4))),
            (e.run_checks, (13,)), (e.run_checks, (True,)), (e.run_checks, (2.0,)),
        ]
        for function, args in calls:
            with self.subTest(function=function.__name__, args=repr(args)):
                with self.assertRaises(ValueError):
                    function(*args)

    def test_parse_before_integer_conversion(self):
        for value in ("", "１２", "-2", "+2", " 2", "2.0", "1"*65, "999", True, 2):
            with self.subTest(value=value), self.assertRaises(ValueError):
                e._parse(value, "nmax", 2, 12)
        self.assertEqual(e._parse("00012", "nmax", 2, 12), 12)
        for argv in (["--full"]*4, ["1"*73], "--full", [1], iter(("--full",))):
            with self.subTest(argv=repr(argv)), self.assertRaises(ValueError):
                e.main(argv)

    def test_runtime_failure_stays_active(self):
        with self.assertRaises(e.CheckFailure):
            e._ensure(False, "sentinel")

    def test_json_has_no_float_complex_or_fraction_objects(self):
        def visit(value):
            self.assertNotIsInstance(value, (float, complex, Q))
            if isinstance(value, dict):
                for child in value.values():
                    visit(child)
            elif isinstance(value, (tuple, list)):
                for child in value:
                    visit(child)
        result = e.run_checks(2)
        visit(result)
        self.assertEqual(result["report"], 278)
        self.assertTrue(result["finite_diagnostics_not_proofs"])

    def test_default_and_full_optimized_json_match(self):
        for args, expected in (([], 3020), (["--full"], 81792)):
            command = [str(COMPANION)] + args
            normal = subprocess.run(PYTHON + command, capture_output=True, text=True, check=True, timeout=30)
            optimized = subprocess.run(PYTHON + ["-O"] + command, capture_output=True, text=True, check=True, timeout=30)
            self.assertEqual(normal.stdout, optimized.stdout)
            result = json.loads(normal.stdout)
            self.assertEqual(result["exhaustive_theorem"]["nontrivial_subset_length_triples"], expected)
            self.assertEqual(normal.stdout, json.dumps(result, sort_keys=True, indent=2) + "\n")

    def test_full_profile_explicit_nmax_override(self):
        result = subprocess.run(PYTHON + [str(COMPANION), "--full", "--nmax", "2"],
                                capture_output=True, text=True, check=True, timeout=30)
        self.assertEqual(json.loads(result.stdout)["parameters"]["nmax"], 2)

    def test_optimized_cli_rejects_bad_inputs(self):
        for args in (["--nmax", "13"], ["--nmax", "1"*65], ["--nmax", "１２"],
                     ["--nmax", "2.0"], ["--nmax=" + "9"*6000], ["--nmax", "-2"]):
            result = subprocess.run(PYTHON + ["-O", str(COMPANION)] + args,
                                    capture_output=True, text=True, timeout=10)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")

    def test_optimized_runtime_guards_match(self):
        program = '''
import importlib.util, json, sys
s = importlib.util.spec_from_file_location("e", sys.argv[1])
e = importlib.util.module_from_spec(s)
s.loader.exec_module(e)
calls = [lambda: e._ensure(False, "sentinel"), lambda: e.run_checks(13),
         lambda: e.arithmetic_parameters(True, 2), lambda: e.proper_support(4, 2, [0, 0]),
         lambda: e.difference_law(2, (1.0, 0)), lambda: e.half_gain_length(2**128),
         lambda: e.coefficient_budget(2, e.Q(1, 2**64)),
         lambda: e.function_diagnostic(2, 2, (1, 0), (1, 0))]
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
        self.assertEqual(json.loads(normal.stdout), ["CheckFailure"] + ["ValueError"]*7)


if __name__ == "__main__":
    unittest.main()
