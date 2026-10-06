#!/usr/bin/env python3
"""Meaningful exact and negative-path tests, active under python -O.

Uses unittest checks and explicit production exceptions, never bare assert.
Run from any directory: python /path/to/companion/test_exact_matrix.py
"""
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import exact_matrix as M


class ExactCountingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.ode = M.ode_sequence(M.MAX_ODE_N)
        cls.gf = M.gf_sequence(M.MAX_GF_N)

    def test_zero_and_small_known_values(self):
        for route in (M.compressed_dp, M.tuple_dp, M.literal_bitmask):
            with self.subTest(route=route.__name__):
                self.assertEqual([route(n) for n in range(4)], [1, 2, 16, 265])
        self.assertEqual(self.ode[:5], [1, 2, 16, 265, 7343])
        self.assertEqual(M.gf_sequence(0), [1])
        self.assertEqual(M.ode_sequence(0), [1])

    def test_all_17_oeis_values(self):
        self.assertEqual(self.ode[:17], M.load_fixtures())
        self.assertEqual(self.gf[:17], M.load_fixtures())
        self.assertEqual(M.load_oeis_source(), M.load_fixtures())

    def test_source_hash_provenance(self):
        metadata = json.loads((M.DATA / "fixture_provenance.json").read_text())
        self.assertEqual(hashlib.sha256((M.DATA / "oeis_term_records.txt").read_bytes()).hexdigest(),
                         metadata["term_records_sha256"])
        self.assertEqual(metadata["fixture_terms"], 17)

    def test_compressed_dp_through_40_and_upper_bound(self):
        self.assertEqual([M.compressed_dp(n) for n in range(41)], self.ode[:41])
        self.assertEqual(M.compressed_dp(M.MAX_DP_N), self.ode[M.MAX_DP_N])

    def test_labeled_tuple_dp_through_8(self):
        self.assertEqual([M.tuple_dp(n) for n in range(9)], self.ode[:9])

    def test_literal_all_masks_through_4(self):
        self.assertEqual([M.literal_bitmask(n) for n in range(5)], self.ode[:5])

    def test_independent_rational_gf_through_50(self):
        self.assertEqual(self.gf, self.ode[:51])

    def test_independent_gf_ode_residual(self):
        self.assertEqual(M.ode_residuals(self.gf), [Fraction(0)] * 50)
        corrupted = self.gf[:]
        corrupted[13] += 1
        self.assertTrue(any(M.ode_residuals(corrupted)))

    def test_ode_at_upper_bound(self):
        self.assertEqual(len(self.ode), 2001)
        self.assertTrue(all(b > a for a, b in zip(self.ode, self.ode[1:])))
        self.assertGreater(len(M.decimal_integer(self.ode[-1])), 4300)

    def test_exact_division_checked(self):
        self.assertEqual(M.exact_divide(32, 16), 2)
        self.assertEqual(M.exact_divide(-32, 16), -2)
        self.assertEqual(M.exact_divide(32, -16), -2)
        with self.assertRaises(ArithmeticError):
            M.exact_divide(33, 16)
        with self.assertRaises(ZeroDivisionError):
            M.exact_divide(1, 0)
        for numerator, denominator in ((True, 1), (1, True), (1.0, 1), (1, 1.0)):
            with self.subTest(numerator=numerator, denominator=denominator):
                with self.assertRaises(TypeError):
                    M.exact_divide(numerator, denominator)

    def test_production_ode_detects_nonintegral_recurrence(self):
        corrupt = ((33,) + M.ODE_POLYNOMIALS[0][1:],) + M.ODE_POLYNOMIALS[1:]
        with patch.object(M, "ODE_POLYNOMIALS", corrupt):
            with self.assertRaisesRegex(ArithmeticError, "nonzero remainder"):
                M.ode_sequence(1)

    def test_large_decimal_without_global_safeguard_change(self):
        before = sys.get_int_max_str_digits() if hasattr(sys, "get_int_max_str_digits") else None
        self.assertEqual(M.decimal_integer(10**5000 + 7), "1" + "0" * 4999 + "7")
        self.assertEqual(M.decimal_integer(-(10**5000 + 7)), "-1" + "0" * 4999 + "7")
        self.assertEqual(M.decimal_integer(0), "0")
        if before is not None:
            self.assertEqual(sys.get_int_max_str_digits(), before)

    def test_integrated_verification(self):
        report = M.verify(40, 40, 30, 8, 4)
        self.assertEqual(report["status"], "PASS")
        self.assertEqual(report["fixture_terms"], 17)
        self.assertEqual(report["independent_ode_residual_count"], 30)

    def test_integrated_check_detects_bad_dp(self):
        with patch.object(M, "compressed_dp", return_value=-1):
            with self.assertRaisesRegex(ArithmeticError, "compressed DP"):
                M.verify(16, 0, 0, 0, 0)


class ValidationTests(unittest.TestCase):
    def test_numeric_api_types_and_bounds(self):
        routes = ((M.ode_sequence, M.MAX_ODE_N), (M.gf_sequence, M.MAX_GF_N),
                  (M.compressed_dp, M.MAX_DP_N), (M.tuple_dp, M.MAX_TUPLE_N),
                  (M.literal_bitmask, M.MAX_LITERAL_N))
        for route, cap in routes:
            for value in (True, False, 1.0, "1", None, Fraction(1)):
                with self.subTest(route=route.__name__, value=value):
                    with self.assertRaises(TypeError):
                        route(value)
            for value in (-1, cap + 1, 10**100):
                with self.subTest(route=route.__name__, value=value):
                    with self.assertRaises(ValueError):
                        route(value)

    def test_verify_rejects_bad_bounds_before_work(self):
        for kwargs in ({"max_n": True}, {"max_n": 15}, {"max_n": 2001},
                       {"dp_max_n": 61}, {"gf_max_n": 51}, {"tuple_max_n": 9},
                       {"literal_max_n": 5}, {"max_n": 16},
                       {"tuple_max_n": True}, {"gf_max_n": False}):
            with self.subTest(kwargs=kwargs):
                with self.assertRaises((ValueError, TypeError)):
                    M.verify(**kwargs)

    def test_residual_input_validation(self):
        for values in ([], (), None, "12", iter([1, 2])):
            with self.subTest(values=values):
                with self.assertRaises(TypeError):
                    M.ode_residuals(values)
        for values in ([True], [-1], [1.0], ["1"], [1] * 2002):
            with self.subTest(values_type=type(values)):
                with self.assertRaises(ValueError):
                    M.ode_residuals(values)
        self.assertEqual(M.ode_residuals([1]), [])

    def test_comparison_guard_survives_optimization(self):
        with self.assertRaises(ArithmeticError):
            M.require_equal(1, 2, "intentional mismatch")

    def test_fixture_schema_corruptions(self):
        good = json.loads((M.DATA / "oeis_fixtures.json").read_text())
        corruptions = [[], {}, {**good, "sequence": "A000000"}, {**good, "offset": True},
                       {**good, "offset": 1}, {**good, "offset": 0.0},
                       {**good, "extra": "not allowed"}, {**good, "terms": good["terms"][:-1]},
                       {**good, "terms": ["0"] + good["terms"][1:]}]
        for bad in (True, 2, 2.0, "02", "+2", "-2", "2.0", " 2", "2 ", "2\n", "２", "1" * 129):
            terms = good["terms"][:]
            terms[1] = bad
            corruptions.append({**good, "terms": terms})
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "fixture.json"
            for obj in corruptions:
                path.write_text(json.dumps(obj))
                with self.subTest(obj=obj):
                    with self.assertRaises(ValueError):
                        M.load_fixtures(path)
            for text in ('{"sequence":"A197458","sequence":"A197458"}', "{", "x" * 16385):
                path.write_text(text)
                with self.assertRaises(ValueError):
                    M.load_fixtures(path)
            path.write_bytes(b"\xff")
            with self.assertRaises(ValueError):
                M.load_fixtures(path)
            with self.assertRaises(OSError):
                M.load_fixtures(Path(directory) / "missing")

    def test_plausible_but_false_fixture_fails_exact_verification(self):
        obj = json.loads((M.DATA / "oeis_fixtures.json").read_text())
        obj["terms"][7] = str(int(obj["terms"][7]) + 1)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "fixture.json"
            path.write_text(json.dumps(obj))
            self.assertEqual(len(M.load_fixtures(path)), 17)
            with self.assertRaisesRegex(ArithmeticError, "17 OEIS"):
                M.verify(16, 0, 0, 0, 0, path)

    def test_malformed_oeis_source_fails(self):
        source = (M.DATA / "oeis_term_records.txt").read_text()
        first = next(line for line in source.splitlines() if line.startswith("%S "))
        for text in ("", source + "\n" + first, source.replace("%T ", "%X "),
                     source.replace("%S A197458 1,", "%S A197458 01,"),
                     source.replace("%S A197458", "%S A000000"), "x" * 32769):
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "source.seq"
                path.write_text(text)
                with self.subTest(prefix=text[:50]):
                    with self.assertRaises(ValueError):
                        M.load_oeis_source(path)


class CliTests(unittest.TestCase):
    def run_cli(self, *args, symbolic=False):
        script = Path(M.__file__).with_name("symbolic_coefficients.py") if symbolic else Path(M.__file__)
        optimization = ["-O"] if sys.flags.optimize else []
        return subprocess.run([sys.executable, *optimization, "-S", str(script), *args],
                              text=True, capture_output=True, timeout=20)

    def test_cli_minimal_sequence_without_site_packages(self):
        result = self.run_cli("sequence", "--max-n", "4")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout)["terms"], ["1", "2", "16", "265", "7343"])

    def test_cli_verification(self):
        result = self.run_cli("verify", "--max-n", "16", "--dp-max-n", "16", "--gf-max-n", "16")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout)["status"], "PASS")

    def test_cli_negative_and_overbound_arguments(self):
        cases = [("sequence", "--max-n", value) for value in
                 ("-1", "true", "False", "1.0", "01", "+1", "2001", "9" * 5000)]
        cases += [("verify", option, value) for option, value in
                  (("--max-n", "15"), ("--dp-max-n", "61"), ("--gf-max-n", "51"),
                   ("--tuple-max-n", "9"), ("--literal-max-n", "5"))]
        cases += [("verify", "--max-n", "16"), ("unknown",), ()]
        for args in cases:
            with self.subTest(args=tuple(x[:50] for x in args)):
                result = self.run_cli(*args)
                self.assertEqual(result.returncode, 2)
                self.assertIn("error:", result.stderr)
                self.assertNotIn("Traceback", result.stderr)

    def test_cli_missing_or_malformed_fixture(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "fixture.json"
            for text in (None, "[]", "{broken}"):
                if text is not None:
                    path.write_text(text)
                result = self.run_cli("verify", "--fixture", str(path))
                self.assertEqual(result.returncode, 2)
                self.assertIn("error:", result.stderr)
                self.assertNotIn("Traceback", result.stderr)

    def test_symbolic_cli_rejects_invalid_orders(self):
        for order in ("-1", "true", "1.5", "09", "9", "1000"):
            with self.subTest(order=order):
                result = self.run_cli("--order", order, symbolic=True)
                self.assertEqual(result.returncode, 2)
                self.assertIn("error:", result.stderr)


if __name__ == "__main__":
    print(f"Report168 exact tests; Python {sys.version.split()[0]}; optimize={sys.flags.optimize}", flush=True)
    unittest.main(verbosity=2)
