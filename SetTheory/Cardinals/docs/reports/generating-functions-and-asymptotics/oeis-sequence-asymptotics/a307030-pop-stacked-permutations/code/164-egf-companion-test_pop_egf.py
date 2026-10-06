#!/usr/bin/env python3
"""Standard-library regression tests for the bounded Report164 companion.

Run from the package root: python -B -m unittest discover -s companion -v
The test runner may read its own fixed JSON fixture; the companion never does.
"""

import ast
from fractions import Fraction
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch

import pop_egf as egf

HERE = Path(__file__).resolve().parent
SCRIPT = HERE / "pop_egf.py"
ROOT = HERE.parent


class BoundsTests(unittest.TestCase):
    def test_all_public_indexed_functions_reject_nonints(self):
        class IntegerSubclass(int):
            pass

        class IndexLike:
            def __index__(self):
                return 5

        for function in (egf.count_coefficients, egf.quotient_coefficients, egf.verify):
            for value in (True, False, 1.0, "1", None, Fraction(1), [1], IntegerSubclass(1), IndexLike()):
                with self.subTest(function=function.__name__, value_type=type(value).__name__):
                    with self.assertRaises(TypeError):
                        function(value)

    def test_all_public_indexed_functions_reject_out_of_bounds_before_work(self):
        for function, maximum in ((egf.count_coefficients, 400),
                                  (egf.quotient_coefficients, 70), (egf.verify, 70)):
            for value in (-1, maximum + 1, 10 ** 10000):
                with self.subTest(function=function.__name__, maximum=maximum):
                    # These fail if coefficient work starts before validation.
                    with patch.object(egf, "_binomial_row", side_effect=RuntimeError("premature recurrence")):
                        with patch.object(egf, "_quotient_series", side_effect=RuntimeError("premature quotient")):
                            with self.assertRaises(ValueError):
                                function(value)

    def test_zero_boundaries(self):
        self.assertEqual(egf.count_coefficients(0), [1])
        self.assertEqual(egf.quotient_coefficients(0), [1])
        result = egf.verify(0)
        self.assertEqual(result["counts_as_decimal_strings"], ["1"])
        self.assertEqual(result["checks"]["riccati_divisibility_checks"], 0)

    def test_explicit_failures_are_not_assertions(self):
        with self.assertRaises(egf.VerificationError):
            egf._require(False, "deliberate failure")
        with patch.object(egf, "_binomial_row", return_value=iter([0])):
            with self.assertRaises(egf.VerificationError):
                egf.count_coefficients(1)
        with patch.object(egf, "_RHO_LOWER", egf._RHO_UPPER):
            with self.assertRaises(egf.VerificationError):
                egf.certify_constants()


class ExactTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.fixture = json.loads((ROOT / "data" / "counts_p0_p70.json").read_text())
        cls.verification = egf.verify(70)

    def test_every_frozen_term_matches_both_routes(self):
        self.assertEqual(self.verification["verified_through_n"], 70)
        self.assertEqual(self.verification["counts_as_decimal_strings"], self.fixture["counts_as_decimal_strings"])
        self.assertEqual(tuple(map(int, self.fixture["counts_as_decimal_strings"])), egf._SOURCE_COUNTS)
        self.assertEqual(self.fixture["provenance"]["source_sha256"], egf._SOURCE_SHA256)
        self.assertEqual(self.verification["checks"]["riccati_divisibility_checks"], 70)
        self.assertEqual(self.verification["checks"]["quotient_integrality_checks"], 71)

    def test_count_upper_boundary(self):
        counts = egf.count_coefficients(400)
        self.assertEqual(len(counts), 401)
        self.assertEqual(counts[:71], list(egf._SOURCE_COUNTS))
        self.assertTrue(all(type(value) is int and value > 0 for value in counts))
        # Lower/upper truncation consistency, independent of the source fixture.
        self.assertEqual(counts[:400], egf.count_coefficients(399))

    def test_nonzero_resultant_specialization(self):
        result = egf.resultant_nonzero_check()
        self.assertEqual(result["sylvester_determinant"], -12)
        self.assertEqual(result["quadratics_descending_coefficients"], [[2, 4, 0], [5, 8, -1]])

    def test_certificate_strict_signs_and_enclosures(self):
        result = egf.certify_constants()
        self.assertTrue(all(result["checks"].values()))
        self.assertGreater(Fraction(result["D_at_rho_lower"][0]), 0)
        self.assertLess(Fraction(result["D_at_rho_upper"][1]), 0)
        lower, upper = map(Fraction, result["rho_rational_bracket"])
        self.assertLess(lower, upper)
        c_lower, c_upper = map(Fraction, result["C_rational_bracket"])
        propagated_lower, propagated_upper = map(Fraction, result["amplitude_propagated_interval"])
        self.assertLess(c_lower, propagated_lower)
        self.assertLessEqual(propagated_lower, propagated_upper)
        self.assertLess(propagated_upper, c_upper)

    def test_binomial_rows(self):
        self.assertEqual(list(egf._binomial_row(0)), [1])
        self.assertEqual(list(egf._binomial_row(5)), [1, 5, 10, 10, 5, 1])
        self.assertEqual(sum(egf._binomial_row(400)), 1 << 400)

    def test_fraction_decimal_outward_rounding(self):
        for value in (Fraction(0), Fraction(1, 3), Fraction(-1, 3), Fraction(-1, 10**12)):
            with self.subTest(value=value):
                lower, upper = map(Fraction, egf._outward_decimal((value, value), 5))
                self.assertLessEqual(lower, value)
                self.assertGreaterEqual(upper, value)

    def test_quotient_does_not_call_recurrence(self):
        with patch.object(egf, "count_coefficients", side_effect=RuntimeError("not independent")):
            self.assertEqual(egf.quotient_coefficients(8), list(egf._SOURCE_COUNTS[:9]))


class InterfaceTests(unittest.TestCase):
    def run_cli(self, *arguments, optimized=False):
        flags = ["-B"] + (["-O"] if optimized else [])
        return subprocess.run([sys.executable, *flags, str(SCRIPT), *arguments],
                              text=True, capture_output=True, timeout=180, check=False)

    def test_rejected_cli_inputs_status_two_stderr_only(self):
        cases = (("counts", "--n", "401"), ("counts", "--n", "-1"),
                 ("counts", "--n", "true"), ("counts", "--n", "1.5"),
                 ("counts", "--n", "9" * 10000), ("counts",),
                 ("verify", "--n", "71"), ("certify", "--n", "1"),
                 ("counts", "--n", "2", "--output", "unapproved.json"))
        for arguments in cases:
            with self.subTest(command=arguments[0], argument_length=len(arguments[-1])):
                for optimized in (False, True):
                    result = self.run_cli(*arguments, optimized=optimized)
                    self.assertEqual(result.returncode, 2)
                    self.assertEqual(result.stdout, "")
                    self.assertTrue(result.stderr)

    def test_normal_optimized_byte_equivalence_at_upper_bounds(self):
        for arguments in (("counts", "--n", "400"), ("verify", "--n", "70"), ("certify",)):
            with self.subTest(command=arguments[0]):
                normal = self.run_cli(*arguments)
                optimized = self.run_cli(*arguments, optimized=True)
                self.assertEqual(normal.returncode, 0, normal.stderr)
                self.assertEqual(optimized.returncode, 0, optimized.stderr)
                self.assertEqual(normal.stderr, "")
                self.assertEqual(optimized.stderr, "")
                self.assertEqual(normal.stdout, optimized.stdout)
                self.assertIsInstance(json.loads(normal.stdout), dict)

    def test_clean_import_no_output_or_application_writes(self):
        # -B excludes interpreter-managed .pyc output. The audit hook rejects any
        # write attempt by the module, imports, or filesystem API calls.
        code = r'''
import os, sys
sys.path.insert(0, sys.argv[1])
def guard(event, args):
    if event == "open":
        path, mode, flags = args
        if (isinstance(mode, str) and any(c in mode for c in "wax+")) or (flags is not None and flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND)):
            raise RuntimeError("unexpected filesystem write")
    if event in ("os.mkdir", "os.remove", "os.rename", "os.rmdir", "socket.connect"):
        raise RuntimeError("unexpected side effect")
sys.addaudithook(guard)
import pop_egf
'''
        for optimized in (False, True):
            flags = ["-B"] + (["-O"] if optimized else [])
            result = subprocess.run([sys.executable, *flags, "-c", code, str(HERE)],
                                    text=True, capture_output=True, timeout=30, check=False)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout, "")
            self.assertEqual(result.stderr, "")

    def test_runtime_source_has_no_assert_or_float_literals(self):
        tree = ast.parse(SCRIPT.read_text())
        self.assertFalse(any(isinstance(node, ast.Assert) for node in ast.walk(tree)))
        self.assertFalse(any(isinstance(node, ast.Constant) and isinstance(node.value, float)
                             for node in ast.walk(tree)))

    def test_certificate_checks_survive_optimization(self):
        code = r'''
import sys
sys.path.insert(0, sys.argv[1])
import pop_egf as e
e._RHO_LOWER = e._RHO_UPPER
try:
    e.certify_constants()
except e.VerificationError:
    sys.exit(0)
sys.exit(5)
'''
        result = subprocess.run([sys.executable, "-B", "-O", "-c", code, str(HERE)],
                                text=True, capture_output=True, timeout=30, check=False)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, "")


if __name__ == "__main__":
    unittest.main()
