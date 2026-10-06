"""Run with python -m unittest -v, or python -O -m unittest -v.

unittest checks are ordinary method calls and stay active under -O.
The default suite imports only the standard library.
"""
from decimal import Decimal
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
import packed_matrix as pm

PREFIX = [1, 2, 66, 5546, 893490, 235804122, 92540869002, 50592275219138,
          36763980389367378, 34277110454602760762, 39890088439337327537706,
          56678337951284473917309346, 96562013312452672907356749786,
          194303876852797223949281552591106, 455927121076167354458618221923117282]


class ExactCounts(unittest.TestCase):
    def test_frozen_prefix_and_both_routes(self):
        self.assertEqual([int(s) for s in pm.read_oeis_prefix()["terms"]], PREFIX)
        for n, expected in enumerate(PREFIX):
            with self.subTest(n=n):
                self.assertEqual(pm.count_stirling(n), expected)
                self.assertEqual(pm.count_inclusion(n), expected)

    def test_larger_independent_count(self):
        for n in (20, 30):
            self.assertEqual(pm.count_stirling(n), pm.count_inclusion(n))
        self.assertEqual(pm.count_stirling(20), 1134648286426968698549238131878228224151475496145235340570)

    def test_large_integer_encoding(self):
        self.assertEqual(pm.integer_decimal(0), "0")
        self.assertEqual(pm.integer_decimal(10**5000+123), "1"+"0"*4997+"123")
        with self.assertRaises(ValueError):
            pm.integer_decimal(-1)
        with self.assertRaises(ValueError):
            pm.integer_decimal(2**65536)
        with self.assertRaises(TypeError):
            pm.integer_decimal(True)

    def test_stirling_boundaries(self):
        self.assertEqual(pm.first_kind_row(0), [1])
        self.assertEqual(pm.first_kind_row(4), [0, 6, 11, 6, 1])
        self.assertEqual(pm.second_kind_table(4)[-1], [0, 1, 7, 6, 1])
        self.assertEqual(pm.ordered_bell_numbers(5), (1, 1, 3, 13, 75, 541))

    def test_count_input_errors(self):
        for func, maximum in ((pm.count_stirling, pm.MAX_COUNT_N), (pm.count_inclusion, pm.MAX_IE_N),
                              (pm.marked_transform, pm.MAX_MARKED_N), (pm.marked_enumeration, pm.MAX_ENUM_N)):
            for bad in (-1, maximum+1):
                with self.subTest(func=func.__name__, bad=bad), self.assertRaises(ValueError):
                    func(bad)
            for bad in (True, False, 1.0, "1", None):
                with self.subTest(func=func.__name__, bad=bad), self.assertRaises(TypeError):
                    func(bad)


class MarkedChecks(unittest.TestCase):
    def test_direct_vs_transform(self):
        for n in range(5):
            with self.subTest(n=n):
                exact = pm.marked_transform(n)
                self.assertEqual(exact, pm.marked_enumeration(n))
                self.assertEqual(sum(exact.values()), PREFIX[n])
                for (j, k), count in exact.items():
                    self.assertGreater(count, 0)
                    self.assertLessEqual(j, n)
                    self.assertLessEqual(k, 2*n)

    def test_known_polynomials(self):
        self.assertEqual(pm.marked_transform(0), {(0, 0): 1})
        self.assertEqual(pm.marked_transform(1), {(1, 1): 1, (0, 2): 1})
        self.assertEqual(pm.marked_transform(2), {
            (2, 1): 1, (2, 2): 2, (1, 1): 2, (1, 2): 16,
            (1, 3): 18, (0, 2): 1, (0, 3): 12, (0, 4): 14})

    def test_moments_and_exact_encoding(self):
        row = pm.marked_record(1, pm.marked_transform(1))
        self.assertEqual(row["mean_J"], "1/2")
        self.assertEqual(row["mean_K"], "3/2")
        self.assertEqual(row["variance_K"], "1/4")
        self.assertIsInstance(row["total"], str)


class CoefficientChecks(unittest.TestCase):
    def test_twelve_exact_specializations(self):
        result = pm.exact_coefficient_checks()
        self.assertTrue(result["all_matches"])
        self.assertEqual(len(result["checks"]), 12)

    def test_C0_and_independent_C1(self):
        q, R = Fraction(3, 4), Fraction(2, 3)
        t = 2*q
        C1 = t/(48*(t-1)**3)*(2*R**2*t**4-9*R**2*t**3+12*R**2*t**2-5*R**2*t
             -6*R*t**3+6*R*t**2+12*R*t-12*R-2*t**3-3*t**2+24*t-24)
        result = pm.rational_coefficients(q, R)
        self.assertEqual(result[0], 1)
        self.assertEqual(result[1], C1)
        self.assertTrue(all(isinstance(value, Fraction) for value in result))

    def test_maximum_documented_rational_text(self):
        from run_companion import rational
        import argparse
        numerator, denominator = 10**76, 10**76+1
        text = str(numerator)+"/"+str(denominator)
        self.assertEqual(len(text), 155)
        self.assertEqual(rational(text), Fraction(numerator, denominator))
        with self.assertRaises(argparse.ArgumentTypeError):
            rational("1"*78+"/2")

    def test_coefficient_input_errors(self):
        for q, R in ((Fraction(1,2), Fraction(1)), (Fraction(1), Fraction(1)),
                     (Fraction(3,4), Fraction(0)), (Fraction(3,4), Fraction(3))):
            with self.assertRaises(ValueError):
                pm.rational_coefficients(q, R)
        with self.assertRaises(TypeError):
            pm.rational_coefficients(0.75, Fraction(1))
        with self.assertRaises(ValueError):
            pm.rational_coefficients(Fraction(3,4), Fraction(1), "unknown")
        with self.assertRaises(ValueError):
            pm.rational_coefficients(Fraction(2**300-1, 2**300), Fraction(1))


class DecimalChecks(unittest.TestCase):
    def test_uncertified_reference_digits(self):
        result = pm.decimal_diagnostics([20], digits=40)
        self.assertIn("UNCERTIFIED", result["certification"])
        expected = ["1", "-0.521806701556482663889144103069", "0.128288828088705778459796704234",
                    "-0.002443538422848595003740380956"]
        for actual, target in zip(result["C0_C3"], expected):
            self.assertLess(abs(Decimal(actual)-Decimal(target)), Decimal("1e-27"))
        self.assertEqual(result["records"][0]["exact_count"], str(pm.count_stirling(20)))
        self.assertTrue(result["constants"]["pi"].startswith("3.141592653589793238462"))

    def test_inverse_diagnostics(self):
        result = pm.decimal_diagnostics([20, 100], digits=40)
        for row in result["records"]:
            values = row["inverse_errors"]
            core, first, second = (Decimal(values[key]) for key in
                                   ("core_error", "first_corrected_error", "second_corrected_error"))
            self.assertLess(core, 0)
            self.assertLess(abs(first), abs(core))
            self.assertLess(abs(second), abs(first))
        self.assertIn("not an exact integer inverse", result["inverse_scope"])

    def test_numeric_errors(self):
        for indices, digits in (([], 40), ([0], 40), ([801], 40), ([1, 1], 40),
                                ([1], 29), ([1], 161), (list(range(1, 14)), 40)):
            with self.assertRaises(ValueError):
                pm.decimal_diagnostics(indices, digits)
        with self.assertRaises(TypeError):
            pm.decimal_diagnostics([True], 40)


class OutputAndCli(unittest.TestCase):
    def test_deterministic_exclusive_writes(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            payload = {"sample.json": {"exact_integer": "12345678901234567890", "x": 1}}
            pm.write_bundle(root/"a", payload)
            pm.write_bundle(root/"b", payload)
            for name in ("sample.json", "manifest.json"):
                self.assertEqual((root/"a"/name).read_bytes(), (root/"b"/name).read_bytes())
            saved = (root/"a"/"sample.json").read_bytes()
            with self.assertRaises(FileExistsError):
                pm.write_bundle(root/"a", {"sample.json": {"changed": True}})
            self.assertEqual((root/"a"/"sample.json").read_bytes(), saved)
            manifest = json.loads((root/"a"/"manifest.json").read_text())
            self.assertEqual(manifest["files"]["sample.json"], hashlib.sha256(saved).hexdigest())
            with self.assertRaises(ValueError):
                pm.write_bundle(root/"bad", {"../escape.json": {}})

    def test_traversal_and_symlink_ancestors(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root/"real").mkdir()
            (root/"link").symlink_to(root/"real", target_is_directory=True)
            with self.assertRaises(ValueError):
                pm.write_bundle(root/"real"/".."/"escaped", {"x.json": {}})
            with self.assertRaises(OSError):
                pm.write_bundle(root/"link"/"escaped", {"x.json": {}})
            with self.assertRaises(FileExistsError):
                pm.write_bundle(root/"link", {"x.json": {}})
            self.assertFalse((root/"escaped").exists())
            self.assertEqual(list((root/"real").iterdir()), [])
            for name in ("", "manifest.json", "sub/x.json", "sub\\x.json"):
                with self.assertRaises(ValueError):
                    pm.write_bundle(root/"bad", {name: {}})
            self.assertFalse((root/"bad").exists())

    def test_cli_errors_and_success(self):
        script = str(pm.ROOT/"run_companion.py")
        for args in (("count", "-1"), ("count", "101"), ("marked", "5"),
                     ("coefficients", "--q", "3/4", "--R", "1/0"),
                     ("diagnostics", "1", "--digits", "29")):
            completed = subprocess.run([sys.executable, script, *args], capture_output=True, text=True)
            self.assertEqual(completed.returncode, 2)
            self.assertIn("error:", completed.stderr)
            self.assertNotIn("Traceback", completed.stderr)
        success = subprocess.run([sys.executable, script, "count", "2"], capture_output=True, text=True)
        self.assertEqual(success.returncode, 0, success.stderr)
        self.assertEqual(json.loads(success.stdout)["count"], "66")

    def test_existing_generation_destination_is_untouched(self):
        with tempfile.TemporaryDirectory() as directory:
            marker = Path(directory)/"keep.txt"
            marker.write_text("keep me", encoding="utf-8")
            completed = subprocess.run([sys.executable, str(pm.ROOT/"run_companion.py"),
                                        "generate", "--output", directory], capture_output=True, text=True)
            self.assertEqual(completed.returncode, 2)
            self.assertEqual(marker.read_text(), "keep me")
            self.assertEqual(sorted(p.name for p in Path(directory).iterdir()), ["keep.txt"])


if __name__ == "__main__":
    unittest.main()
