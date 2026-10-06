"""Bounded tests. Run normally and with -O; no correctness relies on assert."""
from fractions import Fraction as F
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

import companion as c

ROOT = Path(__file__).resolve().parent


class ExactArithmeticTests(unittest.TestCase):
    def test_all_ten_product_and_euler_families(self):
        for cap in c.CAPS:
            for sigma in c.SIGNS:
                with self.subTest(sigma=sigma, cap=cap):
                    a = c.product_counts(sigma, cap)
                    b = c.euler_counts(sigma, cap)
                    self.assertEqual(a, b)
                    self.assertEqual(len(a), c.MAX_N+1)
                    self.assertTrue(all(type(x) is int and x >= 0 for x in a))
                    self.assertEqual(a[0], 1)

    def test_tiny_product_examples_without_zero_evil_part(self):
        self.assertEqual(c.product_counts(-1, None, 8), [1,1,2,2,4,4,6,7,11])
        self.assertEqual(c.product_counts(1, None, 8), [1,0,0,1,0,1,2,0,1])
        self.assertEqual(c.product_counts(-1, 1, 8), [1,1,1,1,1,1,1,2,2])
        self.assertEqual(c.product_counts(1, 1, 8), [1,0,0,1,0,1,1,0,1])
        for cap in c.CAPS:
            for sigma in c.SIGNS:
                self.assertEqual(c.product_counts(sigma, cap, 0), [1])
                self.assertEqual(c.euler_counts(sigma, cap, 0), [1])

    def test_boolean_float_and_coercion_rejection(self):
        class IntSubclass(int):
            pass
        for function in (c.product_counts, c.euler_counts):
            for bad in (True, False, -1.0, 1.0, F(1), "1", IntSubclass(1)):
                with self.subTest(function=function.__name__, bad=repr(bad)):
                    with self.assertRaises(TypeError):
                        function(bad)
            for bad in (True, 1.0, "1", F(1)):
                with self.assertRaises(TypeError):
                    function(-1, bad)
                with self.assertRaises(TypeError):
                    function(-1, None, bad)
            for bad in (-1, c.MAX_N+1):
                with self.assertRaises(ValueError):
                    function(-1, None, bad)
            for bad in (0, 4, 6):
                with self.assertRaises(ValueError):
                    function(-1, bad)
        for bad in (True, 2.0, F(2), "2"):
            with self.assertRaises(TypeError):
                c.exact_threshold(-1, None, bad)
        for bad in (-1, c.MAX_TARGET+1):
            with self.assertRaises(ValueError):
                c.exact_threshold(-1, None, bad)
        for bad in (True, 0.0, 0, "0"):
            with self.assertRaises(TypeError):
                c.bessel_coefficients(bad)
        for bad in (True, 6.0, "6"):
            with self.assertRaises(TypeError):
                c.bessel_coefficients(F(0), bad)
        for bad in (-1, 7):
            with self.assertRaises(ValueError):
                c.bessel_coefficients(F(0), bad)
        with self.assertRaises(ValueError):
            c.inverse_coefficients(F(1))

    def test_ordinary_first_threshold_includes_empty_partition(self):
        for cap in c.CAPS:
            for sigma in c.SIGNS:
                self.assertEqual(c.exact_threshold(sigma, cap, 0), 0)
                self.assertEqual(c.exact_threshold(sigma, cap, 1), 0)
        self.assertEqual(c.exact_threshold(1, None, 2), 6)
        self.assertEqual(c.exact_threshold(1, None, 3), 9)
        self.assertEqual(c.exact_threshold(1, 1, 3), 15)
        # Evil counts visibly decrease on this prefix. No binary search on a
        # presumed monotone sequence may replace examination from index zero.
        self.assertGreater(c.product_counts(1, None, 10)[9], c.product_counts(1, None, 10)[10])
        for cap in c.CAPS:
            for sigma in c.SIGNS:
                counts = c.product_counts(sigma, cap)
                for target in (2, 7, 100):
                    n = c.exact_threshold(sigma, cap, target)
                    self.assertGreaterEqual(counts[n], target)
                    self.assertTrue(all(value < target for value in counts[:n]))

    def test_threshold_exhaustion_is_explicitly_unresolved(self):
        for cap in c.CAPS:
            for sigma in c.SIGNS:
                with self.assertRaisesRegex(c.ThresholdNotFound, "unresolved, not infinite"):
                    c.exact_threshold(sigma, cap, c.MAX_TARGET)

    def test_bessel_product_ode_and_gaussian_through_six(self):
        first = {F(-1,4): F(-5,64), F(0): F(-3,16), F(3,4): F(-45,64)}
        for beta in c.BETAS:
            coefficients = c.bessel_coefficients(beta)
            gaussian, odd = c._gaussian_bessel(beta)
            self.assertEqual(coefficients, c._ode_bessel(beta))
            self.assertEqual(coefficients, gaussian)
            self.assertEqual(odd, [F(0)]*6)
            self.assertEqual(coefficients[1], first[beta])
            self.assertTrue(all(type(x) is F for x in coefficients))
        self.assertEqual(c.bessel_coefficients(F(0), 0), [F(1)])

    def test_inverse_coefficients_and_known_constants(self):
        expected_d1 = {F(-1,4): F(5,128), F(0): F(3,32), F(3,4): F(45,128)}
        for beta in c.BETAS:
            d = c.inverse_coefficients(beta)
            self.assertEqual(d[0], expected_d1[beta])
            self.assertTrue(all(type(x) is F for x in d))
            self.assertEqual(len(d), 6)
        self.assertEqual(2*expected_d1[F(-1,4)]*12, F(15,16))
        self.assertEqual(2*expected_d1[F(3,4)]*12, F(135,16))
        self.assertEqual(2*expected_d1[F(0)], F(3,16))

    def test_failure_checks_survive_optimization(self):
        with self.assertRaises(c.CheckFailure):
            c._require(False, "sentinel")
        with mock.patch.object(c, "_ode_bessel", return_value=[F(0)]*7):
            with self.assertRaises(c.CheckFailure):
                c.exact_results()
        with mock.patch.object(c, "_inverse_residual", return_value=[F(1)]*7):
            with self.assertRaises(c.CheckFailure):
                c.inverse_coefficients(F(0))

    def test_full_document_and_numerical_labels(self):
        document = c.exact_results()
        self.assertEqual([x["terms_matched"] for x in document["oeis_prefix_checks"]], [54,63,69,74])
        self.assertEqual(len(document["families"]), 10)
        def check_no_floats(value):
            if isinstance(value, dict):
                for member in value.values():
                    check_no_floats(member)
            elif isinstance(value, list):
                for member in value:
                    check_no_floats(member)
            else:
                self.assertNotIsInstance(value, float)
        check_no_floats(document)
        for family in document["families"].values():
            self.assertEqual(family["thresholds"][-1]["status"], "not_found_through_bound")
            self.assertEqual(family["thresholds"][-1]["global_threshold"], "unresolved")
        self.assertEqual(c.json_bytes(document), c.json_bytes(c.exact_results()))
        self.assertEqual(json.loads(c.json_bytes(document)), document)
        numerical = c.numerical_illustrations(document)
        self.assertIs(numerical["interval_certified"], False)
        self.assertIs(numerical["onset_certified"], False)
        self.assertIs(numerical["error_bound_certified"], False)
        self.assertEqual(len(numerical["rows"]), 40)
        self.assertEqual(len(numerical["capped_ratio_residuals"]), 16)
        self.assertIn("rounded explicitly", numerical["arithmetic"])
        self.assertIn("No threshold rounding", numerical["warning"])


class OutputSafetyTests(unittest.TestCase):
    def setUp(self):
        # All tests write only below the companion directory.
        self.temp = tempfile.TemporaryDirectory(prefix="test_", dir=str(ROOT))
        self.parent = Path(self.temp.name)

    def tearDown(self):
        self.temp.cleanup()

    def test_write_no_clobber_and_digest_integrity(self):
        destination = Path(c.write_run(str(self.parent), "fresh_run"))
        original = {x.name:x.read_bytes() for x in destination.iterdir()}
        self.assertEqual(set(original), {"exact_results.json", "numerical_illustrations.json", "SHA256SUMS", "COMPLETE.json"})
        with self.assertRaises(FileExistsError):
            c.write_run(str(self.parent), "fresh_run")
        self.assertEqual(original, {x.name:x.read_bytes() for x in destination.iterdir()})
        for line in original["SHA256SUMS"].decode().splitlines():
            digest, name = line.split("  ")
            self.assertEqual(digest, hashlib.sha256(original[name]).hexdigest())
        self.assertTrue(json.loads(original["COMPLETE.json"])["complete"])
        self.assertEqual(destination.stat().st_mode & 0o777, 0o700)
        for item in destination.iterdir():
            self.assertEqual(item.stat().st_mode & 0o777, 0o600)

    def test_directory_file_and_dangling_symlink_destinations_rejected(self):
        (self.parent/"directory").mkdir()
        (self.parent/"file").write_text("untouched")
        (self.parent/"dangling").symlink_to(self.parent/"absent")
        for name in ("directory", "file", "dangling"):
            with self.assertRaises(FileExistsError):
                c.write_run(str(self.parent), name)
        self.assertEqual((self.parent/"file").read_text(), "untouched")
        self.assertFalse((self.parent/"absent").exists())
        self.assertEqual(list((self.parent/"directory").iterdir()), [])

    def test_parent_and_ancestor_symlinks_rejected(self):
        real = self.parent/"real"
        real.mkdir(mode=0o700)
        (real/"inner").mkdir(mode=0o700)
        (self.parent/"link").symlink_to(real, target_is_directory=True)
        for selected in (self.parent/"link", self.parent/"link"/"inner"):
            with self.assertRaises(OSError):
                c.write_run(str(selected), "rejected")
        self.assertFalse((real/"rejected").exists())
        self.assertFalse((real/"inner"/"rejected").exists())

    def test_bad_parent_names_and_missing_parent(self):
        for parent in (".", "relative", "/", str(self.parent)+"/", str(self.parent)+"/../x", str(self.parent)+"//x"):
            with self.assertRaises(ValueError):
                c.write_run(parent, "rejected")
        with self.assertRaises(FileNotFoundError):
            c.write_run(str(self.parent/"missing"), "rejected")
        for name in ("", ".", "..", "../escape", "/absolute", "a/b", "x"*65, "a b", "é"):
            with self.assertRaises(ValueError):
                c.write_run(str(self.parent), name)

    def test_group_or_world_writable_parent_is_rejected(self):
        unsafe = self.parent/"unsafe"
        unsafe.mkdir(mode=0o700)
        for mode in (0o720, 0o702, 0o777):
            unsafe.chmod(mode)
            with self.assertRaises(PermissionError):
                c.write_run(str(unsafe), "rejected")
        unsafe.chmod(0o700)
        self.assertEqual(list(unsafe.iterdir()), [])

    def test_failed_run_has_no_completion_record(self):
        with mock.patch.object(c, "exact_results", side_effect=c.CheckFailure("deliberate")):
            with self.assertRaises(c.CheckFailure):
                c.write_run(str(self.parent), "incomplete")
        self.assertTrue((self.parent/"incomplete").is_dir())
        self.assertFalse((self.parent/"incomplete"/"COMPLETE.json").exists())
        with self.assertRaises(FileExistsError):
            c.write_run(str(self.parent), "incomplete")

    def test_cli_rejects_workload_precision_and_existing_output(self):
        environment = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
        for args in (("--n-max", "1000000"), ("--precision", "1000")):
            result = subprocess.run([sys.executable, "-B", str(ROOT/"companion.py"), *args],
                                    capture_output=True, text=True, env=environment, timeout=20)
            self.assertNotEqual(result.returncode, 0)
        args = [sys.executable, "-B", str(ROOT/"companion.py"), "--output-parent", str(self.parent), "--output-name", "cli"]
        first = subprocess.run(args, capture_output=True, text=True, env=environment, timeout=20)
        self.assertEqual(first.returncode, 0, first.stderr)
        repeated = subprocess.run(args, capture_output=True, text=True, env=environment, timeout=20)
        self.assertEqual(repeated.returncode, 2)


if __name__ == "__main__":
    unittest.main(verbosity=2)
