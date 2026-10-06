#!/usr/bin/env python3
"""Regression, mutation-sensitivity, optimization, and output-safety tests."""
import argparse
from fractions import Fraction as Q
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import verify


class CompanionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.work = tempfile.TemporaryDirectory(prefix="test-", dir=verify.RESULTS)
        cls.directory = Path(cls.work.name)
        cls.claims = verify.load_claims(verify.ROOT / "claims.json")

    @classmethod
    def tearDownClass(cls):
        cls.work.cleanup()

    def fresh(self, name):
        directory = self.directory / self._testMethodName
        directory.mkdir(exist_ok=True)
        return directory / name

    def execute(self, optimized, *arguments):
        command = [sys.executable] + (["-O"] if optimized else [])
        command += [str(verify.ROOT / "verify.py"), *map(str, arguments)]
        return subprocess.run(command, capture_output=True, text=True, timeout=180,
                              env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"})

    def test_complete_normal_and_optimized(self):
        data = []
        for optimized in (False, True):
            destination = self.fresh(f"complete-{optimized}.json")
            outcome = self.execute(optimized, "--output", destination)
            self.assertEqual(outcome.returncode, 0, outcome.stderr)
            payload = json.loads(outcome.stdout)
            self.assertEqual(payload["status"], "passed")
            self.assertEqual(payload["claims"], self.claims)
            self.assertEqual(json.loads(destination.read_text()), payload)
            data.append(payload)
        self.assertEqual(data[0], data[1], "Optimization must not change checks or output")

    def test_mutated_local_coefficient_rejected_normal_and_optimized(self):
        mutation = dict(self.claims, local_zero_relative_M="-9")
        source = self.fresh("mutated-claims.json")
        source.write_text(json.dumps(mutation))
        for optimized in (False, True):
            destination = self.fresh(f"must-not-exist-{optimized}.json")
            outcome = self.execute(optimized, "--claims", source, "--output", destination)
            self.assertNotEqual(outcome.returncode, 0)
            self.assertIn("Claim local_zero_relative_M", outcome.stderr)
            self.assertFalse(destination.exists())
        self.assertEqual(json.loads(source.read_text()), mutation)

    def test_mutated_inverse_coefficient_rejected_normal_and_optimized(self):
        mutation = dict(self.claims, inverse_connected_numerator="104/24")
        # Canonical rational form avoids rejection merely by input validation.
        mutation["inverse_connected_numerator"] = "13/3"
        source = self.fresh("mutated-claims.json")
        source.write_text(json.dumps(mutation))
        for optimized in (False, True):
            outcome = self.execute(optimized, "--claims", source)
            self.assertNotEqual(outcome.returncode, 0)
            self.assertIn("Claim inverse_connected_numerator", outcome.stderr)

    def test_mutated_root_count_changes_transfer(self):
        actual, _ = verify.algebra_checks([1, 3, 12, 58])
        self.assertNotEqual(actual["b2"], self.claims["b2"])
        self.assertNotEqual(actual["connected_first"], self.claims["connected_first"])
        with self.assertRaises(verify.VerificationError):
            verify.exact_equal(actual["b2"], self.claims["b2"], "Changed b2")

    def test_mutated_labeled_coefficient_rejected_normal_and_optimized(self):
        mutation = dict(self.claims, labeled_connected_first="-46/12")
        mutation["labeled_connected_first"] = "-23/6"
        source = self.fresh("mutated-weighted-claims.json")
        source.write_text(json.dumps(mutation))
        for optimized in (False, True):
            destination = self.fresh(f"must-not-exist-{optimized}.json")
            outcome = self.execute(optimized, "--claims", source, "--output", destination)
            self.assertNotEqual(outcome.returncode, 0)
            self.assertIn("Claim labeled_connected_first", outcome.stderr)
            self.assertFalse(destination.exists())

    def test_root_stabilizer_histograms(self):
        rows = verify.graph_checks()
        self.assertEqual([row["rooted_automorphism_order_histogram"] for row in rows[:3]],
                         [{1: 1}, {1: 1, 2: 2}, {1: 3, 2: 6, 6: 2}])

    def test_bounded_specializations(self):
        ordinary, _ = verify.algebra_checks([1, 3, 11, 58])
        weighted, _ = verify.bounded_weight_checks(verify.graph_checks(), ordinary)
        self.assertEqual(weighted["labeled_connected_first"], "-47/12")
        self.assertEqual(weighted["labeled_all_first"], "-41/12")
        self.assertEqual(weighted["asymmetric_connected_first"], "-17/4")
        self.assertEqual(weighted["asymmetric_all_first"], "-15/4")
        self.assertEqual(weighted["asymmetric_relative_first"], "-1/2")

    def test_explicit_exception_active(self):
        with self.assertRaises(verify.VerificationError):
            verify.require(False, "Always active")

    def test_poisson_exact_moments(self):
        self.assertEqual([verify.poisson_moment(k) for k in range(5)],
                         [Q(1), Q(3, 2), Q(15, 4), Q(93, 8), Q(681, 16)])

    def test_source_file_refused_and_unchanged(self):
        source = verify.ROOT / "verify.py"
        before = source.read_bytes()
        with self.assertRaises(verify.VerificationError):
            verify.write_new_json(source, {"bad": True})
        self.assertEqual(source.read_bytes(), before)

    def test_claim_file_refused_and_unchanged(self):
        source = verify.ROOT / "claims.json"
        before = source.read_bytes()
        with self.assertRaises(verify.VerificationError):
            verify.write_new_json(source, {"bad": True})
        self.assertEqual(source.read_bytes(), before)

    def test_input_inside_results_refused_and_unchanged(self):
        source = self.fresh("input.json")
        source.write_text(json.dumps(self.claims))
        before = source.read_bytes()
        with self.assertRaises(FileExistsError):
            verify.write_new_json(source, {"bad": True})
        self.assertEqual(source.read_bytes(), before)

    def test_existing_result_refused_and_unchanged(self):
        destination = self.fresh("already-there.json")
        verify.write_new_json(destination, {"sentinel": True})
        before = destination.read_bytes()
        with self.assertRaises(FileExistsError):
            verify.write_new_json(destination, {"bad": True})
        self.assertEqual(destination.read_bytes(), before)

    def test_outside_allowed_root_refused(self):
        destination = Path(tempfile.gettempdir()) / (self.directory.name+"-outside.json")
        self.assertFalse(destination.exists())
        with self.assertRaises(verify.VerificationError):
            verify.write_new_json(destination, {"bad": True})
        self.assertFalse(destination.exists())

    def test_parent_traversal_refused(self):
        destination = self.fresh("unused") / ".." / "traversal.json"
        with self.assertRaises(verify.VerificationError):
            verify.write_new_json(destination, {"bad": True})
        self.assertFalse(self.fresh("traversal.json").exists())

    def test_symlink_output_file_refused(self):
        target = self.fresh("target.json")
        target.write_text("sentinel")
        link = self.fresh("link.json")
        link.symlink_to(target)
        with self.assertRaises(OSError):
            verify.write_new_json(link, {"bad": True})
        self.assertEqual(target.read_text(), "sentinel")

    def test_dangling_symlink_output_refused(self):
        target = self.fresh("missing.json")
        link = self.fresh("dangling.json")
        link.symlink_to(target)
        with self.assertRaises(OSError):
            verify.write_new_json(link, {"bad": True})
        self.assertFalse(target.exists())

    def test_symlink_output_parent_refused(self):
        real = self.fresh("real-directory")
        real.mkdir()
        link = self.fresh("symlink-directory")
        link.symlink_to(real, target_is_directory=True)
        with self.assertRaises(OSError):
            verify.write_new_json(link / "bad.json", {"bad": True})
        self.assertFalse((real / "bad.json").exists())

    def test_symlink_claim_input_refused(self):
        link = self.fresh("claims-link.json")
        link.symlink_to(verify.ROOT / "claims.json")
        with self.assertRaises(verify.VerificationError):
            verify.load_claims(link)

    def test_symlink_claim_parent_refused(self):
        real = self.fresh("real-input-directory")
        real.mkdir()
        source = real / "claims.json"
        source.write_text(json.dumps(self.claims))
        link = self.fresh("symlink-input-directory")
        link.symlink_to(real, target_is_directory=True)
        with self.assertRaises(verify.VerificationError):
            verify.load_claims(link / "claims.json")

    def test_fifo_claim_input_rejected_without_blocking(self):
        fifo = self.fresh("claims-fifo.json")
        os.mkfifo(fifo)
        for optimized in (False, True):
            command = [sys.executable] + (["-O"] if optimized else [])
            command += [str(verify.ROOT / "verify.py"), "--claims", str(fifo)]
            outcome = subprocess.run(command, capture_output=True, text=True, timeout=3)
            self.assertNotEqual(outcome.returncode, 0)
            self.assertIn("must be a regular file", outcome.stderr)

    def test_claim_parent_swap_cannot_redirect_read(self):
        original = self.fresh("switchable")
        original.mkdir()
        (original / "claims.json").write_text('{"marker":"1"}')
        alternate = self.fresh("alternate")
        alternate.mkdir()
        (alternate / "claims.json").write_text('{"marker":"2"}')
        moved = self.fresh("pinned-original")
        original_open = os.open
        swapped = False

        def swap_before_final_open(path, flags, *args, **kwargs):
            nonlocal swapped
            if path == "claims.json" and "dir_fd" in kwargs:
                original.rename(moved)
                original.symlink_to(alternate, target_is_directory=True)
                swapped = True
            return original_open(path, flags, *args, **kwargs)

        with patch.object(verify.os, "open", side_effect=swap_before_final_open):
            actual = verify.load_claims(original / "claims.json")
        self.assertTrue(swapped)
        self.assertEqual(actual, {"marker": "1"})

    def test_noncanonical_claim_rejected(self):
        source = self.fresh("noncanonical.json")
        source.write_text('{"test":"2/4"}')
        with self.assertRaises(verify.VerificationError):
            verify.load_claims(source)

    def test_new_output_exact_json(self):
        destination = self.fresh("valid.json")
        verify.write_new_json(destination, {"rational": "103/24"})
        self.assertEqual(json.loads(destination.read_text()), {"rational": "103/24"})


class RecordedResult(unittest.TextTestResult):
    def __init__(self, *arguments, **keywords):
        super().__init__(*arguments, **keywords)
        self.success_names = []

    def addSuccess(self, test):
        super().addSuccess(test)
        self.success_names.append(test.id())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="New .json file under results/")
    arguments = parser.parse_args()
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(CompanionTests)
    result = unittest.TextTestRunner(verbosity=2, resultclass=RecordedResult).run(suite)
    summary = {"schema": "report152-companion-tests-v2", "status": "passed" if result.wasSuccessful() else "failed",
               "runner_optimization": sys.flags.optimize, "tests_run": result.testsRun,
               "passed": result.success_names, "failures": [test.id() for test, _ in result.failures],
               "errors": [test.id() for test, _ in result.errors],
               "subprocess_modes": ["normal", "-O"],
               "scope": "Finite diagnostics, mutation sensitivity, and output safety; not an analytic proof"}
    if arguments.output:
        verify.write_new_json(arguments.output, summary)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    sys.exit(main())
