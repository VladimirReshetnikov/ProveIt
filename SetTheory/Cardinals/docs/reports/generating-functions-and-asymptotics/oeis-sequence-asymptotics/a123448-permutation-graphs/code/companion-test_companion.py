#!/usr/bin/env python3
"""Mathematical regression, mutation, optimized-mode and safe-publication tests."""
from __future__ import annotations

import argparse
import ast
from fractions import Fraction as Q
import itertools
import json
from math import factorial
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import enumeration
import safe_io
import verify


class CompanionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.work = tempfile.TemporaryDirectory(prefix="test-", dir=verify.RESULTS)
        cls.directory = Path(cls.work.name)
        cls.claims = verify.load_claims(verify.ROOT / "claims.json")
        cls.inputs = verify.load_json(verify.ROOT / "inputs.json")
        cls.rows = verify.validate_inputs(cls.inputs)
        cls.sampling_rows = verify.validate_sampling_inputs(cls.inputs)

    @classmethod
    def tearDownClass(cls):
        cls.work.cleanup()

    def fresh(self, name):
        directory = self.directory / self._testMethodName
        directory.mkdir(exist_ok=True)
        return directory / name

    def execute(self, optimized, *arguments):
        command = [sys.executable, "-B"] + (["-O"] if optimized else [])
        command += [str(verify.ROOT / "verify.py"), *map(str, arguments)]
        return subprocess.run(command, capture_output=True, text=True, timeout=120,
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
            self.assertEqual(payload["enumeration_checks"]["through_n"], 6)
            data.append(outcome.stdout)
        self.assertEqual(data[0], data[1], "Optimization must not change deterministic checks")

    def test_algebra_only_and_single_enumerator_options(self):
        for arguments, count in ((("--enumerate-through", "0"), 0),
                                 (("--enumerator", "degree", "--enumerate-through", "3"), 3),
                                 (("--enumerator", "refined", "--enumerate-through", "3"), 3)):
            outcome = self.execute(False, *arguments)
            self.assertEqual(outcome.returncode, 0, outcome.stderr)
            data = json.loads(outcome.stdout)
            self.assertEqual(data["enumeration_checks"]["through_n"], count)

    def test_mutated_claims_fail_in_both_modes_without_publication(self):
        for key in ("h7", "log_a_b2", "inverse_second_shift_numerator", "r9", "g6", "tv7", "c7"):
            mutation = dict(self.claims)
            mutation[key] = str(Q(mutation[key])+1)
            source = self.fresh(f"changed-{key}.json")
            source.write_text(json.dumps(mutation))
            before = source.read_bytes()
            for optimized in (False, True):
                destination = self.fresh(f"forbidden-{key}-{optimized}.json")
                outcome = self.execute(optimized, "--claims", source, "--output", destination)
                self.assertNotEqual(outcome.returncode, 0)
                self.assertIn(f"Claim {key}", outcome.stderr)
                self.assertFalse(destination.exists())
            self.assertEqual(source.read_bytes(), before)

    def test_mutated_fixed_input_rejected_in_both_modes(self):
        mutation = json.loads(json.dumps(self.inputs))
        mutation["rows"][8]["a"] += 1
        source = self.fresh("changed-input.json")
        source.write_text(json.dumps(mutation))
        for optimized in (False, True):
            outcome = self.execute(optimized, "--inputs", source)
            self.assertNotEqual(outcome.returncode, 0)
            self.assertIn("Claim a9", outcome.stderr)

    def test_exact_dependency_on_a9_and_r8(self):
        baseline, _ = verify.direct_coefficients(self.rows)
        for index, field in ((8, "a"), (7, "r")):
            rows = [row.copy() for row in self.rows]
            rows[index][field] += 1
            changed, _ = verify.direct_coefficients(rows)
            independent, _ = verify.independent_coefficients(rows)
            self.assertEqual(changed, independent)
            self.assertEqual(changed[:7], baseline[:7])
            self.assertNotEqual(changed[7], baseline[7])

    def test_low_order_stabilization_and_denominators(self):
        full, details = verify.direct_coefficients(self.rows)
        for order in range(8):
            h, _ = verify.direct_coefficients(self.rows, order)
            independent, _ = verify.independent_coefficients(self.rows, order)
            self.assertEqual(h, full[:order+1])
            self.assertEqual(h, independent)
            self.assertTrue(all((factorial(k)*value).denominator == 1 for k, value in enumerate(h)))
        self.assertTrue(all(Q(value).denominator == 1 for value in details["exponent"]))
        self.assertTrue(all(Q(value).denominator == 1 for value in details["prefactor"]))

    def test_formal_log_and_inverse_residuals(self):
        actual, diagnostics = verify.algebra_checks(self.rows)
        self.assertEqual(actual["log_a_b1"], "-47/12")
        self.assertEqual(actual["log_a_b2"], "-9")
        inverse = diagnostics["formal_inverse"]
        self.assertEqual(inverse["constant_residual"], {})
        self.assertEqual(inverse["second_shift_1_over_u_residual"], {})
        self.assertEqual(inverse["first_shift_1_over_u_residual"], {"-2,2": "1/2", "0,0": "-97/24"})
        self.assertEqual(inverse["second_shift_1_over_u_squared_residual"],
                         {"-4,3": "1/2", "-3,3": "1/6", "-2,1": "-97/24", "-1,1": "-97/24", "0,0": "-11"})

    def test_bernoulli_recurrence(self):
        self.assertEqual(verify.bernoulli_numbers(8),
                         list(map(Q, [1, "-1/2", "1/6", 0, "-1/30", 0, "1/42", 0, "-1/30"])))

    def test_series_preconditions(self):
        s = verify.Series(4)
        for action in (lambda: s.reciprocal([0, 1]), lambda: s.exp_zero([1]),
                       lambda: s.log_one([2]), lambda: s.compose([1, 2], [1, 1]),
                       lambda: s.power([1], -1)):
            with self.assertRaises(verify.VerificationError):
                action()

    def test_every_permutation_visited_by_both_enumerators(self):
        for row in self.rows[:6]:
            for function in (enumeration.enumerate_degree, enumeration.enumerate_refined):
                result = function(row["n"])
                self.assertEqual(result, {**row, "permutations": factorial(row["n"])})

    def test_sampling_inputs_replay_through_seven(self):
        for row in self.sampling_rows[:7]:
            outputs = []
            for function in (enumeration.enumerate_degree, enumeration.enumerate_refined):
                result = function(row["n"], sampling=True)
                self.assertEqual(result["b"], row["b"])
                self.assertEqual(result["c"], row["c"])
                self.assertEqual(result["permutations"], factorial(row["n"]))
                outputs.append(result)
            self.assertEqual(outputs[0], outputs[1])

    def test_sampling_series_and_marked_context_dependency(self):
        h, _ = verify.direct_coefficients(self.rows)
        baseline, diagnostics = verify.sampling_algebra_checks(self.sampling_rows, h)
        self.assertEqual([baseline[f"tv{k}"] for k in range(1, 8)],
                         ["4", "-15", "169/3", "215/2", "26449/15", "232253/10", "101570743/315"])
        mutation = [row.copy() for row in self.sampling_rows]
        mutation[6]["c"] = 0
        changed, _ = verify.sampling_algebra_checks(mutation, h)
        self.assertEqual(Q(baseline["g6"])-Q(changed["g6"]), 2)
        self.assertEqual(Q(baseline["tv7"])-Q(changed["tv7"]), 8)
        for k in range(1, 7):
            self.assertEqual(baseline[f"tv{k}"], changed[f"tv{k}"])
        self.assertEqual(diagnostics["TV_quotient_recurrence_residual"], ["0"]*8)

    def test_sampling_input_mutation_rejected_in_both_modes(self):
        mutation = json.loads(json.dumps(self.inputs))
        mutation["sampling_rows"][6]["c"] = 0
        source = self.fresh("changed-sampling.json")
        source.write_text(json.dumps(mutation))
        for optimized in (False, True):
            outcome = self.execute(optimized, "--inputs", source)
            self.assertNotEqual(outcome.returncode, 0)
            self.assertIn("Claim c7", outcome.stderr)

    def test_enumerator_invalid_inputs(self):
        for function in (enumeration.enumerate_degree, enumeration.enumerate_refined):
            for invalid in (0, -1, True, 2.5, "4"):
                with self.assertRaises(ValueError):
                    function(invalid)

    def test_twin_reductions_against_bruteforce_all_graphs_through_four(self):
        for n in range(1, 5):
            edges = list(itertools.combinations(range(n), 2))
            orders = list(itertools.permutations(range(n)))
            for mask in range(1 << len(edges)):
                rows = [0]*n
                for bit, (left, right) in enumerate(edges):
                    if mask >> bit & 1:
                        rows[left] |= 1 << right
                        rows[right] |= 1 << left
                automorphisms = [p for p in orders if all(
                    ((rows[i] >> j) & 1) == ((rows[p[i]] >> p[j]) & 1)
                    for i, j in edges)]
                orbits = {frozenset(p[v] for p in automorphisms) for v in range(n)}
                key, aut, roots = enumeration._refined_canonical(rows, enumeration._refined_partition(rows))
                self.assertEqual(aut, len(automorphisms))
                self.assertEqual(roots, len(orbits))
                root_keys = set()
                for root in range(n):
                    signature, groups = enumeration._degree_blocks(rows, root)
                    best, _ = enumeration._degree_minimum(rows, groups)
                    root_keys.add((signature, best))
                self.assertEqual(len(root_keys), len(orbits))

    def test_checks_do_not_use_assert_statements(self):
        for path in verify.ROOT.glob("*.py"):
            parsed = ast.parse(path.read_text())
            self.assertFalse(any(isinstance(node, ast.Assert) for node in ast.walk(parsed)), path.name)
        with self.assertRaises(verify.VerificationError):
            verify.require(False, "Active in every optimization mode")

    def test_existing_output_and_input_preserved(self):
        destination = self.fresh("existing.json")
        destination.write_text("sentinel")
        with self.assertRaises(FileExistsError):
            verify.write_new_json(destination, {"changed": True})
        self.assertEqual(destination.read_text(), "sentinel")

    def test_source_and_fixed_input_output_refused(self):
        for name in ("verify.py", "claims.json", "inputs.json"):
            destination = verify.ROOT / name
            before = destination.read_bytes()
            with self.assertRaises(verify.VerificationError):
                verify.write_new_json(destination, {})
            self.assertEqual(destination.read_bytes(), before)

    def test_outside_results_and_parent_traversal_refused(self):
        targets = [self.directory.parent.parent / "outside.json", self.fresh("unused") / ".." / "bad.json"]
        for destination in targets:
            with self.assertRaises(verify.VerificationError):
                verify.write_new_json(destination, {})

    def test_output_requires_json_and_existing_parents(self):
        with self.assertRaises(verify.VerificationError):
            verify.write_new_json(self.fresh("wrong.txt"), {})
        with self.assertRaises(OSError):
            verify.write_new_json(self.fresh("missing") / "out.json", {})
        self.assertFalse(self.fresh("missing").exists())

    def test_symlink_and_dangling_output_refused(self):
        target = self.fresh("target.json")
        target.write_text("sentinel")
        missing = self.fresh("missing.json")
        for name, real in (("link.json", target), ("dangling.json", missing)):
            link = self.fresh(name)
            link.symlink_to(real)
            with self.assertRaises(FileExistsError):
                verify.write_new_json(link, {})
        self.assertEqual(target.read_text(), "sentinel")
        self.assertFalse(missing.exists())

    def test_output_symlink_parent_refused(self):
        real = self.fresh("real")
        real.mkdir()
        link = self.fresh("parent-link")
        link.symlink_to(real, target_is_directory=True)
        with self.assertRaises(OSError):
            verify.write_new_json(link / "bad.json", {})
        self.assertEqual(list(real.iterdir()), [])

    def test_output_fifo_and_directory_refused(self):
        fifo, directory = self.fresh("fifo.json"), self.fresh("directory.json")
        os.mkfifo(fifo)
        directory.mkdir()
        for target in (fifo, directory):
            with self.assertRaises(FileExistsError):
                verify.write_new_json(target, {})

    def test_input_symlink_and_parent_symlink_refused(self):
        real = self.fresh("real")
        real.mkdir()
        source = real / "input.json"
        source.write_text("{}")
        direct = self.fresh("direct.json")
        direct.symlink_to(source)
        parent = self.fresh("parent")
        parent.symlink_to(real, target_is_directory=True)
        for path in (direct, parent / "input.json"):
            with self.assertRaises(verify.VerificationError):
                verify.load_json(path)

    def test_fifo_input_nonblocking_in_both_modes(self):
        fifo = self.fresh("fifo.json")
        os.mkfifo(fifo)
        for optimized in (False, True):
            command = [sys.executable, "-B"] + (["-O"] if optimized else [])
            command += [str(verify.ROOT / "verify.py"), "--claims", str(fifo)]
            outcome = subprocess.run(command, capture_output=True, text=True, timeout=3)
            self.assertNotEqual(outcome.returncode, 0)
            self.assertIn("must be a regular file", outcome.stderr)

    def test_directory_and_large_input_rejected(self):
        with self.assertRaises(verify.VerificationError):
            verify.load_json(self.directory)
        source = self.fresh("large.json")
        source.write_bytes(b" "*(safe_io.MAX_INPUT_BYTES+1))
        with self.assertRaises(verify.VerificationError):
            verify.load_json(source)

    def test_duplicate_nonfinite_and_noncanonical_claims_rejected(self):
        for i, text in enumerate(('{"x":"1", "x":"2"}', '{"x":NaN}', '{"x":"2/4"}', '{"x":1}')):
            source = self.fresh(f"invalid-{i}.json")
            source.write_text(text)
            with self.assertRaises(verify.VerificationError):
                verify.load_claims(source)

    def test_boolean_fixed_count_rejected(self):
        mutation = json.loads(json.dumps(self.inputs))
        mutation["rows"][0]["a"] = True
        with self.assertRaises(verify.VerificationError):
            verify.validate_inputs(mutation)

    def test_input_parent_swap_cannot_redirect(self):
        original = self.fresh("original")
        original.mkdir()
        (original / "value.json").write_text('{"marker":1}')
        alternate = self.fresh("alternate")
        alternate.mkdir()
        (alternate / "value.json").write_text('{"marker":2}')
        moved = self.fresh("pinned")
        real_open = os.open
        swapped = False

        def swap(path, flags, *args, **kwargs):
            nonlocal swapped
            if path == "value.json" and "dir_fd" in kwargs:
                original.rename(moved)
                original.symlink_to(alternate, target_is_directory=True)
                swapped = True
            return real_open(path, flags, *args, **kwargs)

        with patch.object(safe_io.os, "open", side_effect=swap):
            result = verify.load_json(original / "value.json")
        self.assertTrue(swapped)
        self.assertEqual(result, {"marker": 1})

    def test_output_parent_swap_cannot_redirect(self):
        original, alternate, moved = self.fresh("original"), self.fresh("alternate"), self.fresh("pinned")
        original.mkdir()
        alternate.mkdir()
        real_open = os.open
        swapped = False

        def swap(path, flags, *args, **kwargs):
            nonlocal swapped
            if isinstance(path, str) and path.startswith(".report153-") and "dir_fd" in kwargs:
                original.rename(moved)
                original.symlink_to(alternate, target_is_directory=True)
                swapped = True
            return real_open(path, flags, *args, **kwargs)

        with patch.object(safe_io.os, "open", side_effect=swap):
            verify.write_new_json(original / "out.json", {"pinned": True})
        self.assertTrue(swapped)
        self.assertEqual(json.loads((moved / "out.json").read_text()), {"pinned": True})
        self.assertEqual(list(alternate.iterdir()), [])

    def test_failed_write_exposes_no_partial_destination(self):
        target = self.fresh("out.json")
        with patch.object(safe_io.os, "fsync", side_effect=OSError("simulated write failure")):
            with self.assertRaises(OSError):
                verify.write_new_json(target, {"complete": True})
        self.assertFalse(target.exists())
        self.assertEqual(list(target.parent.iterdir()), [])

    def test_racing_publication_never_clobbers(self):
        target = self.fresh("out.json")
        real_link = os.link

        def race(source, destination, *args, **kwargs):
            target.write_text("racing sentinel")
            return real_link(source, destination, *args, **kwargs)

        with patch.object(safe_io.os, "link", side_effect=race):
            with self.assertRaises(FileExistsError):
                verify.write_new_json(target, {"overwrite": True})
        self.assertEqual(target.read_text(), "racing sentinel")
        self.assertEqual(list(target.parent.iterdir()), [target])

    def test_atomic_publication_sees_complete_json_only(self):
        target = self.fresh("out.json")
        data = {"rational": "97/24"}
        real_link = os.link
        observed = []

        def check(source, destination, *args, **kwargs):
            self.assertFalse(target.exists())
            observed.append(json.loads((target.parent / source).read_text()))
            return real_link(source, destination, *args, **kwargs)

        with patch.object(safe_io.os, "link", side_effect=check):
            verify.write_new_json(target, data)
        self.assertEqual(observed, [data])
        self.assertEqual(target.read_text(), safe_io.encoded_json(data))
        self.assertEqual(list(target.parent.iterdir()), [target])


class RecordedResult(unittest.TextTestResult):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.success_names = []

    def addSuccess(self, test):
        super().addSuccess(test)
        self.success_names.append(test.id())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Unused .json path inside companion/results/")
    args = parser.parse_args()
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(CompanionTests)
    result = unittest.TextTestRunner(verbosity=2, resultclass=RecordedResult).run(suite)
    summary = {"schema": "report153-companion-tests-v2", "status": "passed" if result.wasSuccessful() else "failed",
               "runner_optimization": sys.flags.optimize, "tests_run": result.testsRun,
               "passed": result.success_names, "failures": [test.id() for test, _ in result.failures],
               "errors": [test.id() for test, _ in result.errors],
               "subprocess_modes": ["normal", "-O"],
               "scope": "Finite algebra/enumeration, mutation sensitivity, optimization invariance and atomic output safety"}
    try:
        if args.output:
            verify.write_new_json(args.output, summary)
        print(safe_io.encoded_json(summary), end="")
    except (verify.VerificationError, ValueError, OSError) as exc:
        print(f"Test result publication failed: {exc}", file=sys.stderr)
        return 1
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    sys.exit(main())
