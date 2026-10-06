#!/usr/bin/env python3
"""Standard-library mathematical, CLI, and exclusive-output regression tests."""
from __future__ import annotations

import argparse
from contextlib import redirect_stdout
from fractions import Fraction
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
import exact_checks as exact
import numerical_diagnostics as numerical
from release_tools import fresh_file, parent_handle

HERE = Path(__file__).resolve().parent


class CompanionTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='report154-tests-')
        self.root = Path(self.temp.name)

    def tearDown(self):
        self.temp.cleanup()

    def invoke(self, *args, optimized=False):
        command = [sys.executable, '-B'] + (['-O'] if optimized else [])
        return subprocess.run(command + [str(HERE / 'exact_checks.py'), *args],
                              cwd=self.root, text=True, capture_output=True, timeout=60)

    def test_full_exact_release_scope(self):
        result = exact.run_checks()
        self.assertEqual(result['status'], 'pass')
        self.assertEqual(result['payload']['total_exact_checks'], 11993)
        self.assertEqual(result['payload']['contraction_term_counts'], [1, 2, 5, 11, 22, 42, 77])

    def test_all_official_terms(self):
        rows = exact.stirling_first_rows(16)
        self.assertEqual(tuple(exact.moment_count(rows[n], n) for n in range(17)), exact.OFFICIAL_PREFIX)

    def test_empty_label_and_moment_edges(self):
        first = exact.stirling_first_rows(12)
        second = exact.stirling_second_rows(12)
        derivatives = exact.derivative_product_rows(11, 11)
        for k in range(12):
            self.assertEqual(exact.moment_count(first[0], k), 1)
            self.assertEqual(exact.stirling_product_count(first, second, 0, k), 1)
            self.assertEqual(derivatives[0][k], 1)
        for n in range(12):
            self.assertEqual(exact.moment_count(first[n], 0), exact.factorial(n))
            self.assertEqual(derivatives[n][0], exact.factorial(n))

    def test_contractions_displayed_and_sixth_order(self):
        coefficients = exact.contraction_partitions(6)
        _, contracted = exact.exponential_recurrence(6)
        self.assertEqual(coefficients[1:3], exact.known_first_coefficients(12))
        self.assertEqual(coefficients[6], contracted[12])
        self.assertEqual(len(coefficients[6]), 77)

    def test_bernoulli_fourteenth_order(self):
        self.assertEqual(exact.bernoulli_recurrence(14), exact.bernoulli_stirling(14))

    def test_threshold_equality_and_between(self):
        sequence = [1, 2, 13, 161]
        self.assertEqual((exact.threshold_ge(sequence, 13), exact.threshold_gt(sequence, 13)), (2, 3))
        self.assertEqual((exact.threshold_ge(sequence, Fraction(25, 2)),
                          exact.threshold_gt(sequence, Fraction(25, 2))), (2, 2))

    def test_threshold_outside_finite_scope_rejected(self):
        with self.assertRaises(ValueError):
            exact.threshold_gt([1, 2], 2)
        with self.assertRaises(ValueError):
            exact.threshold_ge([1, 2], 3)

    def test_fraction_rounding_integer_and_negative_edges(self):
        for value, expected in ((Fraction(3), (3, 3)), (Fraction(7, 2), (3, 4)),
                                (Fraction(-7, 2), (-4, -3)), (Fraction(-3), (-3, -3))):
            self.assertEqual((exact.floor_fraction(value), exact.ceil_fraction(value)), expected)

    def test_require_is_an_active_exception(self):
        with self.assertRaises(exact.CheckFailure):
            exact.require(False, 'deliberate failure')

    def test_corrupt_official_prefix_is_detected(self):
        with patch.object(exact, 'OFFICIAL_PREFIX', (99,) + exact.OFFICIAL_PREFIX[1:]):
            with self.assertRaises(exact.CheckFailure):
                exact.run_checks(16, 2)

    def test_corrupt_sequence_route_is_detected(self):
        with patch.object(exact, 'stirling_product_count', return_value=-1):
            with self.assertRaises(exact.CheckFailure):
                exact.run_checks(16, 2)

    def test_corrupt_contraction_identity_is_detected(self):
        bad = exact.known_first_coefficients(4)
        bad[0][exact.monomial(4, {4: 1})] = Fraction(1, 9)
        with patch.object(exact, 'known_first_coefficients', return_value=bad):
            with self.assertRaises(exact.CheckFailure):
                exact.run_checks(16, 2)

    def test_direct_workload_bounds(self):
        for max_n, order in ((15, 6), (65, 6), (16, 1), (16, 7), (True, 6)):
            with self.assertRaises(exact.CheckFailure):
                exact.run_checks(max_n, order)

    def test_cli_workload_bounds(self):
        for args in (('--max-n', '65'), ('--max-n', '-1'), ('--order', '7'), ('--order', 'word')):
            result = self.invoke(*args)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, '')

    def test_default_stdout_only(self):
        result = self.invoke('--max-n', '16', '--order', '2')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout)['status'], 'pass')
        self.assertEqual(list(self.root.iterdir()), [])

    def test_normal_and_optimized_mathematics_agree(self):
        values = []
        for optimized in (False, True):
            result = self.invoke('--max-n', '16', '--order', '2', optimized=optimized)
            self.assertEqual(result.returncode, 0, result.stderr)
            values.append(json.loads(result.stdout))
        self.assertEqual(values[0]['mathematical_payload_sha256'], values[1]['mathematical_payload_sha256'])
        self.assertEqual(values[0]['payload'], values[1]['payload'])
        self.assertEqual([x['python_optimization'] for x in values], [0, 1])

    def test_optimized_validation_still_fails(self):
        command = [sys.executable, '-B', '-O', '-c',
                   'import exact_checks; exact_checks.require(False, "deliberate failure")']
        result = subprocess.run(command, cwd=HERE, text=True, capture_output=True, timeout=10)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('CheckFailure', result.stderr)

    def test_fresh_output_and_mode(self):
        output = self.root / 'fresh.json'
        result = self.invoke('--max-n', '16', '--order', '2', '--output', str(output))
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, '')
        self.assertEqual(json.loads(output.read_text())['status'], 'pass')
        self.assertEqual(output.stat().st_mode & 0o777, 0o600)

    def test_existing_regular_file_rejected_unchanged(self):
        output = self.root / 'existing'
        output.write_bytes(b'preserve me')
        with self.assertRaises(OSError):
            with fresh_file(output):
                self.fail('Existing output was opened')
        self.assertEqual(output.read_bytes(), b'preserve me')

    def test_existing_directory_rejected(self):
        output = self.root / 'directory'
        output.mkdir()
        with self.assertRaises(OSError):
            with fresh_file(output):
                self.fail('Directory was opened as output')

    def test_final_symlink_rejected_unchanged(self):
        target = self.root / 'target'
        target.write_bytes(b'preserve me')
        link = self.root / 'link'
        link.symlink_to(target)
        with self.assertRaises(OSError):
            with fresh_file(link):
                self.fail('Symlink output was opened')
        self.assertEqual(target.read_bytes(), b'preserve me')

    def test_dangling_symlink_rejected(self):
        link = self.root / 'dangling'
        link.symlink_to(self.root / 'absent')
        with self.assertRaises(OSError):
            with fresh_file(link):
                self.fail('Dangling output link was followed')
        self.assertFalse((self.root / 'absent').exists())

    def test_symlinked_parent_rejected(self):
        target = self.root / 'target'
        target.mkdir()
        link = self.root / 'alias'
        link.symlink_to(target, target_is_directory=True)
        with self.assertRaises(OSError):
            with fresh_file(link / 'output'):
                self.fail('Symlinked parent was followed')
        self.assertEqual(list(target.iterdir()), [])

    def test_symlinked_non_immediate_ancestor_rejected(self):
        target = self.root / 'target'
        (target / 'nested').mkdir(parents=True)
        link = self.root / 'alias'
        link.symlink_to(target, target_is_directory=True)
        with self.assertRaises(OSError):
            with fresh_file(link / 'nested' / 'output'):
                self.fail('Symlinked ancestor was followed')
        self.assertEqual(list((target / 'nested').iterdir()), [])

    def test_hardlinked_existing_output_rejected(self):
        original = self.root / 'original'
        original.write_bytes(b'preserve me')
        linked = self.root / 'linked'
        os.link(original, linked)
        with self.assertRaises(OSError):
            with fresh_file(linked):
                self.fail('Hardlinked existing target was opened')
        self.assertEqual(original.read_bytes(), b'preserve me')
        self.assertEqual(original.stat().st_nlink, 2)

    def test_parent_traversal_rejected(self):
        (self.root / 'directory').mkdir()
        with self.assertRaises(ValueError):
            with fresh_file(self.root / 'directory' / '..' / 'output'):
                self.fail('Parent traversal was accepted')
        self.assertFalse((self.root / 'output').exists())

    def test_missing_parent_is_not_created(self):
        with self.assertRaises(OSError):
            with fresh_file(self.root / 'absent' / 'output'):
                self.fail('Missing parent was created')
        self.assertFalse((self.root / 'absent').exists())

    def test_parent_descriptor_remains_pinned_after_rename(self):
        parent = self.root / 'parent'
        parent.mkdir()
        moved = self.root / 'moved'
        outside = self.root / 'outside'
        outside.mkdir()
        with parent_handle(parent / 'file') as (_, descriptor, leaf):
            parent.rename(moved)
            parent.symlink_to(outside, target_is_directory=True)
            fd = os.open(leaf, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                         0o600, dir_fd=descriptor)
            with os.fdopen(fd, 'wb') as stream:
                stream.write(b'pinned')
        self.assertEqual((moved / 'file').read_bytes(), b'pinned')
        self.assertEqual(list(outside.iterdir()), [])

    def test_emit_json_stdout_default(self):
        output = io.StringIO()
        with redirect_stdout(output):
            exact.emit_json({'answer': 42})
        self.assertEqual(json.loads(output.getvalue()), {'answer': 42})
        self.assertEqual(list(self.root.iterdir()), [])

    def test_optional_dependency_version_rejected(self):
        fake = type('WrongVersion', (), {'__version__': '0.0'})()
        with patch.dict(sys.modules, {'mpmath': fake}):
            with self.assertRaisesRegex(RuntimeError, 'mpmath==1.3.0'):
                numerical.checked_mpmath()

    def test_optional_dependency_missing_rejected(self):
        with patch.dict(sys.modules, {'mpmath': None}):
            with self.assertRaisesRegex(RuntimeError, 'no installation was attempted'):
                numerical.checked_mpmath()

    def test_numerical_workload_bounds(self):
        for digits, order in ((99, 6), (201, 6), (100, 1), (100, 7)):
            with self.assertRaises(exact.CheckFailure):
                numerical.run_diagnostics(digits, order)

    def test_numerical_exact_counts_independent_batch(self):
        pairs = ((20, 20), (20, 10), (50, 25))
        counts = numerical.exact_sample_counts(pairs)
        rows = exact.derivative_product_rows(50, 25)
        for n, k in pairs:
            self.assertEqual(counts[n, k], rows[n][k])


class RecordingResult(unittest.TestResult):
    def __init__(self):
        super().__init__()
        self.test_ids = []

    def startTest(self, test):
        self.test_ids.append(test.id().split('.')[-1])
        super().startTest(test)


def run_tests():
    result = RecordingResult()
    unittest.defaultTestLoader.loadTestsFromTestCase(CompanionTests).run(result)
    return {'schema': 'report154.companion-tests.v1', 'status': 'pass' if result.wasSuccessful() else 'fail',
            'python_optimization': sys.flags.optimize, 'test_count': result.testsRun,
            'tests': result.test_ids, 'failure_count': len(result.failures), 'error_count': len(result.errors),
            'failures': [{'test': test.id(), 'traceback': detail} for test, detail in result.failures],
            'errors': [{'test': test.id(), 'traceback': detail} for test, detail in result.errors],
            'scope': 'Functional regression tests and output-safety checks; no asymptotic certification.'}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', help='Create one fresh JSON file; existing paths are never replaced')
    args = parser.parse_args(argv)
    result = run_tests()
    try:
        exact.emit_json(result, args.output)
    except (OSError, ValueError, RuntimeError) as error:
        parser.exit(1, f'error: {error}\n')
    if result['status'] != 'pass':
        parser.exit(1)


if __name__ == '__main__':
    main()
