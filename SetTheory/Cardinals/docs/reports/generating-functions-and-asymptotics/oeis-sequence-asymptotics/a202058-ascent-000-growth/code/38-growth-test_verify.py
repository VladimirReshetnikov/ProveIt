#!/usr/bin/env python3
"""Fail-closed verifier regression tests, including optimized Python runs."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import verify

HERE = Path(__file__).resolve().parent


class VerifierTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.path = Path(self.temporary.name) / 'input.txt'

    def write(self, content):
        self.path.write_text(content)
        return self.path

    def test_valid_exact_table(self):
        values = verify.exact_file(self.write('  # comment\n0 1\n1 1\n2 2\n'))
        self.assertEqual(values, {0: 1, 1: 1, 2: 2})
        verify.contiguous_indices(values, 0, 2, 'fixture')

    def test_exact_parser_rejects_bad_rows(self):
        cases = {
            'empty': '',
            'comments_only': '# no data\n',
            'duplicate': '0 1\n0 1\n',
            'duplicate_leading_zero': '0 1\n00 1\n',
            'negative_index': '-1 1\n',
            'negative_value': '0 -1\n',
            'zero_value': '0 0\n',
            'noninteger_index': '0.5 1\n',
            'noninteger_value': '0 1.5\n',
            'missing_column': '0\n',
            'extra_column': '0 1 2\n',
        }
        for name, content in cases.items():
            with self.subTest(case=name), self.assertRaises(verify.VerificationError):
                verify.exact_file(self.write(content))

    def test_cli_rejects_incomplete_or_incorrect_rebuilds_in_both_modes(self):
        good = '0 1\n1 1\n2 2\n3 4\n4 10\n'
        cases = {
            'empty': '',
            'truncated': '0 1\n1 1\n2 2\n3 4\n',
            'gap': '0 1\n1 1\n3 4\n4 10\n',
            'duplicate': good + '4 10\n',
            'wrong_value': good.replace('4 10', '4 11'),
            'negative': good.replace('3 4', '3 -4'),
            'noninteger': good.replace('3 4', '3 4.0'),
            'malformed': good.replace('3 4', '3 4 5'),
        }
        for flags in ([], ['-O']):
            command = [sys.executable, *flags, str(HERE / 'verify.py'),
                       '--rebuilt', str(self.path), '--expected-max', '4']
            for name, content in cases.items():
                with self.subTest(mode=flags, case=name):
                    self.write(content)
                    result = subprocess.run(command, capture_output=True, text=True)
                    self.assertNotEqual(result.returncode, 0, result.stdout)
                    self.assertIn('Verification failed:', result.stderr)
                    self.assertNotIn('Fresh GMP transfer agrees', result.stdout)
            with self.subTest(mode=flags, case='valid'):
                self.write(good)
                result = subprocess.run(command, capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn('Fresh GMP transfer agrees on all indices 0..4', result.stdout)
            with self.subTest(mode=flags, case='empty_filename'):
                empty_command = command.copy()
                empty_command[empty_command.index('--rebuilt') + 1] = ''
                result = subprocess.run(empty_command, capture_output=True, text=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('Verification failed:', result.stderr)
            with self.subTest(mode=flags, case='missing_expected_max'):
                result = subprocess.run(command[:-2], capture_output=True, text=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('must be supplied together', result.stderr)

    def test_numerical_rows_are_unique_contiguous_finite_and_positive(self):
        rows = [f'{n} 0 1 1 1\n' for n in range(1, 1201)]
        values = verify.numerical_file(self.write(''.join(rows)))
        self.assertEqual(len(values), 1200)
        cases = {
            'empty': '',
            'truncated': ''.join(rows[:-1]),
            'gap': ''.join(rows[:600] + rows[601:]),
            'duplicate': ''.join(rows[:-1] + [rows[0]]),
            'negative_index': '-1 0 1 1 1\n' + ''.join(rows[1:]),
            'noninteger_index': '1.0 0 1 1 1\n' + ''.join(rows[1:]),
            'nan_ratio': '1 0 NaN 1 1\n' + ''.join(rows[1:]),
            'infinite_ratio': '1 0 Infinity 1 1\n' + ''.join(rows[1:]),
            'infinite_other_column': '1 Infinity 1 1 1\n' + ''.join(rows[1:]),
            'negative_ratio': '1 0 -1 1 1\n' + ''.join(rows[1:]),
            'zero_ratio': '1 0 0 1 1\n' + ''.join(rows[1:]),
            'malformed': '1 0 1 1\n' + ''.join(rows[1:]),
            'nondecimal': '1 0 invalid 1 1\n' + ''.join(rows[1:]),
        }
        for name, content in cases.items():
            with self.subTest(case=name), self.assertRaises(verify.VerificationError):
                verify.numerical_file(self.write(content))


if __name__ == '__main__':
    unittest.main(verbosity=2)
