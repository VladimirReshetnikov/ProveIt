"""Exact, bounded-workload and CLI tests; also run under python -O."""
import argparse
import ast
from fractions import Fraction
from itertools import permutations
import json
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch

import pop_stacked as c

HERE = Path(__file__).resolve().parent
DATA = HERE.parent / 'data'


class ExactTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.values, cls.tables = c.endpoint_tables()
        cls.verification = c.verify_document()

    def test_all_70_counts_and_packaged_output(self):
        self.assertEqual(len(self.values), 71)
        self.assertEqual(self.values[0], 1)
        self.assertEqual(self.values[1:26], list(c.OEIS_TERMS))
        self.assertEqual(self.values[1:46], list(c.PAPER_TABLE))
        self.assertEqual(self.values[70], int(
            '4509918709779623767450744053714823629593899853380943076380113423948190149807924015710118751513767'))
        expected = json.loads((DATA / 'counts.json').read_text())
        self.assertEqual(c.counts_document(), expected)

    def test_full_verification_and_packaged_output(self):
        self.assertEqual(self.verification['status'], 'pass')
        self.assertEqual(self.verification['bounds'],
                         {'max_n': 70, 'brute_to': 9, 'poset_to': 10, 'direct_to': 12})
        self.assertEqual(self.verification['oeis_displayed_terms_matched'], 25)
        self.assertEqual(self.verification['paper_table_terms_matched'], 45)
        self.assertEqual(self.verification,
                         json.loads((DATA / 'finite_checks.json').read_text()))
        self.assertEqual(self.verification['brute_force'][-1]['image_count'], '95991')
        self.assertEqual(self.verification['position_poset_normalization'][-1]['count'], '862047')

    def test_literal_full_endpoint_tables(self):
        self.assertEqual(c.literal_endpoint_tables(12), self.tables[:13])
        self.assertEqual(self.tables[3][1][2], 0)
        self.assertEqual(self.tables[3][2][2], 1)
        self.assertEqual(self.tables[3][1][3], 2)

    def test_operational_stack_distinct_from_falling_run_reversal(self):
        def reverse_falling_runs(p):
            out, start = [], 0
            for i in range(1, len(p) + 1):
                if i == len(p) or p[i - 1] < p[i]:
                    out.extend(reversed(p[start:i]))
                    start = i
            return tuple(out)
        for n in range(7):
            for p in permutations(range(1, n + 1)):
                self.assertEqual(c.apply_stack(p), reverse_falling_runs(p))
        self.assertEqual(c.apply_stack((3, 1, 2)), (1, 3, 2))
        self.assertEqual(c.ascending_runs((1, 4, 3, 2, 5)), ((1, 4), (3,), (2, 5)))
        self.assertEqual(c.canonical_preimage((1, 4, 3, 2, 5)), (4, 1, 3, 5, 2))

    def test_composition_poset_distribution_and_coefficient(self):
        self.assertEqual(c.composition_distribution(0), [1])
        self.assertEqual(c.composition_distribution(10),
                         [0, 1, 1004, 41708, 279566, 413878, 122830, 3060, 0, 0, 0])
        for n in range(11):
            self.assertEqual(sum(c.composition_distribution(n)), self.values[n])
        row = self.verification['position_poset_normalization'][-1]
        coefficient = row['coefficient_of_z_n']
        self.assertEqual(Fraction(int(coefficient['numerator']), int(coefficient['denominator'])),
                         Fraction(862047, 3628800))
        self.assertEqual(c.composition_edges(0, 0), ((), ()))
        self.assertEqual(c.count_extensions(0, ()), 1)
        self.assertEqual(c.count_extensions(3, ()), 6)
        self.assertEqual(c.count_extensions(3, ((0, 1), (1, 2))), 1)
        self.assertEqual(c.count_extensions(2, ((0, 1), (1, 0))), 0)
        self.assertEqual(c.count_extensions(1, ((0, 0),)), 0)
        self.assertEqual(c.count_extensions(2, ((0, 1), (0, 1))), 1)

    def test_cross_conditions_and_monotonicity(self):
        examples = c.cross_condition_examples()
        self.assertEqual(examples['composition_sum_n4']['both'], 11)
        self.assertEqual(examples['composition_sum_n4']['maximality_only'], 24)
        self.assertGreater(examples['composition_sum_n4']['overlap_only'], 11)
        self.assertEqual(c.append_largest(()), (1,))
        self.assertEqual(c.append_largest((1, 3, 2)), (1, 3, 2, 4))
        self.assertTrue(c.has_overlapping_runs((1, 4, 3, 2, 5)))
        self.assertFalse(c.has_overlapping_runs((4, 3, 2, 1)))
        self.assertTrue(all(a <= b for a, b in zip(self.values, self.values[1:])))

    def test_exact_threshold_boundaries(self):
        self.assertEqual(c.threshold_document(1, 0)['first_n'], 0)
        self.assertEqual(c.threshold_document(2, 3)['first_n'], 3)
        self.assertEqual(c.threshold_document(3, 3)['first_n'], 3)
        self.assertFalse(c.threshold_document(4, 3)['reached'])
        self.assertIsNone(c.threshold_document(4, 3)['first_n'])
        self.assertEqual(c.threshold_document(4, 3)['conclusion'], 'N(value)>3')
        self.assertEqual(c.threshold_document(11, 4)['first_n'], 4)
        for n in range(4, 15):
            self.assertEqual(c.threshold_document(self.values[n], n)['first_n'], n)
            self.assertEqual(c.threshold_document(self.values[n - 1] + 1, n)['first_n'], n)
            self.assertFalse(c.threshold_document(self.values[n] + 1, n)['reached'])
        self.assertFalse(c.threshold_document(10 ** 200)['reached'])

    def test_low_order_formal_inverse_rational_identities(self):
        self.assertEqual(c.low_order_inverse_coefficients(Fraction(1), Fraction(0)),
                         (Fraction(0), Fraction(-1, 12), Fraction(1, 24)))
        self.assertEqual(c.low_order_inverse_coefficients(Fraction(2), Fraction(1)),
                         (Fraction(-1, 2), Fraction(1, 48), Fraction(0)))
        self.assertEqual(c.low_order_inverse_coefficients(Fraction(1), Fraction(1)),
                         (Fraction(-1), Fraction(-1, 12), Fraction(-1, 24)))
        result = c.inverse_coefficient_checks()
        self.assertEqual(result['parameter_pairs_checked'], 25)
        self.assertTrue(all(row['residual_coefficients_t0_to_t2'] == ['0', '0', '0']
                            for row in result['rows']))
        for bad in (True, 1, 1.0, '1', None, Fraction(1001), Fraction(1, 101)):
            with self.assertRaises(c.InputError):
                c.low_order_inverse_coefficients(bad, Fraction(0))
            with self.assertRaises(c.InputError):
                c.low_order_inverse_coefficients(Fraction(1), bad)
        for bad in (Fraction(0), Fraction(-1)):
            with self.assertRaises(c.InputError):
                c.low_order_inverse_coefficients(bad, Fraction(0))
        with patch.object(c, 'low_order_inverse_coefficients', return_value=(Fraction(0),) * 3):
            with self.assertRaises(c.CheckFailure):
                c.inverse_coefficient_checks()

    def test_zero_bounds_and_automatic_shrinking(self):
        self.assertEqual(c.counts(0), [1])
        self.assertEqual(c.literal_endpoint_tables(0), [[[0]]])
        for n in (0, 1, 2, 5):
            result = c.verify_document(n)
            self.assertEqual(result['bounds'],
                             {'max_n': n, 'brute_to': n, 'poset_to': n, 'direct_to': n})
            self.assertEqual(result['oeis_displayed_terms_matched'], n)
        self.assertEqual(c.verify_document(5, 0, 0, 0)['bounds']['brute_to'], 0)

    def test_source_provenance_and_embedded_data(self):
        data = json.loads((DATA / 'source_data.json').read_text())
        self.assertEqual(data['sources'], c.SOURCES)
        self.assertEqual(data['oeis_displayed_terms_as_decimal_strings'], list(map(str, c.OEIS_TERMS)))
        self.assertEqual(data['paper_table_terms_as_decimal_strings'], list(map(str, c.PAPER_TABLE)))
        self.assertEqual(len(c.OEIS_TERMS), 25)
        self.assertEqual(len(c.PAPER_TABLE), 45)
        self.assertEqual(c.SOURCES['oeis']['url'], 'https://oeis.org/A307030')
        for source in c.SOURCES.values():
            for key, value in source.items():
                if key.endswith('sha256'):
                    self.assertRegex(value, r'^[0-9a-f]{64}$')


class GuardTests(unittest.TestCase):
    def test_integer_arguments_reject_types_and_bounds(self):
        for value in (True, False, -1, 71, 1.0, '1', None, 10 ** 1000):
            with self.subTest(value=repr(value)[:30]):
                for function in (c.counts, c.endpoint_tables, c.counts_document, c.verify_document):
                    with self.assertRaises(c.InputError):
                        function(value)
        for value in (True, -1, 13, 1.0, '1', None):
            with self.assertRaises(c.InputError):
                c.literal_endpoint_tables(value)
        for name, maximum in [('brute_to', 9), ('poset_to', 10), ('direct_to', 12)]:
            for value in (True, -1, maximum + 1, 1.0, '1'):
                with self.assertRaises(c.InputError):
                    c.verify_document(70, **{name: value})
            with self.assertRaises(c.InputError):
                c.verify_document(0, **{name: 1})
        for value in (True, False, 0, -1, 1.0, '1', 10 ** 200 + 1):
            with self.assertRaises(c.InputError):
                c.threshold_document(value)

    def test_permutations_and_injections_reject_invalid_arguments(self):
        bad = (None, '12', {1, 2}, (True,), (1.0,), (0,), (2,), (1, 1), tuple(range(1, 72)))
        for value in bad:
            for function in (c.apply_stack, c.ascending_runs, c.has_overlapping_runs,
                             c.canonical_preimage, c.append_largest):
                with self.assertRaises(c.InputError):
                    function(value)
        with self.assertRaises(c.InputError):
            c.append_largest(tuple(range(1, 71)))
        for function in (c.canonical_preimage, c.append_largest):
            with self.assertRaises(c.InputError):
                function((3, 2, 1))

    def test_poset_guards(self):
        for n in (True, -1, 11, 1.0, '1'):
            with self.assertRaises(c.InputError):
                c.composition_distribution(n)
            with self.assertRaises(c.InputError):
                c.composition_edges(n, 0)
            with self.assertRaises(c.InputError):
                c.count_extensions(n, ())
        for cuts in (True, -1, 4, 1.0, '1'):
            with self.assertRaises(c.InputError):
                c.composition_edges(3, cuts)
        for edges in (None, {(0, 1)}, ((0,),), ((0, 1, 2),), ((-1, 1),),
                      ((0, True),), ((0, 1.0),), ((0, 2),), ((0, 1),) * 5):
            with self.assertRaises(c.InputError):
                c.count_extensions(2, edges)
        with self.assertRaises(c.InputError):
            c.count_extensions(0, ((0, 0),))

    def test_no_disabled_correctness_asserts_and_faults_fail(self):
        tree = ast.parse((HERE / 'pop_stacked.py').read_text())
        self.assertFalse(any(isinstance(node, ast.Assert) for node in ast.walk(tree)))
        with self.assertRaises(c.CheckFailure):
            c.check(False, 'intentional failure')
        with patch.object(c, 'OEIS_TERMS', (99,) + c.OEIS_TERMS[1:]):
            with self.assertRaises(c.CheckFailure):
                c.verify_document(1)
        with patch.object(c, 'PAPER_TABLE', (99,) + c.PAPER_TABLE[1:]):
            with self.assertRaises(c.CheckFailure):
                c.verify_document(1)
        with patch.object(c, '_apply_stack', return_value=()):
            with self.assertRaises(c.CheckFailure):
                c.verify_document(1)
        with patch.object(c, 'composition_distribution', return_value=[99]):
            with self.assertRaises(c.CheckFailure):
                c.verify_document(0)

    def test_canonical_cli_integer_and_json(self):
        for token in ('-1', '+1', '01', '1.0', 'True', ' 1', '1 ', '', '１２', '١', '1' * 202):
            with self.assertRaises(argparse.ArgumentTypeError):
                c.cli_integer(token)
        self.assertEqual(c.cli_integer('0'), 0)
        self.assertEqual(c.cli_integer('10'), 10)
        self.assertEqual(c.encoded_json({'z': 1, 'a': 0}), '{\n  "a": 0,\n  "z": 1\n}\n')
        for data in ({'x': float('nan')}, {'x': float('inf')}, {'x': Fraction(1, 2)},
                     {'x': 'a' * c.MAX_JSON_BYTES}):
            with self.assertRaises(c.InputError):
                c.encoded_json(data)


class CliTests(unittest.TestCase):
    def run_cli(self, *args, optimized=None):
        if optimized is None:
            optimized = bool(sys.flags.optimize)
        return subprocess.run([sys.executable, '-B', *(['-O'] if optimized else []),
                               str(HERE / 'pop_stacked.py'), *args],
                              text=True, capture_output=True, timeout=30, check=False)

    def test_deterministic_normal_and_optimized_stdout(self):
        for args in [('counts', '--max-n', '12'), ('verify', '--max-n', '5'), ('sources',),
                     ('threshold', '--value', '11', '--max-n', '4')]:
            normal = self.run_cli(*args, optimized=False)
            optimized = self.run_cli(*args, optimized=True)
            self.assertEqual(normal.returncode, 0, normal.stderr)
            self.assertEqual(optimized.returncode, 0, optimized.stderr)
            self.assertEqual(normal.stdout, optimized.stdout)
            self.assertEqual(normal.stderr, '')
            self.assertIsInstance(json.loads(normal.stdout), dict)
        self.assertEqual(json.loads(self.run_cli('threshold', '--value', '1', '--max-n', '0').stdout)['first_n'], 0)

    def test_invalid_cli_has_no_json_or_output_file_api(self):
        for args in [(), ('counts', '--max-n', '71'), ('counts', '--max-n', '-1'),
                     ('counts', '--max-n', '2.0'), ('counts', '--max-n', 'True'),
                     ('counts', '--max-n', '01'), ('counts', '--max-n', '１２'),
                     ('counts', '--max-n', '1' * 202), ('verify', '--brute-to', '10'),
                     ('verify', '--poset-to', '11'), ('verify', '--direct-to', '13'),
                     ('verify', '--max-n', '0', '--brute-to', '1'),
                     ('threshold', '--value', '0'), ('threshold', '--value', str(10 ** 200 + 1)),
                     ('counts', '--out', 'test.json'), ('counts', '--source', 'test.json')]:
            with self.subTest(args=args):
                result = self.run_cli(*args)
                self.assertEqual(result.returncode, 2, result.stderr)
                self.assertEqual(result.stdout, '')


if __name__ == '__main__':
    unittest.main()
