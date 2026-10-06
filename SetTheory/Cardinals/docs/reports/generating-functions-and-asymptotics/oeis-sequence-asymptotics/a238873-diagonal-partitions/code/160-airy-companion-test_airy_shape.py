#!/usr/bin/env python3
"""Standard-library tests. Run with both python -B and python -B -O."""
import argparse
import ast
from fractions import Fraction as F
import json
import math
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import airy_shape as c

HERE = Path(__file__).absolute().parent
DATA = HERE.parent / 'data'


class ExactCountsTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.table = c.counts_by_length(c.MAX_N)
        cls.a = [sum(row) for row in cls.table]
        cls.p = c.ordinary_counts(c.MAX_N)

    def test_empty_small_and_source_prefix(self):
        self.assertEqual(c.counts(0), [1])
        self.assertEqual(c.counts_by_length(0), [[1]])
        self.assertEqual(self.a[:13], [1, 1, 1, 2, 3, 3, 5, 7, 9, 11, 14, 19, 25])
        source = c.read_prefix()
        self.assertEqual(len(source['terms']), 61)
        self.assertEqual(self.a[:61], source['terms'])
        self.assertEqual(self.p[100], 190569292)

    def test_independent_enumeration_and_length_refinement(self):
        for n in range(23):
            all_parts = list(c.partitions(n))
            self.assertEqual(len(all_parts), self.p[n])
            self.assertEqual(len(set(all_parts)), len(all_parts))
            observed = [0] * len(self.table[n])
            for parts in all_parts:
                self.assertEqual(sum(parts), n)
                self.assertTrue(all(a <= b for a, b in zip(parts, parts[1:])))
                self.assertEqual(c.indexed_constraint(parts), c.cumulative_constraint(parts))
                if c.indexed_constraint(parts):
                    observed[len(parts)] += 1
            self.assertEqual(observed, self.table[n])

    def test_prefix_stability_and_staircase_cap(self):
        for n in (0, 1, 5, 30, 100, 200):
            self.assertEqual(c.counts(n), self.a[:n + 1])
        for n, row in enumerate(self.table):
            self.assertTrue(1 <= self.a[n] <= self.p[n])
            self.assertTrue(all(value == 0 for k, value in enumerate(row) if k * (k + 1) // 2 > n))
        self.assertTrue(all(a <= b for a, b in zip(self.a, self.a[1:])))

    def test_monotonicity_map_and_empty_case(self):
        self.assertEqual(c.monotonicity_image(()), (1,))
        self.assertEqual(c.monotonicity_image((2, 2)), (2, 3))
        for n in range(19):
            images = set()
            for parts in c.partitions(n):
                if c.indexed_constraint(parts):
                    mapped = c.monotonicity_image(parts)
                    self.assertTrue(c.indexed_constraint(mapped))
                    self.assertEqual(sum(mapped), n + 1)
                    self.assertNotIn(mapped, images)
                    images.add(mapped)
                    self.assertTrue(len(mapped) == 1 or mapped[-1] > mapped[-2])

    def test_exact_threshold_has_no_asymptotic_rounding(self):
        first = c.threshold_document(1, 0)
        self.assertEqual(first['first_n'], 0)
        self.assertIsNone(first['previous_count'])
        self.assertFalse(c.threshold_document(2, 0)['reached'])
        self.assertEqual(c.threshold_document(2, 3)['first_n'], 3)
        for value in (3, 4, 5, 25, 100, 1000):
            result = c.threshold_document(value, 80)
            self.assertEqual(result['first_n'], next(n for n in range(81) if self.a[n] >= value))
            self.assertGreaterEqual(result['count_at_first'], value)
            self.assertLess(result['previous_count'], value)
        result = c.threshold_document(c.MAX_THRESHOLD, 1)
        self.assertFalse(result['reached'])
        self.assertIsNone(result['first_n'])
        self.assertIsNone(result['count_at_first'])
        self.assertIsNone(result['previous_count'])


class ExactIdentityTests(unittest.TestCase):
    def test_known_prefixes_and_area_indexing(self):
        s = c.prefix_statistics((1, 0, 2))
        self.assertEqual(s, {'M': 3, 'weight': 7, 'length': 3,
                            'heights': [0, 0, 1, 0], 'area': 1, 'endpoint': 0})
        q = F(2, 3)
        self.assertEqual(c.prefix_identity((1, 0, 2), q), (q ** 7, q ** 7))
        s = c.prefix_statistics((4, 0, 0))
        self.assertEqual((s['area'], s['endpoint']), (-5, -1))
        self.assertEqual(c.prefix_identity((4, 0, 0), q), (q ** 4, q ** 4))
        self.assertEqual(c.prefix_identity((), q), (F(1), F(1)))

    def test_full_product_empty_and_cutoff_endpoints(self):
        for M in range(4):
            self.assertEqual(c.full_identity((4, 0, 0), M, F(2, 3)), (F(2, 3) ** 4,) * 2)
        self.assertEqual(c.full_identity((), 0, F(1, 2)), (F(1), F(1)))

    def test_exact_cutoffs_include_the_power_equality_case(self):
        self.assertEqual(c.exact_cutoffs(F(1, 3)), (0, 2))
        self.assertEqual(c.exact_cutoffs(F(1, 2)), (1, 2))
        self.assertEqual(c.exact_cutoffs(F(2, 3)), (1, 3))
        self.assertEqual(c.exact_cutoffs(F(9, 10)), (6, 8))
        for q in (True, 0.5, F(0), F(1), F(99, 100)):
            with self.assertRaises(c.InputError):
                c.exact_cutoffs(q)

    def test_finite_tail_coefficients_are_independently_enumerated(self):
        for cutoff, largest in ((0, 0), (0, 4), (2, 6), (5, 6)):
            coefficients = c.finite_tail_counts(cutoff, largest, 22)
            for n in range(23):
                brute = sum(all(cutoff < part <= largest for part in parts) for parts in c.partitions(n))
                self.assertEqual(coefficients[n], brute)
        self.assertEqual(c.finite_tail_normalization(F(1, 2), 0, 0), 1)

    def test_survival_one_step_and_monotonicity(self):
        for p in (F(1, 4), F(1, 3), F(49, 100)):
            self.assertEqual(c.survival(p, 0), 1)
            self.assertEqual(c.survival(p, 1), 1 - p * p)
            actual = [c.survival(p, h) for h in range(11)]
            self.assertTrue(all(a >= b for a, b in zip(actual, actual[1:])))
            self.assertGreaterEqual(actual[-1], 1 - 2 * p)

    def test_frozen_finite_document(self):
        doc = c.verify()
        self.assertEqual(doc, json.loads((DATA / 'finite_checks.json').read_text()))
        self.assertEqual(doc['status'], 'pass')
        self.assertEqual(doc['coverage']['prefix_weight_identities'], 1365)
        self.assertEqual(doc['coverage']['prefix_change_of_measure_identities'], 4095)
        self.assertEqual(doc['coverage']['full_product_identities'], 2916)
        self.assertEqual(doc['coverage']['tail_retilting_identities'], 164)
        self.assertGreater(doc['coverage']['quantile_comparisons'], 100000)

    def test_zero_enumeration_and_check_failures_survive_optimization(self):
        result = c.verify(0, 0)
        self.assertEqual(result['coverage']['ordinary_partitions'], 1)
        with self.assertRaises(c.CheckFailure):
            c.check(False, 'explicit failure')
        with patch.object(c, 'counts_by_length', return_value=[[0]]):
            with self.assertRaises(c.CheckFailure):
                c.verify(0, 0)
        with patch.object(c, 'prefix_identity', return_value=(F(0), F(1))):
            with self.assertRaises(c.CheckFailure):
                c.verify(0, 0)
        tree = ast.parse((HERE / 'airy_shape.py').read_text())
        self.assertFalse(any(isinstance(node, ast.Assert) for node in ast.walk(tree)))


class IllustrativeFormulaTests(unittest.TestCase):
    def test_shape_junction_inverse_and_stable_endpoint(self):
        self.assertEqual(c.density(0), 1.0)
        self.assertEqual(c.density(c.B), 1.0)
        self.assertEqual(c.row_shape(c.B), c.B)
        self.assertEqual(c.cumulative_shape(c.B), c.B)
        for i in range(1000):
            y = 2 * c.B * i / 1000
            self.assertAlmostEqual(c.cumulative_shape(c.row_shape(y)), y, delta=1e-14)
        self.assertTrue(math.isfinite(c.row_shape(math.nextafter(2 * c.B, 0))))
        self.assertEqual(c.density(10 ** 6), 0)
        self.assertEqual(c.cumulative_shape(10 ** 6), 2 * c.B)

    def test_constants_and_area_have_independent_formula_checks(self):
        doc = c.constants_document()
        self.assertAlmostEqual(float(doc['length_over_sqrt_n']), 1.214497355562513, delta=1e-11)
        self.assertLess(float(doc['area_identity_absolute_float_discrepancy']), 1e-14)
        self.assertEqual(doc['zeta_table_supplied'], '2.3381074105')
        self.assertEqual(doc['zeta_source'], 'https://dlmf.nist.gov/9.9.T1')
        # A second series length tests ordinary implementation consistency only.
        li2 = sum(0.5 ** k / (k * k) for k in range(1, 61))
        self.assertAlmostEqual(li2, math.pi ** 2 / 12 - math.log(2) ** 2 / 2, delta=1e-14)
        D = c.ZETA_TABLE * c.B * c.C ** (-1 / 6)
        for n in (1, 25, 10 ** 6, 10 ** 12):
            self.assertAlmostEqual(c.airy_log_expression(n), 2 * math.sqrt(c.C) * math.sqrt(n) - D * n ** (1 / 6), delta=1e-9)
        u = 100
        x = u * u / (4 * c.C)
        self.assertAlmostEqual(c.threshold_expression(u), x + 2 * D / (2 * math.sqrt(c.C)) * x ** (2 / 3), delta=1e-10)

    def test_reference_mean_riemann_examples_are_not_fixed_size_means(self):
        for t in (0.2, 0.1, 0.01, 0.001):
            doc = c.reference_length(t)
            value = float(doc['t_times_truncated_reference_mean_K'])
            tail = float(doc['omitted_t_mean_upper_bound'])
            self.assertLessEqual(2 * c.B - value, t + tail + 1e-11)
            self.assertGreaterEqual(2 * c.B - value, -1e-11)

    def test_frozen_illustrations_and_shape(self):
        self.assertEqual(c.illustrations_document(), json.loads((DATA / 'illustrations.json').read_text()))
        shape = c.shape_document()
        self.assertEqual(shape, json.loads((DATA / 'shape_coordinates.json').read_text()))
        self.assertEqual(len(shape['cumulative']), 122)
        self.assertEqual(len(shape['row']), 122)
        self.assertLess(float(shape['row'][-1]['y']), 2 * c.B)
        # Finite expected length is independently checked by explicit partitions.
        row = c.illustrations_document()['finite_uniform_law'][0]
        valid = [parts for parts in c.partitions(25) if c.indexed_constraint(parts)]
        self.assertEqual(F(row['exact_mean_K']), F(sum(map(len, valid)), len(valid)))


class ValidationTests(unittest.TestCase):
    def test_integer_only_apis_reject_bool_float_and_workload_excess(self):
        for method, upper in ((c.counts, c.MAX_N), (c.counts_by_length, c.MAX_N),
                              (c.ordinary_counts, c.MAX_N), (c.partitions, c.MAX_ENUMERATE)):
            for bad in (True, False, -1, upper + 1, 1.0, '2', None):
                with self.subTest(method=method.__name__, bad=bad), self.assertRaises(c.InputError):
                    method(bad)
        for args in ((0, 1), (20, True), (20, 2.0), (400, 33)):
            with self.assertRaises(c.InputError):
                c.verify(*args)
        for bad in (True, 0, -1, 2.0, '2', c.MAX_THRESHOLD + 1):
            with self.assertRaises(c.InputError):
                c.threshold_document(bad)
        for bad in (True, 0, 1.0, 10 ** 12 + 1):
            with self.assertRaises(c.InputError):
                c.airy_log_expression(bad)
        for bad in (True, 2, 1002, 4.0, '4'):
            with self.assertRaises(c.InputError):
                c.shape_document(bad)

    def test_real_domains_are_finite_and_strict(self):
        for method in (c.density, c.cumulative_shape, c.row_shape, c.threshold_expression):
            for bad in (True, False, float('nan'), float('inf'), -float('inf'), -1, '0', None, F(1, 2), 10 ** 1000):
                with self.subTest(method=method.__name__, bad=str(bad)[:20]), self.assertRaises(c.InputError):
                    method(bad)
        for bad in (2 * c.B, 2, 10 ** 6):
            with self.assertRaises(c.InputError):
                c.row_shape(bad)
        for bad in (True, 0, 0.0009, 0.5001, float('nan')):
            with self.assertRaises(c.InputError):
                c.reference_length(bad)

    def test_vectors_partitions_and_rational_parameters(self):
        for vector in (None, '1', {1}, (True,), (1.0,), (-1,), (9,), (0,) * 9):
            with self.assertRaises(c.InputError):
                c.prefix_statistics(vector)
        for parts in (None, '1', (True,), (1.0,), (0,), (2, 1), (400, 400)):
            with self.assertRaises(c.InputError):
                c.indexed_constraint(parts)
        with self.assertRaises(c.InputError):
            c.monotonicity_image((1, 1))
        for p in (True, 0.5, 1, F(0), F(1), F(-1, 2), F(1, 101)):
            with self.assertRaises(c.InputError):
                c.survival(p, 1)
            with self.assertRaises(c.InputError):
                c.prefix_identity((), p)
        for horizon in (True, -1, 1.0, 21):
            with self.assertRaises(c.InputError):
                c.survival(F(1, 3), horizon)
        for M in (True, -1, 2, 0.0):
            with self.assertRaises(c.InputError):
                c.full_identity((0,), M, F(1, 2))
        for args in ((0, 13, 1), (3, 2, 1), (False, 1, 1), (0, 2, 401), (0, 2, 1.0)):
            with self.assertRaises(c.InputError):
                c.finite_tail_counts(*args)

    def test_source_validation_rejects_noninteger_and_unattributed_data(self):
        original = c.read_prefix()
        with tempfile.TemporaryDirectory(dir=HERE) as directory:
            p = Path(directory) / 'source.json'
            invalid = ['{"schema":1,"schema":1}', '[]', '{', '{"x": NaN}', '0' * 101,
                       json.dumps(original).replace('"offset": 0', '"offset": 0.0')]
            for changes in ({'offset': True}, {'terms': [True]}, {'terms': [1.0]},
                            {'terms': []}, {'source_url': 'https://example.org'},
                            {'source_snapshot_sha256': 'bad'}, {'sequence': 'A000041'}):
                invalid.append(json.dumps({**original, **changes}))
            for content in invalid:
                p.write_text(content)
                with self.assertRaises(c.InputError):
                    c.read_prefix(p)
            p.write_bytes(b' ' * 32769)
            with self.assertRaises(c.InputError):
                c.read_prefix(p)
            with self.assertRaises(c.InputError):
                c.read_prefix(Path(directory))
            p.write_text(json.dumps(original))
            link = Path(directory) / 'link.json'
            link.symlink_to(p)
            with self.assertRaises(c.InputError):
                c.read_prefix(link)

    def test_json_and_cli_validation(self):
        for token in ('-1', '+1', '01', '1.0', 'True', ' 1', '', '1' * 202):
            with self.assertRaises(argparse.ArgumentTypeError):
                c.cli_integer(token)
        self.assertEqual(c.cli_integer('0'), 0)
        for document in ({'x': float('nan')}, {'x': F(1, 2)}, {'x': 'a' * c.MAX_JSON_BYTES}):
            with self.assertRaises(c.InputError):
                c.encoded_json(document)
        self.assertEqual(c.encoded_json({'z': 1, 'a': 0}), '{\n  "a": 0,\n  "z": 1\n}\n')


class CliTests(unittest.TestCase):
    def run_cli(self, *args):
        return subprocess.run([sys.executable, '-B', *(['-O'] if sys.flags.optimize else []),
                               str(HERE / 'airy_shape.py'), *args],
                              text=True, capture_output=True, timeout=30, check=False)

    def test_deterministic_stdout_and_no_file_api(self):
        first = self.run_cli('counts', '--max-n', '12')
        second = self.run_cli('counts', '--max-n', '12')
        self.assertEqual(first.returncode, 0, first.stderr)
        self.assertEqual(first.stdout, second.stdout)
        self.assertEqual(json.loads(first.stdout), c.counts_document(12))
        threshold = self.run_cli('threshold', '--value', '1', '--max-n', '0')
        self.assertEqual(threshold.returncode, 0, threshold.stderr)
        self.assertEqual(json.loads(threshold.stdout)['first_n'], 0)
        self.assertNotEqual(self.run_cli('counts', '--out', 'test.json').returncode, 0)

    def test_invalid_cli_never_emits_a_result(self):
        for args in (('counts', '--max-n', '401'), ('counts', '--max-n', '2.0'),
                     ('verify', '--max-n', '0'), ('shape', '--points', '1002'),
                     ('threshold', '--value', '0'), ('counts', '--max-n', 'True')):
            result = self.run_cli(*args)
            self.assertEqual(result.returncode, 2)
            self.assertEqual(result.stdout, '')


if __name__ == '__main__':
    unittest.main()
