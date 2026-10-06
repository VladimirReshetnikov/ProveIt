#!/usr/bin/env python3
"""Deterministic standard-library tests; run normally and with python -O."""
from fractions import Fraction as F
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import companion as c

ROOT = Path(__file__).absolute().parent


class ExactCountsTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.s = c.subdiagonal_counts(c.MAX_N)
        cls.p = c.partition_counts(c.MAX_N)

    def test_empty_and_small_values(self):
        self.assertEqual(c.subdiagonal_counts(0), [1])
        self.assertEqual(c.partition_counts(0), [1])
        self.assertEqual(self.s[:12], [1, 1, 1, 2, 2, 4, 5, 7, 10, 15, 18, 26])
        self.assertEqual(self.p[100], 190569292)

    def test_source_prefix(self):
        source = c.read_prefix()
        self.assertEqual(len(source['terms']), 57)
        self.assertEqual(self.s[:57], source['terms'])

    def test_every_direct_partition_through_20(self):
        for n in range(21):
            mu = list(c.partitions(n))
            self.assertEqual(len(set(mu)), len(mu))
            self.assertEqual(len(mu), self.p[n])
            self.assertTrue(all(sum(v) == n and all(a >= b > 0 for a, b in zip(v, v[1:])) for v in mu))
            self.assertEqual(sum(all(a <= i for i, a in enumerate(v[::-1], 1)) for v in mu), self.s[n])

    def test_positive_bounds_and_prefix_stability(self):
        self.assertTrue(all(1 <= s <= p for s, p in zip(self.s, self.p)))
        self.assertTrue(all(a <= b for a, b in zip(self.s, self.s[1:])))
        for n in (0, 1, 2, 12, 40, 100):
            self.assertEqual(c.subdiagonal_counts(n), self.s[:n + 1])

    def test_exact_threshold_boundaries(self):
        self.assertEqual(c.threshold_document(1, 1)['first_n'], 0)
        self.assertEqual(c.threshold_document(1, 0)['first_n'], 0)
        self.assertEqual(c.threshold_document(1, 0)['search_starts_at'], 0)
        self.assertIsNone(c.threshold_document(1, 0)['previous_count'])
        self.assertFalse(c.threshold_document(2, 0)['reached'])
        self.assertEqual(c.threshold_document(2, 3)['first_n'], 3)
        for value in (4, 10, 18, 26, 80, 283):
            doc = c.threshold_document(value, 20)
            self.assertTrue(doc['reached'])
            self.assertEqual(doc['first_n'], next(n for n in range(1, 21) if self.s[n] >= value))
            self.assertEqual(doc['count_at_first'], self.s[doc['first_n']])
            self.assertLess(doc['previous_count'], value)
        doc = c.threshold_document(self.s[20] + 1, 20)
        self.assertFalse(doc['reached'])
        self.assertIsNone(doc['first_n'])
        self.assertIsNone(doc['count_at_first'])
        self.assertIsNone(doc['previous_count'])
        self.assertEqual(doc['last_count_searched'], self.s[20])
        self.assertFalse(c.threshold_document(c.MAX_THRESHOLD, 1)['reached'])


class FiniteIdentitiesTests(unittest.TestCase):
    def test_boundary_gap_counterexample_and_repair(self):
        core, x, y = (2,), (1,), (1,)
        after = c._insert_rows(core, x)
        self.assertEqual(after, (2, 1))
        self.assertEqual(c._gaps(core, 1), (2,))
        self.assertEqual(c._gaps(after, 1), (1,))
        target = c._insert_columns(after, y)
        self.assertEqual(target, c._insert_rows(c._insert_columns(core, y), x))
        self.assertTrue(c._meets(target, x, y))
        self.assertEqual(c._remove_rows(c._remove_columns(target, y), x), core)

    def test_negative_source_weight_exception_is_present(self):
        doc = c.mixed_identity(1, 0, (1,), (1,))
        self.assertEqual(doc['source_weight'], -1)
        self.assertEqual(doc['shifted_rank_count'], 0)
        self.assertEqual(doc['bad_target'], 1)
        self.assertEqual(doc['actual'], doc['reduced'])
        self.assertEqual(doc['actual'], 1)

    def test_empty_core_and_pure_rows(self):
        for n in range(8):
            for r in range(-4, 5):
                for cumulative in (True, False):
                    doc = c.mixed_identity(n, r, (2,), (), cumulative)
                    self.assertEqual(doc['actual'], doc['reduced'])
        doc = c.mixed_identity(0, 0, (), (0,))
        self.assertEqual(doc['actual'], 1)
        self.assertEqual(doc['bad_source'], 1)
        self.assertEqual(doc['bad_target'], 1)

    def test_exact_box_includes_signed_exceptions(self):
        seen_exception = False
        for n in range(13):
            for args in ((0, (1, 0), (), True, True), (0, (1,), (0,), False, False),
                         (0, (1, 0), (0,), True, False), (-1, (1, 1, 0), (0, 0), True, False)):
                doc = c.pattern_identity(n, *args)
                self.assertEqual(doc['actual'], doc['reduced'])
                seen_exception |= bool(doc['signed_bad_source'] or doc['signed_bad_target'])
        self.assertTrue(seen_exception)
        self.assertEqual(c.pattern_identity(0, 0, (5,), (5,))['actual'], 0)

    def test_finite_check_document_reproduces_packaged_result(self):
        generated = c.verify()
        saved = json.loads((ROOT / 'finite_checks.json').read_text())
        self.assertEqual(generated, saved)
        self.assertEqual(generated['status'], 'pass')
        self.assertGreater(generated['coverage']['boundary_gap_changes_observed'], 0)
        self.assertGreater(generated['coverage']['box_identities_with_nonzero_exceptions'], 0)
        self.assertEqual(generated['coverage']['forward_good_maps'], generated['coverage']['inverse_good_maps'])

    def test_all_zero_small_verification(self):
        doc = c.verify(0, 0)
        self.assertEqual(doc['direct_counts'], [{'n': 0, 's': 1, 'p': 1}])
        self.assertEqual(doc['partitions_enumerated'], 1)

    def test_checks_do_not_depend_on_assert(self):
        with self.assertRaises(c.CheckFailure):
            c.check(False, 'must raise, even under -O')
        with patch.object(c, 'subdiagonal_counts', return_value=[0]):
            with self.assertRaises(c.CheckFailure):
                c.verify(0, 0)


class ExactExpansionTests(unittest.TestCase):
    def test_full_cubic_and_packaged_json(self):
        output = c.expansion_document(3)
        self.assertEqual(output, json.loads((ROOT / 'endpoint_expansion.json').read_text()))
        self.assertEqual(output['coefficients_in_pi_inverse_squared'],
                         [['1/2'], ['-1/8'], ['-11/32', '3/4'], ['-317/384', '329/64', '-9/8']])
        self.assertEqual((output['bottom_first_failure_patterns'], output['top_first_failure_patterns'],
                          output['bottom_top_intersections'], output['nonzero_shift_terms']), (22, 64, 1408, 201))

    def test_all_orders_in_implemented_range_are_consistent(self):
        reference = c.expansion_document(3)['coefficients_in_t']
        for order in range(4):
            result = c.expansion_document(order)
            self.assertEqual(result['coefficients_in_t'], reference[:order + 1])
            self.assertEqual(result['endpoint_cutoff_M'], order + 2)
            self.assertEqual(result['remainder_order_in_beta'], order + 1)
        self.assertEqual(len(c.endpoint_patterns(2)[0]), 1)
        self.assertEqual(len(c.endpoint_patterns(2)[1]), 3)

    def test_audited_input_formulas(self):
        self.assertEqual(c.shifted_expansion('N', 0, 0),
                         [(F(0),), (F(1, 4),), (F(3, 16), F(-1, 4)), (F(53, 192), F(-89, 192), F(1, 16))])
        self.assertEqual(c.shifted_expansion('p', 0, 1),
                         [(F(1),), (F(-1),), (F(1, 2), F(1)), (F(-1, 6), F(-61, 48), F(-1, 4))])
        for r in range(5):
            self.assertEqual(c.shifted_expansion('N', r, 2), c.shifted_expansion('N', -r, 2))

    def test_independent_six_pattern_cancellation(self):
        # Direct finite differences on the audited analytic inputs; this does
        # not import/reuse the 201-term reduction or its pattern generator.
        def add(destination, series, sign=1):
            for j, coefficients in enumerate(series):
                for degree, coefficient in enumerate(coefficients):
                    destination[j][degree] += sign * coefficient
        def atom(r, w):
            return c.shifted_expansion('N', r, w)
        def cumulative(r, w):
            result = [[F(0) for _ in range(3)] for _ in range(4)]
            add(result, c.shifted_expansion('p', 0, w), F(1, 2))
            add(result, atom(0, w), F(1, 2) if r >= 0 else -F(1, 2))
            for j in range(1, r + 1 if r >= 0 else -r):
                add(result, atom(j, w), 1 if r >= 0 else -1)
            return result
        def masks(length):
            for mask in range(1 << length):
                chosen = [i + 1 for i in range(length) if mask & (1 << i)]
                yield len(chosen), sum(chosen), (-1) ** len(chosen)
        bottom, top = [(1, 0), (1, 1, 0), (2, 0, 0)], [(0, (0,)), (0, (1, 0)), (1, (0, 0))]
        bu = [[F(0) for _ in range(3)] for _ in range(4)]
        tu = [[F(0) for _ in range(3)] for _ in range(4)]
        for x in bottom:
            for u, w, sign in masks(len(x)):
                add(bu, cumulative(sum(x) + u, sum((i + 1) * a for i, a in enumerate(x)) + w), sign)
        for d, y in top:
            for v, w, sign in masks(len(y)):
                add(tu, atom(-d + 1 - sum(y) - v, 1 + sum((i + 1) * a for i, a in enumerate(y)) + w), sign)
        expected = [[F(0)] * 3, [F(0)] * 3, [F(1, 4), F(0), F(0)], [F(1, 2), -F(5, 8), F(0)]]
        self.assertEqual(bu, expected)
        self.assertEqual(tu, expected)
        for x in bottom:
            for d, y in top:
                overlap = [[F(0) for _ in range(3)] for _ in range(4)]
                for u, wa, sa in masks(len(x)):
                    for v, wb, sb in masks(len(y)):
                        w = sum((i + 1) * a for i, a in enumerate(x)) + sum((i + 1) * a for i, a in enumerate(y)) + wa + wb
                        add(overlap, atom(-d + sum(x) - sum(y) + u - v, w), sa * sb)
                self.assertEqual(overlap, [[F(0)] * 3 for _ in range(4)])


class InputValidationTests(unittest.TestCase):
    def test_counts_and_enumeration_ranges_types(self):
        for method, upper in ((c.subdiagonal_counts, c.MAX_N), (c.partition_counts, c.MAX_N), (c.partitions, c.MAX_ENUM_N)):
            for bad in (True, False, -1, upper + 1, 1.0, '2', None):
                with self.subTest(method=method.__name__, bad=bad), self.assertRaises(c.InputError):
                    method(bad)
        for args in ((1, 2), (1, True), (c.MAX_N + 1, 0), (2, c.MAX_ENUM_N + 1)):
            with self.assertRaises(c.InputError):
                c.verify(*args)

    def test_orders_shifts_threshold_bounds(self):
        for bad in (True, -1, 4, 1.0, '3', None):
            with self.assertRaises(c.InputError):
                c.expansion_document(bad)
        for bad in (True, -1, 1, 6, 2.0, None):
            with self.assertRaises(c.InputError):
                c.endpoint_reduction(bad)
        for args in (('X', 0, 0), ('p', 1, 0), ('N', True, 0), ('N', 33, 0), ('N', 0, -1), ('N', 0, 101), ('N', 0, 0, 4)):
            with self.assertRaises(c.InputError):
                c.shifted_expansion(*args)
        for value in (True, 0, -1, 2.0, '2', c.MAX_THRESHOLD + 1):
            with self.assertRaises(c.InputError):
                c.threshold_document(value)
        for maximum in (False, -1, c.MAX_N + 1, 2.0):
            with self.assertRaises(c.InputError):
                c.threshold_document(2, maximum)

    def test_vectors_and_flags(self):
        for vector in (None, '1', {1}, (True,), (-1,), (7,), (0,) * 6):
            with self.assertRaises(c.InputError):
                c.mixed_identity(0, 0, vector, ())
        with self.assertRaises(c.InputError):
            c.mixed_identity(0, 0, (), (0,), True)
        with self.assertRaises(c.InputError):
            c.mixed_identity(0, 0, (), (), 1)
        with self.assertRaises(c.InputError):
            c.pattern_identity(0, 0, (), (), exact_rows=1)
        with self.assertRaises(c.InputError):
            c.pattern_identity(0, 0, (6,), ())
        with self.assertRaises(c.InputError):
            c.pattern_identity(0, 0, (), (6,))
        self.assertEqual(c.pattern_identity(0, 0, (6,), (), exact_rows=False)['actual'], 0)

    def test_weak_vectors_and_cli_integer(self):
        self.assertEqual(list(c.weak_vectors(0, 0)), [()])
        self.assertEqual(list(c.weak_vectors(1, 0)), [])
        self.assertEqual(set(c.weak_vectors(2, 2)), {(0, 2), (1, 1), (2, 0)})
        for args in ((True, 1), (-1, 1), (6, 1), (1, 6), (1, False)):
            with self.assertRaises(c.InputError):
                c.weak_vectors(*args)
        for text in ('00', '01', '+1', '-1', ' 1', '1 ', '1.0', '1e2', '', '1' * 1002, True):
            with self.assertRaises(Exception):
                c.cli_integer(text)
        self.assertEqual(c.cli_integer('0'), 0)
        self.assertEqual(c.cli_integer('1' + '0' * 1000), c.MAX_THRESHOLD)


@unittest.skipUnless(os.name == 'posix' and hasattr(os, 'O_NOFOLLOW'), 'POSIX safe file I/O required')
class FileSafetyTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        os.chmod(self.root, 0o700)

    def tearDown(self):
        self.temporary.cleanup()

    def test_new_atomic_output_and_no_overwrite(self):
        target = self.root / 'output.json'
        doc = {'a': [1, 2], 'b': 'ok'}
        c.write_new_json(target, doc)
        self.assertEqual(target.read_bytes(), c.encoded_json(doc))
        self.assertEqual(target.stat().st_mode & 0o777, 0o600)
        with self.assertRaises(c.InputError):
            c.write_new_json(target, {'changed': True})
        self.assertEqual(target.read_bytes(), c.encoded_json(doc))
        self.assertEqual(sorted(p.name for p in self.root.iterdir()), ['output.json'])

    def test_symlinks_directories_fifo_and_wrong_extension(self):
        original = self.root / 'original.json'
        original.write_text('original')
        alias = self.root / 'alias.json'
        alias.symlink_to(original)
        broken = self.root / 'broken.json'
        broken.symlink_to(self.root / 'missing')
        directory = self.root / 'directory.json'
        directory.mkdir()
        fifo = self.root / 'fifo.json'
        os.mkfifo(fifo)
        for name in (alias, broken, directory, fifo, self.root / 'bad.txt'):
            with self.assertRaises(c.InputError):
                c.write_new_json(name, {})
        parent_alias = self.root / 'parent'
        parent_alias.symlink_to(self.root, target_is_directory=True)
        with self.assertRaises(c.InputError):
            c.write_new_json(parent_alias / 'new.json', {})
        self.assertEqual(original.read_text(), 'original')

    def test_path_and_parent_refusals(self):
        for target in ('', '.', '..', './new.json', 'a/../new.json', str(self.root) + '//new.json',
                       str(self.root) + '/new.json/', str(self.root) + '/bad\x00.json',
                       str(self.root) + '/bad\n.json', str(self.root) + '/bad\\name.json', b'bytes.json', None):
            with self.subTest(target=target), self.assertRaises(c.InputError):
                c.write_new_json(target, {})
        with self.assertRaises(c.InputError):
            c.write_new_json(self.root / 'missing' / 'new.json', {})
        os.chmod(self.root, 0o777)
        with self.assertRaises(c.InputError):
            c.write_new_json(self.root / 'new.json', {})
        os.chmod(self.root, 0o700)
        with patch.object(c.os, 'geteuid', return_value=os.geteuid() + 1):
            with self.assertRaises(c.InputError):
                c.write_new_json(self.root / 'new.json', {})
        with patch.object(c.os, 'name', 'nt'):
            with self.assertRaises(c.InputError):
                c.write_new_json(str(self.root / 'new.json'), {})

    def test_output_encoding_bounds(self):
        for doc in ({'nan': float('nan')}, {'infinity': float('inf')}, {'fraction': F(1, 2)}, {'big': 'x' * c.MAX_JSON_BYTES}):
            with self.assertRaises(c.InputError):
                c.write_new_json(self.root / 'new.json', doc)
        self.assertFalse((self.root / 'new.json').exists())

    def test_failed_publication_cleans_temporary_file(self):
        with patch.object(c.os, 'link', side_effect=OSError('simulated link failure')):
            with self.assertRaises(c.InputError):
                c.write_new_json(self.root / 'new.json', {'complete': True})
        self.assertEqual(list(self.root.iterdir()), [])

    def test_post_link_fsync_error_preserves_complete_output(self):
        real_fsync = c.os.fsync
        calls = 0
        def fail_directory(fd):
            nonlocal calls
            calls += 1
            if calls == 2:
                raise OSError('simulated directory fsync failure')
            return real_fsync(fd)
        target = self.root / 'new.json'
        with patch.object(c.os, 'fsync', side_effect=fail_directory):
            with self.assertRaises(c.InputError):
                c.write_new_json(target, {'complete': True})
        self.assertEqual(json.loads(target.read_text()), {'complete': True})
        self.assertEqual([p.name for p in self.root.iterdir()], ['new.json'])

    def test_two_benign_writers_never_clobber(self):
        target = self.root / 'race.json'
        command = [sys.executable, '-B', str(ROOT / 'companion.py'), 'counts', '--max-n', '2', '--out', str(target)]
        first = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        second = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        first.communicate(timeout=20)
        second.communicate(timeout=20)
        self.assertEqual(sorted([first.returncode, second.returncode]), [0, 2])
        self.assertEqual(json.loads(target.read_text()), c.counts_document(2))
        self.assertEqual([p.name for p in self.root.iterdir()], ['race.json'])

    def test_source_validation_and_no_symlinks(self):
        valid = c.read_prefix()
        source = self.root / 'source.json'
        source.write_text(json.dumps(valid))
        self.assertEqual(c.read_prefix(source), valid)
        modifications = [('schema', 'bad'), ('sequence', 'bad'), ('source_url', 'https://example.com'),
                         ('offset', True), ('terms', [True]), ('terms', [1.0]), ('terms', []),
                         ('terms', [-1]), ('terms', [10 ** 101]), ('terms', [1] * (c.MAX_N + 2))]
        for key, value in modifications:
            changed = dict(valid)
            changed[key] = value
            source.write_text(json.dumps(changed))
            with self.subTest(key=key, value=str(value)[:20]), self.assertRaises(c.InputError):
                c.read_prefix(source)
        for text in ('{"schema":"x","schema":"x"}', '{"n":NaN}', '{"n":Infinity}',
                     '{"n":' + '1' * 103 + '}', '[]', '{', 'x' * 32769):
            source.write_text(text)
            with self.assertRaises(c.InputError):
                c.read_prefix(source)
        source.write_bytes(b'\xff')
        with self.assertRaises(c.InputError):
            c.read_prefix(source)
        source.write_text(json.dumps(valid))
        alias = self.root / 'alias.json'
        alias.symlink_to(source)
        with self.assertRaises(c.InputError):
            c.read_prefix(alias)
        fifo = self.root / 'fifo.json'
        os.mkfifo(fifo)
        with self.assertRaises(c.InputError):
            c.read_prefix(fifo)


class CliAndArtifactsTests(unittest.TestCase):
    def run_cli(self, *arguments):
        return subprocess.run([sys.executable, '-B', str(ROOT / 'companion.py'), *arguments], capture_output=True, text=True, timeout=90)

    def test_counts_artifact_reproduction(self):
        self.assertEqual(c.counts_document(), json.loads((ROOT / 'counts.json').read_text()))

    def test_cli_success_stdout(self):
        result = self.run_cli('counts', '--max-n', '12')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout), c.counts_document(12))
        result = self.run_cli('threshold', '--value', '2', '--max-n', '2')
        self.assertEqual(result.returncode, 0)
        self.assertFalse(json.loads(result.stdout)['reached'])
        result = self.run_cli('threshold', '--value', '1', '--max-n', '0')
        self.assertEqual(result.returncode, 0)
        self.assertEqual(json.loads(result.stdout)['first_n'], 0)
        result = self.run_cli('expansion', '--order', '0')
        self.assertEqual(result.returncode, 0)
        self.assertEqual(json.loads(result.stdout)['coefficients_in_t'], [['1/2']])

    def test_cli_errors_are_clean(self):
        for arguments in (('counts', '--max-n', '301'), ('counts', '--max-n', '-1'), ('counts', '--max-n', '01'),
                          ('expansion', '--order', '4'), ('verify', '--max-n', '2', '--enumerate-to', '3'),
                          ('threshold', '--value', '0'), ('threshold', '--value', '2', '--max-n', '301')):
            result = self.run_cli(*arguments)
            self.assertEqual(result.returncode, 2)
            self.assertNotIn('Traceback', result.stderr)
            self.assertEqual(result.stdout, '')


if __name__ == '__main__':
    unittest.main(verbosity=2)
