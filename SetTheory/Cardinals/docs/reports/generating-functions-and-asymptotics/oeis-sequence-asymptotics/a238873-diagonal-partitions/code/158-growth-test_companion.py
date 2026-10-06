"""Exact finite regression, strict validation, and adversarial file-I/O tests.

Run: python -B -m unittest -v test_companion
Also: python -O -B -m unittest -v test_companion
All dependencies are from the standard library. No network is used.
"""
from __future__ import annotations

import argparse
import ast
from fractions import Fraction
from itertools import product
import json
import math
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import companion as c

HERE = Path(__file__).absolute().parent


class ExactMathematics(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.document = c.counts_document()
        cls.sequence = cls.document['counts']

    def test_saved_counts_reproduce_exactly(self):
        self.assertEqual(c.encoded_json(self.document), (HERE / 'counts.json').read_bytes())
        self.assertEqual(self.sequence[:14], [1, 1, 1, 2, 3, 3, 5, 7, 9, 11, 14, 19, 25, 31])
        self.assertEqual(self.sequence[200], 25548856857)

    def test_attributed_oeis_prefix(self):
        source = c.read_prefixes()['A238873']
        self.assertEqual(source['source_url'], 'https://oeis.org/A238873')
        self.assertEqual(source['offset'], 0)
        self.assertEqual(len(source['terms']), 61)
        self.assertEqual(self.sequence[:61], source['terms'])

    def test_full_verification_replay(self):
        actual = c.verify()
        self.assertEqual(c.encoded_json(actual), (HERE / 'finite_checks.json').read_bytes())
        self.assertEqual(actual['status'], 'pass')
        self.assertEqual(actual['coverage']['direct_enumeration_indices'], 41)
        self.assertEqual(actual['coverage']['prefix_count_comparisons'], 100)
        self.assertEqual(actual['coverage']['prefix_tail_coefficient_inequalities'], 20100)
        self.assertEqual(actual['coverage']['rational_survival_horizons'], 93)
        self.assertEqual(actual['coverage']['rational_prefix_tail_inequalities'], 40)
        for row in actual['rational_survival']:
            self.assertIsInstance(row['finite_survival'], str)
            self.assertGreaterEqual(Fraction(row['finite_survival']), Fraction(row['lower_bound']))

    def test_empty_conventions(self):
        self.assertEqual(c.counts(0), [1])
        self.assertEqual(list(c.partitions(0)), [()])
        self.assertTrue(c.indexed_constraint(()))
        self.assertTrue(c.cumulative_constraint(()))
        self.assertEqual(c.monotonicity_image(()), (1,))
        for h in range(1, 11):
            self.assertEqual(list(c.prefixes(0, h)), [()])
            self.assertEqual(c.dyck_count(0, h), 1)
            self.assertEqual(c.prefix_weight_bound(0, h), 0)
            self.assertEqual(c.prefix_to_dyck((), h), ())
            self.assertEqual(c.dyck_to_prefix((), h), ())
        self.assertEqual(c.survival(Fraction(1, 3), 0), 1)
        self.assertEqual(c.finite_weighted(Fraction(1, 3), 0), 1)
        self.assertEqual(c.tail_product(Fraction(1, 3), 0), 1)
        self.assertEqual(c.verify(0, 0, 0, 1, 0)['status'], 'pass')

    def test_independent_in_place_recurrence(self):
        # Unlike the production fresh multiplicity layer, this uses coin-change
        # updates with length and weight increasing, allowing repetition of v.
        for cutoff in range(9):
            N = 60
            K = (math.isqrt(8 * N + 1) - 1) // 2
            state = [[0] * (K + 1) for _ in range(N + 1)]
            state[0][0] = 1
            for value in range(cutoff + 1, N + 1):
                for length in range(1, min(value - cutoff, K) + 1):
                    for weight in range(value, N + 1):
                        state[weight][length] += state[weight - value][length - 1]
            self.assertEqual(c.counts(N, cutoff), [sum(row) for row in state])
        self.assertEqual(c.counts(3, 10), [1, 0, 0, 0])

    def test_direct_tail_partition_counts(self):
        for cutoff in range(5):
            expected = c.counts(16, cutoff)
            for n in range(17):
                actual = sum(all(part >= cutoff + i for i, part in enumerate(parts, 1))
                             for parts in c.partitions(n))
                self.assertEqual(actual, expected[n], (n, cutoff))

    def test_partition_enumerator_complete_and_canonical(self):
        ordinary = [1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42]
        for n, expected in enumerate(ordinary):
            parts = list(c.partitions(n))
            self.assertEqual(len(parts), expected)
            self.assertEqual(len(set(parts)), expected)
            self.assertTrue(all(sum(p) == n and tuple(sorted(p)) == p for p in parts))
        self.assertFalse(c.indexed_constraint((1, 1)))
        self.assertFalse(c.cumulative_constraint((1, 1)))
        self.assertTrue(c.indexed_constraint((2, 2)))
        self.assertEqual(c.monotonicity_image((2, 2)), (2, 3))

    def test_dyck_paths_directly_exhausted_and_inverted(self):
        for M in range(7):
            for h in range(1, 7):
                valid = []
                for steps in product((-1, 1), repeat=2 * M):
                    height = 0
                    valid_path = True
                    for step in steps:
                        height += step
                        if not 0 <= height <= h:
                            valid_path = False
                            break
                    if valid_path and height == 0:
                        valid.append(steps)
                self.assertEqual(len(valid), c.dyck_count(M, h))
                inverse = {c.dyck_to_prefix(steps, h) for steps in valid}
                self.assertEqual(inverse, set(c.prefixes(M, h)))
                for parts in inverse:
                    self.assertIn(c.prefix_to_dyck(parts, h), valid)

    def test_dyck_extreme_strips(self):
        for M in range(11):
            self.assertEqual(c.dyck_count(M, 1), 1)
            self.assertEqual(c.dyck_count(M, 10), math.comb(2 * M, M) // (M + 1))
        self.assertEqual(c.prefix_to_dyck((1, 2, 3), 1), (1, -1, 1, -1, 1, -1))
        self.assertEqual(c.prefix_to_dyck((3, 3, 3), 3), (1, 1, 1, -1, -1, -1))

    def test_finite_survival_small_exact_values(self):
        for p in (Fraction(1, 4), Fraction(1, 3), Fraction(1, 2), Fraction(3, 4)):
            self.assertEqual(c.survival(p, 1), 1 - p ** 2)
            direct = sum(((1 - p) ** 2 * p ** (z1 + z2)
                          for z1 in range(2) for z2 in range(3 - z1)), Fraction(0))
            self.assertEqual(c.survival(p, 2), direct)
        value = c.survival(Fraction(49, 100), 30)
        self.assertGreaterEqual(value, Fraction(1, 50))
        self.assertLessEqual(value, 1)

    def test_finite_weighted_polynomials_independent(self):
        q = Fraction(2, 3)
        for J in range(7):
            for cutoff in range(J + 1):
                direct = Fraction(0)
                # Enumerate multiplicities without pruning; validate afterward.
                for z in product(range(J - cutoff + 1), repeat=J - cutoff):
                    if all(sum(z[:j]) <= j for j in range(1, J - cutoff + 1)):
                        direct += q ** sum(v * count for v, count in zip(range(cutoff + 1, J + 1), z))
                self.assertEqual(c.finite_weighted(q, J, cutoff), direct)
        self.assertEqual(c.finite_weighted(q, 1), 1 + q)
        self.assertEqual(c.tail_product(q, 2), 1 / ((1 - q) * (1 - q ** 2)))

    def test_exact_tilt_cutoff_equality(self):
        self.assertEqual(c.tilt_cutoff(Fraction(1, 2)), 1)
        self.assertEqual(c.tilt_cutoff(Fraction(1, 4)), 0)
        self.assertEqual(c.tilt_cutoff(Fraction(2, 3)), 1)
        self.assertEqual(c.tilt_cutoff(Fraction(3, 4)), 2)
        self.assertEqual(c.tilt_cutoff(Fraction(9, 10)), 6)
        self.assertEqual(c.tilt_cutoff(Fraction(97, 100)), 22)

    def test_threshold_first_occurrence_including_plateaus(self):
        self.assertEqual(c.threshold_document(1, 0)['first_n'], 0)
        self.assertIsNone(c.threshold_document(1)['previous_count'])
        self.assertEqual(c.threshold_document(2)['first_n'], 3)
        self.assertEqual(c.threshold_document(3)['first_n'], 4)
        self.assertEqual(c.threshold_document(1000000)['first_n'], 84)
        for target in range(1, 50):
            result = c.threshold_document(target, 20)
            expected = next((i for i, value in enumerate(self.sequence[:21]) if value >= target), None)
            self.assertEqual(result['first_n'], expected)
            if expected:
                self.assertLess(result['previous_count'], target)
        result = c.threshold_document(c.MAX_THRESHOLD)
        self.assertFalse(result['reached'])
        self.assertIsNone(result['first_n'])
        self.assertIsNone(result['count_at_first'])
        self.assertIsNone(result['previous_count'])
        self.assertEqual(result['last_count_searched'], self.sequence[-1])


class Validation(unittest.TestCase):
    def test_strict_integer_api_rejects_coercion(self):
        invalid = (True, False, 1.0, '1', Fraction(1), None, [1], complex(1))
        calls = (c.counts, lambda x: c.counts(1, x), c.partitions,
                 lambda x: c.prefixes(x, 1), lambda x: c.prefixes(1, x),
                 lambda x: c.prefix_weight_bound(x, 1), lambda x: c.prefix_weight_bound(1, x),
                 lambda x: c.dyck_count(x, 1), lambda x: c.dyck_count(1, x),
                 lambda x: c.prefix_to_dyck((), x), lambda x: c.dyck_to_prefix((), x),
                 lambda x: c.survival(Fraction(1, 3), x),
                 lambda x: c.finite_weighted(Fraction(1, 3), x),
                 lambda x: c.finite_weighted(Fraction(1, 3), 1, x),
                 lambda x: c.tail_product(Fraction(1, 3), x),
                 lambda x: c.tail_product(Fraction(1, 3), 1, x),
                 c.counts_document, c.threshold_document, lambda x: c.threshold_document(1, x),
                 c.verify, lambda x: c.verify(1, x, 0, 1, 0),
                 lambda x: c.verify(1, 1, x, 1, 0), lambda x: c.verify(1, 1, 0, x, 0),
                 lambda x: c.verify(1, 1, 0, 1, x))
        for call in calls:
            for value in invalid:
                with self.subTest(call=call, value=value), self.assertRaises(c.InputError):
                    call(value)

    def test_workload_caps(self):
        calls = (lambda: c.counts(-1), lambda: c.counts(201), lambda: c.counts(0, 201),
                 lambda: c.partitions(41), lambda: c.prefixes(11, 1), lambda: c.prefixes(1, 11),
                 lambda: c.prefixes(1, 0), lambda: c.dyck_count(11, 1),
                 lambda: c.survival(Fraction(1, 3), 31),
                 lambda: c.finite_weighted(Fraction(1, 3), 31),
                 lambda: c.tail_product(Fraction(1, 3), 1, 2),
                 lambda: c.verify(1, 2), lambda: c.verify(200, 41),
                 lambda: c.verify(0, 0, 11), lambda: c.verify(0, 0, 0, 11),
                 lambda: c.verify(0, 0, 0, 1, 31), lambda: c.threshold_document(0),
                 lambda: c.threshold_document(c.MAX_THRESHOLD + 1),
                 lambda: c.tilt_cutoff(Fraction(99, 100)))
        for call in calls:
            with self.subTest(call=call), self.assertRaises(c.InputError):
                call()

    def test_probability_type_range_and_size_caps(self):
        values = (True, False, 0, 1, 0.5, '1/2', Fraction(0), Fraction(1),
                  Fraction(-1, 2), Fraction(3, 2), Fraction(1, 101))
        for value in values:
            for call in (lambda x: c.survival(x, 1), lambda x: c.finite_weighted(x, 1),
                         lambda x: c.tail_product(x, 1), c.tilt_cutoff):
                with self.subTest(value=value, call=call), self.assertRaises(c.InputError):
                    call(value)

    def test_partition_and_path_validation(self):
        for value in (True, (), (1,), [1, 2]):
            if value is not True:
                self.assertIsInstance(c.indexed_constraint(value), bool)
        bad = (True, '123', {1, 2}, (2, 1), (True,), (1.0,), (0,), (201,), (100, 101), (1,) * 201)
        for value in bad:
            for call in (c.indexed_constraint, c.cumulative_constraint, c.monotonicity_image):
                with self.subTest(value=value, call=call), self.assertRaises(c.InputError):
                    call(value)
        for value in ((1, 1), (200,)):
            with self.assertRaises(c.InputError):
                c.monotonicity_image(value)
        for steps in ((True, -1), (1, -1.0), (1,), (-1, 1), (1, 1), (1, 1, -1, -1), (1, -1) * 11, 'UD'):
            with self.subTest(steps=steps), self.assertRaises(c.InputError):
                c.dyck_to_prefix(steps, 1)
        with self.assertRaises(c.InputError):
            c.prefix_to_dyck((2, 2), 1)

    def test_checks_explicit_under_optimization(self):
        tree = ast.parse((HERE / 'companion.py').read_text())
        self.assertFalse(any(isinstance(node, ast.Assert) for node in ast.walk(tree)))
        with self.assertRaises(c.CheckFailure):
            c.check(False, 'intentional failure')
        with patch.object(c, 'counts', return_value=[1, 0]):
            with self.assertRaises(c.CheckFailure):
                c.verify(1, 0, 0, 1, 0)

    def test_cli_canonical_integer_parser(self):
        for token in ('0', '1', '200', '1' + '0' * 1000):
            self.assertEqual(c.cli_integer(token), int(token))
        for token in ('', '+1', '-0', '01', '00', '1.0', '1e2', ' 1', '1 ', '١', '１', '1' * 1002, True):
            with self.subTest(token=token), self.assertRaises(argparse.ArgumentTypeError):
                c.cli_integer(token)

    def test_bounded_source_data_rejects_malformed_content(self):
        source = c.SOURCE_PATH.read_text()
        variants = ('[]', '{}', source.replace('report158-oeis-prefixes-v1', 'wrong'),
                    source.replace('"offset": 0', '"offset": true'),
                    source.replace('"offset": 0', '"offset": 0.0'),
                    source.replace('"offset": 0', '"offset": NaN'),
                    source.replace('"offset": 0', '"offset": 0, "offset": 0'),
                    source.replace('"offset": 0', '"offset": 1'),
                    source.replace('https://oeis.org/A238873', 'https://example.invalid'),
                    source.replace('"terms": [', '"terms": [true,'),
                    source.replace('"terms": [', '"terms": [' + '9' * 103 + ','))
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / 'source.json'
            for payload in variants:
                path.write_text(payload)
                with self.subTest(payload=payload[:70]), self.assertRaises(c.InputError):
                    c.read_prefixes(path)
            for payload in (b'\xff', b' ' * 32769):
                path.write_bytes(payload)
                with self.assertRaises(c.InputError):
                    c.read_prefixes(path)


@unittest.skipUnless(os.name == 'posix', 'POSIX safe-output contract')
class SafeOutput(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)

    def tearDown(self):
        self.temp.cleanup()

    def test_atomic_new_json_and_no_overwrite(self):
        path = self.root / 'new.json'
        c.write_new_json(path, {'count': 42})
        before = path.read_bytes()
        self.assertEqual(json.loads(before), {'count': 42})
        self.assertEqual(path.stat().st_mode & 0o777, 0o600)
        with self.assertRaises(c.InputError):
            c.write_new_json(path, {'replacement': True})
        self.assertEqual(path.read_bytes(), before)
        self.assertEqual(sorted(p.name for p in self.root.iterdir()), ['new.json'])

    def test_refuse_existing_source_or_input_files(self):
        for name in ('companion.py', 'source.json', 'Report158.tex'):
            path = self.root / name
            path.write_text('do not change\n')
            with self.assertRaises(c.InputError):
                c.write_new_json(path, {'overwrite': True})
            self.assertEqual(path.read_text(), 'do not change\n')

    def test_refuse_symlinks_leaf_and_parent(self):
        victim = self.root / 'victim.json'
        victim.write_text('unchanged')
        link = self.root / 'link.json'
        link.symlink_to(victim)
        with self.assertRaises(c.InputError):
            c.write_new_json(link, {})
        self.assertEqual(victim.read_text(), 'unchanged')
        dangling = self.root / 'dangling.json'
        dangling.symlink_to(self.root / 'missing.json')
        with self.assertRaises(c.InputError):
            c.write_new_json(dangling, {})
        real = self.root / 'real'
        real.mkdir()
        alias = self.root / 'alias'
        alias.symlink_to(real, target_is_directory=True)
        with self.assertRaises(c.InputError):
            c.write_new_json(alias / 'out.json', {})
        self.assertFalse((real / 'out.json').exists())
        with self.assertRaises(c.InputError):
            c.read_prefixes(link)

    def test_refuse_directories_fifo_and_special_file_targets(self):
        directory = self.root / 'directory.json'
        directory.mkdir()
        fifo = self.root / 'pipe.json'
        os.mkfifo(fifo)
        for path in (directory, fifo):
            with self.subTest(path=path), self.assertRaises(c.InputError):
                c.write_new_json(path, {})
            with self.subTest(path=path), self.assertRaises(c.InputError):
                c.read_prefixes(path)

    def test_refuse_untrusted_parent(self):
        parent = self.root / 'writable'
        parent.mkdir(mode=0o777)
        parent.chmod(0o777)
        try:
            with self.assertRaises(c.InputError):
                c.write_new_json(parent / 'out.json', {})
        finally:
            parent.chmod(0o700)
        self.assertFalse((parent / 'out.json').exists())

    def test_refuse_traversal_bad_paths_suffix_and_missing_parent(self):
        bad = ('', True, b'bytes.json', str(self.root / 'out.txt'),
               str(self.root) + '/./out.json', str(self.root) + '/../out.json',
               str(self.root) + '//out.json', str(self.root) + '/out.json/',
               str(self.root) + '/nul\x00.json', str(self.root) + '/back\\slash.json',
               self.root / 'absent' / 'out.json')
        for path in bad:
            with self.subTest(path=path), self.assertRaises(c.InputError):
                c.write_new_json(path, {})

    def test_new_target_race_does_not_clobber(self):
        destination = self.root / 'race.json'
        real_link = os.link
        def racing_link(src, dst, **kwargs):
            destination.write_text('racing owner content')
            return real_link(src, dst, **kwargs)
        with patch.object(c.os, 'link', side_effect=racing_link):
            with self.assertRaises(c.InputError):
                c.write_new_json(destination, {'data': 1})
        self.assertEqual(destination.read_text(), 'racing owner content')
        self.assertEqual(sorted(p.name for p in self.root.iterdir()), ['race.json'])

    def test_failed_prepublication_flush_leaves_no_output_or_temp(self):
        with patch.object(c.os, 'fsync', side_effect=OSError('simulated write failure')):
            with self.assertRaises(c.InputError):
                c.write_new_json(self.root / 'out.json', {'data': 1})
        self.assertEqual(list(self.root.iterdir()), [])

    def test_postpublication_failure_leaves_only_complete_output(self):
        original = c.os.fsync
        calls = 0
        def fail_second(fd):
            nonlocal calls
            calls += 1
            if calls == 2:
                raise OSError('simulated directory sync failure')
            return original(fd)
        with patch.object(c.os, 'fsync', side_effect=fail_second):
            with self.assertRaises(c.InputError):
                c.write_new_json(self.root / 'out.json', {'complete': True})
        self.assertEqual(json.loads((self.root / 'out.json').read_text()), {'complete': True})
        self.assertEqual(sorted(p.name for p in self.root.iterdir()), ['out.json'])

    def test_refuse_nonfinite_or_oversized_json_before_creating_files(self):
        for payload in ({'bad': float('nan')}, {'bad': float('inf')}, {'bad': object()},
                        {'big': 'x' * c.MAX_JSON_BYTES}):
            with self.assertRaises(c.InputError):
                c.write_new_json(self.root / 'out.json', payload)
        self.assertEqual(list(self.root.iterdir()), [])


    def test_random_temporary_collision_preserves_existing_file(self):
        collision = self.root / ('.report158-' + 'a' * 32 + '.tmp')
        collision.write_text('preexisting, not ours')
        with patch.object(c.secrets, 'token_hex', return_value='a' * 32):
            with self.assertRaises(c.InputError):
                c.write_new_json(self.root / 'out.json', {'data': 1})
        self.assertEqual(collision.read_text(), 'preexisting, not ours')
        self.assertFalse((self.root / 'out.json').exists())

    def test_input_directory_symlink_is_refused(self):
        real = self.root / 'real'
        real.mkdir()
        (real / 'prefix.json').write_bytes(c.SOURCE_PATH.read_bytes())
        alias = self.root / 'alias'
        alias.symlink_to(real, target_is_directory=True)
        with self.assertRaises(c.InputError):
            c.read_prefixes(alias / 'prefix.json')

    def test_wrong_owner_output_parent_is_refused(self):
        with patch.object(c.os, 'geteuid', return_value=os.geteuid() + 1):
            with self.assertRaises(c.InputError):
                c.write_new_json(self.root / 'out.json', {})
        self.assertEqual(list(self.root.iterdir()), [])

    def test_safe_io_unsupported_platform_is_explicit(self):
        with patch.object(c.os, 'name', 'unsupported'):
            with self.assertRaises(c.InputError):
                c.write_new_json(str(self.root / 'out.json'), {})
            with self.assertRaises(c.InputError):
                c.read_prefixes(str(c.SOURCE_PATH))


class CommandLine(unittest.TestCase):
    def run_cli(self, *arguments, optimized=False, cwd=None):
        command = [sys.executable]
        if optimized:
            command.append('-O')
        command.extend(['-B', str(HERE / 'companion.py'), *map(str, arguments)])
        return subprocess.run(command, cwd=cwd, text=True, capture_output=True, timeout=60)

    def test_stdout_normal_optimized_match(self):
        for arguments in (('counts', '--max-n', 12),
                          ('verify', '--max-n', 3, '--prefix-to', 2, '--height-to', 2, '--survival-to', 2),
                          ('threshold', '--value', 1000000)):
            normal = self.run_cli(*arguments)
            optimized = self.run_cli(*arguments, optimized=True)
            self.assertEqual(normal.returncode, 0, normal.stderr)
            self.assertEqual(optimized.returncode, 0, optimized.stderr)
            self.assertEqual(normal.stdout, optimized.stdout)

    def test_invalid_numbers_rejected_without_traceback(self):
        for value in ('true', '1.0', '2e1', '-1', '+1', '01', '201', '1' * 1002, '١'):
            result = self.run_cli('counts', '--max-n', value)
            self.assertEqual(result.returncode, 2, value)
            self.assertEqual(result.stdout, '')
            self.assertNotIn('Traceback', result.stderr)
        for args in (('verify', '--max-n', 3, '--enumerate-to', 4),
                     ('verify', '--enumerate-to', 41), ('verify', '--prefix-to', 11),
                     ('verify', '--height-to', 0), ('verify', '--height-to', 11),
                     ('verify', '--survival-to', 31), ('threshold', '--value', 0),
                     ('threshold', '--value', '2' + '0' * 1000),
                     ('counts', '--max-n', 0, '--out', ''), ('counts', '--max', 2)):
            result = self.run_cli(*args)
            self.assertEqual(result.returncode, 2, args)
            self.assertEqual(result.stdout, '')
            self.assertNotIn('Traceback', result.stderr)

    def test_new_output_and_no_clobber(self):
        with tempfile.TemporaryDirectory() as temp:
            result = self.run_cli('counts', '--max-n', 3, '--out', 'result.json', cwd=temp)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout, '')
            path = Path(temp) / 'result.json'
            before = path.read_bytes()
            result = self.run_cli('counts', '--max-n', 4, '--out', 'result.json', cwd=temp)
            self.assertEqual(result.returncode, 2)
            self.assertEqual(path.read_bytes(), before)

    def test_nonadversarial_concurrent_writers_publish_once(self):
        with tempfile.TemporaryDirectory() as temp:
            command = [sys.executable, '-B', str(HERE / 'companion.py'), 'counts',
                       '--max-n', '20', '--out', 'shared.json']
            children = [subprocess.Popen(command, cwd=temp, stdout=subprocess.PIPE,
                                         stderr=subprocess.PIPE, text=True) for _ in range(2)]
            outcomes = [child.communicate(timeout=30) for child in children]
            self.assertEqual(sorted(child.returncode for child in children), [0, 2], outcomes)
            self.assertEqual((Path(temp) / 'shared.json').read_bytes(), c.encoded_json(c.counts_document(20)))
            self.assertEqual([p.name for p in Path(temp).iterdir()], ['shared.json'])

    def test_reduced_verification_and_bounded_thresholds(self):
        result = self.run_cli('verify', '--max-n', 0, '--prefix-to', 0, '--height-to', 1, '--survival-to', 0)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout)['parameters']['enumerate_to'], 0)
        result = self.run_cli('threshold', '--value', 1000000, '--max-n', 84)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout)['first_n'], 84)
        result = self.run_cli('threshold', '--value', 1000000, '--max-n', 83)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertFalse(json.loads(result.stdout)['reached'])

    def test_import_has_no_output_or_working_directory_side_effects(self):
        script = ('import importlib.util; '
                  f's=importlib.util.spec_from_file_location("isolated_companion",{str(HERE / "companion.py")!r}); '
                  'm=importlib.util.module_from_spec(s); s.loader.exec_module(m)')
        with tempfile.TemporaryDirectory() as temp:
            result = subprocess.run([sys.executable, '-B', '-c', script], cwd=temp,
                                    text=True, capture_output=True, timeout=10)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout, '')
            self.assertEqual(result.stderr, '')
            self.assertEqual(list(Path(temp).iterdir()), [])


if __name__ == '__main__':
    unittest.main()
