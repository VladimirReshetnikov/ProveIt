"""Exact regression and adversarial validation/I/O tests for Report157.

Run both from this directory:
    python -B -m unittest -v test_companion
    python -O -B -m unittest -v test_companion
No network, third-party modules, shell interpolation, or assertions are needed.
"""
from __future__ import annotations

import argparse
import ast
from fractions import Fraction
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
        cls.counts = c.counts_document()

    def test_saved_counts_are_reproducible(self):
        self.assertEqual(c.encoded_json(self.counts), (HERE / 'counts.json').read_bytes())
        self.assertEqual(self.counts['counts_by_c']['2'][:8], [1, 1, 3, 25, 443, 13956, 695902, 50741797])
        self.assertEqual(self.counts['counts_by_c']['1'][100], 101 ** 99)

    def test_original_source_prefix(self):
        source = c.read_prefixes()['A397711']
        self.assertEqual(len(source['terms']), 17)
        self.assertEqual(self.counts['counts_by_c']['2'][:17], source['terms'])
        self.assertEqual(source['terms'][-1], 163084920731472027278428501433)

    def test_complete_finite_verification_replay(self):
        actual = c.verify()
        self.assertEqual(c.encoded_json(actual), (HERE / 'finite_checks.json').read_bytes())
        self.assertEqual(actual['status'], 'pass')
        self.assertEqual(actual['coverage']['direct_graph_count_comparisons'], 30)
        self.assertEqual(actual['coverage']['graph_pair_state_assignments'], 59810)
        self.assertEqual(actual['coverage']['occupancy_poisson_sink_comparisons'], 105)
        self.assertEqual(actual['coverage']['pathwise_summation_by_parts_instances'], 34590)

    def test_empty_and_singleton_conventions(self):
        for bound in range(1, c.MAX_C + 1):
            self.assertEqual(c.sink_counts(1, bound), [1, 1])
            self.assertEqual(c.interval_widths(0, bound), [])
            self.assertEqual(c.occupancy_count(0, bound), 1)
            self.assertEqual(c.poisson_exact(0, bound), (Fraction(1), Fraction(1)))
            self.assertEqual(c.parking_word_count(0, bound), 1)
            self.assertEqual(c.pathwise_checks(0, bound), 1)
        self.assertEqual(list(c.excursion_occupancies(0)), [()])
        self.assertEqual(c.verify(0, 1, 0, 0, 0, 0)['status'], 'pass')

    def test_unbounded_small_dag_counts(self):
        unrestricted = [1, 1, 3, 25, 543, 29281]
        self.assertEqual(c.sink_counts(5, 8), unrestricted)
        for n, expected in enumerate(unrestricted):
            self.assertEqual(c.brute_dag_counts(n, 8)[8], expected)
        self.assertEqual(c.brute_dag_counts(4, 3), {1: 125, 2: 443, 3: 543})

    def test_widths_independent_pascal_difference(self):
        for bound in range(1, c.MAX_C + 1):
            cumulative = 0
            widths = c.interval_widths(100, bound)
            for i, width in enumerate(widths):
                cumulative += width
                self.assertGreaterEqual(width, 1)
                self.assertEqual(cumulative, c.parent_choices(i, bound))
        self.assertEqual(c.interval_widths(7, 2), [1, 1, 2, 3, 4, 5, 6])
        self.assertEqual(c.interval_widths(7, 1), [1] * 7)

    def test_normalizations_and_left_endpoint_area(self):
        expected = {0: Fraction(1), 1: Fraction(1), 2: Fraction(3, 2),
                    3: Fraction(25, 12), 4: Fraction(443, 144)}
        for n, en_z in expected.items():
            actual, count = c.poisson_exact(n, 2)
            self.assertEqual(actual, en_z)
            self.assertEqual(count, c.sink_counts(n, 2)[n])
            if n:
                self.assertEqual(count, actual * math.factorial(n) * math.factorial(n - 1))
        for n in range(16):
            en_z, count = c.poisson_exact(n, 1)
            self.assertEqual(count, c.forest_count(n))
            self.assertEqual(en_z, Fraction(c.forest_count(n), math.factorial(n)))

    def test_highest_supported_rational_boundary(self):
        for bound in (1, 2, 5, 8):
            expected = c.sink_counts(c.MAX_RATIONAL_N, bound)[-1]
            self.assertEqual(c.occupancy_count(c.MAX_RATIONAL_N, bound), expected)
            self.assertEqual(c.poisson_exact(c.MAX_RATIONAL_N, bound)[1], expected)

    def test_compositions_canonical_unique_and_catalan(self):
        for n in range(10):
            paths = list(c.excursion_occupancies(n))
            self.assertEqual(len(paths), len(set(paths)))
            self.assertEqual(len(paths), math.comb(2 * n, n) // (n + 1))
            for path in paths:
                self.assertEqual(len(path), n)
                self.assertEqual(sum(path), n)
                self.assertTrue(all(x >= 0 for x in path))
                self.assertTrue(all(sum(path[:i]) >= i for i in range(n + 1)))

    def test_exact_threshold_and_bounded_failure(self):
        self.assertEqual(c.threshold_document(1)['first_n'], 1)
        self.assertIsNone(c.threshold_document(1)['previous_count'])
        self.assertEqual(c.threshold_document(2)['first_n'], 2)
        self.assertEqual(c.threshold_document(1000000)['first_n'], 7)
        for bound in (1, 2, 5, 8):
            seq = c.sink_counts(12, bound)
            for n in range(2, 13):
                hit = c.threshold_document(seq[n], bound, n)
                self.assertEqual(hit['first_n'], n)
                self.assertEqual(hit['count_at_first'], seq[n])
                self.assertLess(hit['previous_count'], hit['value'])
                miss = c.threshold_document(seq[n] + 1, bound, n)
                self.assertFalse(miss['reached'])
                self.assertIsNone(miss['first_n'])
                self.assertIsNone(miss['count_at_first'])
                self.assertIsNone(miss['previous_count'])
                self.assertEqual(miss['last_count_searched'], seq[n])
        self.assertFalse(c.threshold_document(c.MAX_THRESHOLD, 1, c.MAX_N)['reached'])


class Validation(unittest.TestCase):
    def test_boolean_float_string_and_fraction_inputs_rejected(self):
        invalid = [True, False, 1.0, '1', None, Fraction(1), complex(1), [1]]
        functions = (lambda v: c.parent_choices(v, 2), lambda v: c.parent_choices(1, v),
                     lambda v: c.sink_counts(v, 2), lambda v: c.sink_counts(1, v),
                     c.forest_count, lambda v: c.interval_widths(v, 2),
                     lambda v: c.interval_widths(1, v), lambda v: c.occupancy_count(v, 2),
                     lambda v: c.occupancy_count(1, v), lambda v: c.poisson_exact(v, 2),
                     lambda v: c.poisson_exact(1, v), lambda v: c.brute_dag_counts(v, 2),
                     lambda v: c.brute_dag_counts(1, v), lambda v: c.parking_word_count(v, 2),
                     lambda v: c.parking_word_count(1, v), c.excursion_occupancies,
                     lambda v: c.pathwise_checks(v, 2), lambda v: c.pathwise_checks(1, v),
                     c.counts_document, lambda v: c.counts_document(1, v),
                     c.threshold_document, lambda v: c.threshold_document(1, v),
                     lambda v: c.threshold_document(1, 2, v), c.verify,
                     lambda v: c.verify(0, v, 0, 0, 0, 0),
                     lambda v: c.verify(1, 1, v, 0, 0, 0),
                     lambda v: c.verify(1, 1, 0, v, 0, 0),
                     lambda v: c.verify(1, 1, 0, 0, v, 0),
                     lambda v: c.verify(1, 1, 0, 0, 0, v))
        for fn in functions:
            for value in invalid:
                with self.subTest(fn=fn, value=value), self.assertRaises(c.InputError):
                    fn(value)

    def test_workload_caps_and_invalid_numeric_bounds(self):
        calls = (lambda: c.sink_counts(-1, 2), lambda: c.sink_counts(101, 2),
                 lambda: c.sink_counts(1, 0), lambda: c.sink_counts(1, 9),
                 lambda: c.occupancy_count(26, 2), lambda: c.poisson_exact(26, 2),
                 lambda: c.brute_dag_counts(6), lambda: c.parking_word_count(6, 2),
                 lambda: c.excursion_occupancies(10), lambda: c.pathwise_checks(10, 2),
                 lambda: c.threshold_document(0), lambda: c.threshold_document(c.MAX_THRESHOLD + 1),
                 lambda: c.threshold_document(1, 2, 0), lambda: c.verify(1, 1, 2, 0, 0, 0),
                 lambda: c.verify(1, 1, 0, 2, 0, 0), lambda: c.verify(1, 1, 0, 0, 2, 0),
                 lambda: c.verify(1, 1, 0, 0, 0, 2))
        for fn in calls:
            with self.subTest(fn=fn), self.assertRaises(c.InputError):
                fn()
        with patch.object(c, 'MAX_PARKING_WORDS', 1):
            with self.assertRaises(c.InputError):
                c.parking_word_count(2, 2)

    def test_canonical_decimal_only(self):
        for value in ('true', '1.0', '1e2', '-1', '+1', '01', ' 1', '1 ', '1\n',
                      '1_000', '١', '１', '1' * 1002, True, 1, None):
            with self.subTest(value=value), self.assertRaises(argparse.ArgumentTypeError):
                c.cli_integer(value)
        for value in ('0', '1', '123', '1' + '0' * 1000):
            self.assertEqual(c.cli_integer(value), int(value))

    def test_explicit_checks_survive_optimization_and_detect_mutation(self):
        with self.assertRaises(c.CheckFailure):
            c.check(False, 'intentional failure')
        tree = ast.parse((HERE / 'companion.py').read_text())
        self.assertFalse(any(isinstance(node, ast.Assert) for node in ast.walk(tree)))
        with patch.object(c, 'occupancy_count', return_value=0):
            with self.assertRaises(c.CheckFailure):
                c.verify(0, 1, 0, 0, 0, 0)
        with patch.object(c, 'poisson_exact', return_value=(Fraction(1), Fraction(1, 2))):
            with self.assertRaises(c.CheckFailure):
                c.verify(0, 1, 0, 0, 0, 0)

    def test_bad_prefix_schema_values_and_json(self):
        template = json.loads(c.SOURCE_PATH.read_text())
        variants = ['{}', '{', '[]', '{"x":1,"x":2}', '{"x":NaN}', '{"x":Infinity}',
                    '{"x":1.0}', '{"x":' + '1' * 103 + '}', '[' * 2000 + ']' * 2000]
        for value in (True, 1.0, -1, '1', 10 ** 101):
            copy = json.loads(json.dumps(template))
            copy['sequences']['A397711']['terms'][0] = value
            variants.append(json.dumps(copy))
        for key, value in (('offset', True), ('c', True), ('offset', 1), ('c', 3),
                           ('source_url', 'https://example.org/A397711'), ('terms', []),
                           ('terms', [1] * 102), ('terms', None)):
            copy = json.loads(json.dumps(template))
            copy['sequences']['A397711'][key] = value
            variants.append(json.dumps(copy))
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / 'input.json'
            for text in variants:
                path.write_text(text)
                with self.subTest(text=text[:60]), self.assertRaises(c.InputError):
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
        for name in ('companion.py', 'source.json', 'Report157.tex'):
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
        collision = self.root / ('.report157-' + 'a' * 32 + '.tmp')
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
        return subprocess.run(command, cwd=cwd, text=True, capture_output=True, timeout=30)

    def test_stdout_and_normal_optimized_match(self):
        for arguments in (('counts', '--max-n', 12), ('verify', '--max-n', 3),
                          ('threshold', '--value', 443)):
            normal = self.run_cli(*arguments)
            optimized = self.run_cli(*arguments, optimized=True)
            self.assertEqual(normal.returncode, 0, normal.stderr)
            self.assertEqual(optimized.returncode, 0, optimized.stderr)
            self.assertEqual(normal.stdout, optimized.stdout)

    def test_invalid_numbers_bounded_and_no_traceback(self):
        for value in ('true', '1.0', '2e1', '-1', '+1', '01', '101', '1' * 1002, '١'):
            run = self.run_cli('counts', '--max-n', value)
            self.assertEqual(run.returncode, 2, value)
            self.assertEqual(run.stdout, '')
            self.assertNotIn('Traceback', run.stderr)
        for args in (('counts', '--max-c', '0'), ('counts', '--max-c', '9'),
                     ('verify', '--max-n', '3', '--enumerate-to', '4'),
                     ('verify', '--rational-to', '26'), ('verify', '--parking-to', '6'),
                     ('verify', '--path-to', '10'), ('threshold', '--value', '0'),
                     ('threshold', '--value', '1', '--max-n', '0'),
                     ('counts', '--max-n', '0', '--out', '')):
            run = self.run_cli(*args)
            self.assertEqual(run.returncode, 2, args)
            self.assertEqual(run.stdout, '')
            self.assertNotIn('Traceback', run.stderr)

    def test_cli_safe_output_and_rejection(self):
        with tempfile.TemporaryDirectory() as temp:
            run = self.run_cli('counts', '--max-n', 3, '--out', 'result.json', cwd=temp)
            self.assertEqual(run.returncode, 0, run.stderr)
            self.assertEqual(run.stdout, '')
            before = (Path(temp) / 'result.json').read_bytes()
            run = self.run_cli('counts', '--max-n', 4, '--out', 'result.json', cwd=temp)
            self.assertEqual(run.returncode, 2)
            self.assertEqual((Path(temp) / 'result.json').read_bytes(), before)

    def test_verify_reduced_workload_and_threshold_outcomes(self):
        run = self.run_cli('verify', '--max-n', 3)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(json.loads(run.stdout)['status'], 'pass')
        self.assertEqual(json.loads(run.stdout)['parameters']['rational_to'], 3)
        run = self.run_cli('verify', '--max-n', 0)
        self.assertEqual(run.returncode, 0, run.stderr)
        run = self.run_cli('threshold', '--value', 1000000, '--max-n', 30)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(json.loads(run.stdout)['first_n'], 7)
        run = self.run_cli('threshold', '--value', 1000000, '--max-n', 6)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertFalse(json.loads(run.stdout)['reached'])

    def test_import_has_no_output_or_working_directory_side_effects(self):
        script = ('import importlib.util; '
                  f's=importlib.util.spec_from_file_location("isolated_companion",{str(HERE / "companion.py")!r}); '
                  'm=importlib.util.module_from_spec(s); s.loader.exec_module(m)')
        with tempfile.TemporaryDirectory() as temp:
            run = subprocess.run([sys.executable, '-B', '-c', script], cwd=temp,
                                 text=True, capture_output=True, timeout=10)
            self.assertEqual(run.returncode, 0, run.stderr)
            self.assertEqual(run.stdout, '')
            self.assertEqual(run.stderr, '')
            self.assertEqual(list(Path(temp).iterdir()), [])


if __name__ == '__main__':
    unittest.main()
