"""Exact regression and adversarial validation/I/O tests for Report156.

Run both:
    python -B -m unittest -v test_companion
    python -O -B -m unittest -v test_companion
No third-party packages, shell interpolation, or network access are needed.
"""
from __future__ import annotations

import ast
from collections import Counter
from fractions import Fraction
import hashlib
import importlib.util
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
        cls.counts = c.counts_document(200)

    def test_saved_counts_are_reproducible(self):
        self.assertEqual(self.counts, json.loads((HERE / 'counts.json').read_text()))
        expected = {'A000041': 3972999029388, 'A000009': 487067746,
                    'A238875': 1930845918142, 'A238873': 25548856857}
        self.assertEqual({k: v[-1] for k, v in self.counts['sequences'].items()}, expected)

    def test_original_source_prefixes(self):
        for seq, source in c.read_prefixes().items():
            with self.subTest(seq=seq):
                self.assertEqual(self.counts['sequences'][seq][:len(source['terms'])], source['terms'])

    def test_complete_finite_verification_replay(self):
        actual = c.verify(200, 40, 10)
        self.assertEqual(actual, json.loads((HERE / 'finite_checks.json').read_text()))
        self.assertEqual(actual['status'], 'pass')
        self.assertEqual(actual['coverage']['fixed_rank_injection_instances'], 215267)
        self.assertEqual(actual['coverage']['interior_lemma_minimal_shift_instances'], 446242)

    def test_zero_weight_conventions(self):
        self.assertEqual(list(c.partitions(0)), [()])
        self.assertEqual(list(c.prefixes(0)), [()])
        self.assertEqual(c.prefix_to_walk(()), (0,))
        self.assertEqual(c.conjugate(()), ())
        self.assertTrue(c.subdiagonal(()))
        self.assertTrue(c.superdiagonal(()))
        for seq in c.counts_document(0)['sequences'].values():
            self.assertEqual(seq, [1])
        self.assertEqual(c.verify(0, 0, 0)['status'], 'pass')

    def test_enumeration_unique_and_canonical(self):
        for n in range(17):
            pp = list(c.partitions(n))
            self.assertEqual(len(pp), len(set(pp)))
            self.assertEqual(len(pp), self.counts['sequences']['A000041'][n])
            for lam in pp:
                self.assertEqual(sum(lam), n)
                self.assertEqual(lam, tuple(sorted(lam)))

    def test_shifted_dp_by_independent_enumeration(self):
        for shift in range(15):
            actual = c.diagonal_counts(14, 'sub', shift)
            expected = [sum(all(v <= i + shift for i, v in enumerate(lam, 1))
                            for lam in c.partitions(n)) for n in range(15)]
            self.assertEqual(actual, expected)
        self.assertEqual(c.diagonal_counts(25, 'sub', 25), c.ordinary_counts(25))

    def test_containment_through_200(self):
        seq = self.counts['sequences']
        for n in range(201):
            self.assertLessEqual(seq['A000009'][n], seq['A238873'][n])
            self.assertLessEqual(seq['A238873'][n], seq['A000041'][n])
            self.assertLessEqual(seq['A238875'][n], seq['A000041'][n])

    def test_rank_inverse_tied_largest_and_no_ones(self):
        cases = ((1, 1, 3, 3), (1, 2, 2), (2, 2), (1, 1, 1, 2), (9,))
        for lam in cases:
            image = c.remove_ones(lam)
            self.assertEqual(c.restore_ones(image, c.rank(lam)), lam)
        self.assertEqual(c.remove_ones((1, 1, 3, 3)), (3, 5))
        self.assertEqual(c.remove_ones((2, 2)), (2, 2))
        # The map is NOT globally injective: recording the source rank matters.
        self.assertEqual(c.remove_ones((1, 1, 2)), c.remove_ones((4,)))
        self.assertNotEqual(c.rank((1, 1, 2)), c.rank((4,)))

    def test_all_ones_are_explicit_exceptions(self):
        for n in range(1, 41):
            with self.assertRaises(c.AllOnesException):
                c.remove_ones((1,) * n)
        self.assertEqual(c.ordinary_counts(1)[1] - c.ordinary_counts(1)[0], 0)

    def test_rank_inverse_rejects_nonimages(self):
        for target, rank in (((1, 3), 0), ((2, 2), -2), ((2, 3), 0),
                             ((2,), -5), ((3, 4), -3), ((2,), 2)):
            with self.subTest(target=target, rank=rank), self.assertRaises(c.InputError):
                c.restore_ones(target, rank)

    def test_interior_endpoint_examples(self):
        lam = (1, 1, 1, 2, 2, 2, 2)
        self.assertTrue(c.interior_hypotheses(lam, 2, 0))
        self.assertTrue(c.subdiagonal(lam))
        # Area must be strict: equality does not satisfy the hypotheses.
        self.assertFalse(c.interior_hypotheses((1, 1, 3, 3), 1, 0))
        # Nonnegative shifts are part of the statement, not an inferred default.
        with self.assertRaises(c.InputError):
            c.interior_hypotheses(lam, 2, -1)

    def test_exact_bounded_walk_edges(self):
        self.assertEqual(c.bounded_walk_count(0, 0), 1)
        self.assertEqual(c.bounded_walk_count(1, 0), 0)
        for m in range(1, 20):
            self.assertEqual(c.bounded_walk_count(m, 1), 1)
            self.assertEqual(c.bounded_walk_count(m, 2), 2 ** (m - 1))
            self.assertEqual(c.bounded_walk_count(m, m), c.catalan(m))

    def test_spectral_formula_is_only_a_float_diagnostic(self):
        for height in range(1, 9):
            for m in range(11):
                spectral = sum(2 / (height + 2) * math.sin(j * math.pi / (height + 2)) ** 2
                               * (2 * math.cos(j * math.pi / (height + 2))) ** (2 * m)
                               for j in range(1, height + 2))
                self.assertAlmostEqual(spectral, c.bounded_walk_count(m, height), delta=1e-7)

    def test_tail_zero_negative_and_monotone_range(self):
        f = c.distinct_counts(30, 4)
        self.assertEqual(f[:6], [1, 0, 0, 0, 0, 1])
        self.assertEqual(c.coefficient(f, -1), 0)
        self.assertEqual(c.coefficient(f, 0), 1)
        self.assertGreater(f[0], f[1])  # Never claim monotonicity starting at zero.
        for n in range(5, 30):
            self.assertLessEqual(f[n], f[n + 1])

    def test_actual_distinct_tail_injection(self):
        for n in range(1, 25):
            images = set()
            for lam in c.partitions(n):
                if len(lam) != len(set(lam)):
                    continue
                image = lam[:-1] + (lam[-1] + 1,)
                self.assertEqual(len(image), len(set(image)))
                self.assertEqual(image[:-1] + (image[-1] - 1,), lam)
                self.assertNotIn(image, images)
                images.add(image)

    def test_exact_threshold_and_bounded_failure(self):
        self.assertEqual(c.threshold_document(1)['first_n'], 0)
        self.assertEqual(c.threshold_document(2)['first_n'], 3)
        r = c.threshold_document(1000)
        self.assertEqual(r['first_n'], 26)
        self.assertLess(r['previous_count'], r['value'])
        self.assertGreaterEqual(r['count_at_first'], r['value'])
        missing = c.threshold_document(1000, 25)
        self.assertFalse(missing['reached'])
        self.assertIsNone(missing['first_n'])
        self.assertIsNone(missing['count_at_first'])

    def test_inverse_initializer_explicitly_noncertifying(self):
        for value in (3, 10 ** 10, 10 ** 300):
            result = c.inverse_model_document(value)
            self.assertFalse(result['certified'])
            self.assertTrue(math.isfinite(result['approximate_initializer']))
            self.assertIn('No computable error bound', result['scope'])
            self.assertNotIn('first_n', result)


class Validation(unittest.TestCase):
    def test_boolean_float_string_and_fraction_inputs_rejected(self):
        invalid = (True, False, 1.0, '1', Fraction(1), None, float('nan'), float('inf'))
        functions = (c.ordinary_counts, c.distinct_counts, c.partitions, c.catalan,
                     c.prefixes, c.counts_document, c.threshold_document,
                     lambda x: c.diagonal_counts(x, 'sub'),
                     lambda x: c.bounded_walk_count(x, 2),
                     lambda x: c.bounded_walk_count(2, x),
                     lambda x: c.bounded_weight(x, 2),
                     lambda x: c.subdiagonal((1,), x),
                     lambda x: c.restore_ones((2,), x),
                     lambda x: c.interior_hypotheses((1, 1, 2), x, 0),
                     lambda x: c.verify(0, x, 0),
                     lambda x: c.distinct_counts(10, x),
                     lambda x: c.coefficient([1, 1], x), c.inverse_model_document)
        for fn in functions:
            for value in invalid:
                with self.subTest(fn=fn, value=value), self.assertRaises(c.InputError):
                    fn(value)

    def test_numeric_bounds_and_invalid_kinds(self):
        cases = (lambda: c.counts_document(-1), lambda: c.counts_document(201),
                 lambda: c.partitions(41), lambda: c.prefixes(11),
                 lambda: c.prefixes(2, 0), lambda: c.bounded_walk_count(2, 201),
                 lambda: c.bounded_weight(2, 0), lambda: c.subdiagonal((1,), 201),
                 lambda: c.threshold_document(0), lambda: c.threshold_document(10 ** 301),
                 lambda: c.inverse_model_document(2), lambda: c.verify(5, 6, 0),
                 lambda: c.diagonal_counts(2, 'ordinary'),
                 lambda: c.diagonal_counts(2, 'super', 1),
                 lambda: c.coefficient([1], 1))
        for fn in cases:
            with self.subTest(fn=fn), self.assertRaises(c.InputError):
                fn()

    def test_malformed_partitions(self):
        bad = ([2, 1], [0], [-1], [True], [1.0], ['1'], [201], [100, 101],
               [1] * 201, '1', None)
        for value in bad:
            with self.subTest(value=value), self.assertRaises(c.InputError):
                c.partition(value)
        for fn in (c.rank, c.remove_ones):
            with self.assertRaises(c.InputError):
                fn(())
        with self.assertRaises(c.InputError):
            c.prefix_to_walk((1, 3))

    def test_explicit_checks_survive_optimization(self):
        with self.assertRaises(c.CheckFailure):
            c.check(False, 'intentional failure')
        tree = ast.parse((HERE / 'companion.py').read_text())
        self.assertFalse(any(isinstance(node, ast.Assert) for node in ast.walk(tree)))

    def test_bad_prefix_schema_values_and_json(self):
        template = json.loads(c.SOURCE_PATH.read_text())
        variants = ['{}', '{', '[]', '{"x":1,"x":2}', '{"x":NaN}', '{"x":1.0}',
                    '{"x":' + '1' * 103 + '}', '[' * 2000 + ']' * 2000]
        for value in (True, 1.0, -1, '1'):
            copy = json.loads(json.dumps(template))
            copy['sequences']['A238875']['terms'][0] = value
            variants.append(json.dumps(copy))
        copy = json.loads(json.dumps(template))
        copy['sequences']['A238875']['offset'] = True
        variants.append(json.dumps(copy))
        copy = json.loads(json.dumps(template))
        copy['sequences']['A238875']['source_url'] = 'https://example.org/A238875'
        variants.append(json.dumps(copy))
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / 'input.json'
            for text in variants:
                path.write_text(text)
                with self.subTest(text=text[:60]), self.assertRaises(c.InputError):
                    c.read_prefixes(path)
            path.write_bytes(b'\xff')
            with self.assertRaises(c.InputError):
                c.read_prefixes(path)
            path.write_bytes(b' ' * 32769)
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
        for name in ('companion.py', 'source.json', 'Report156.tex'):
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


class CommandLine(unittest.TestCase):
    def run_cli(self, *arguments, optimized=False, cwd=None):
        command = [sys.executable]
        if optimized:
            command.append('-O')
        command.extend(['-B', str(HERE / 'companion.py'), *map(str, arguments)])
        return subprocess.run(command, cwd=cwd, text=True, capture_output=True, timeout=30)

    def test_stdout_and_normal_optimized_match(self):
        normal = self.run_cli('counts', '--max-n', 12)
        optimized = self.run_cli('counts', '--max-n', 12, optimized=True)
        self.assertEqual(normal.returncode, 0, normal.stderr)
        self.assertEqual(optimized.returncode, 0, optimized.stderr)
        self.assertEqual(normal.stdout, optimized.stdout)
        self.assertEqual(json.loads(normal.stdout)['max_n'], 12)

    def test_invalid_numbers_bounded_and_no_traceback(self):
        for value in ('true', '1.0', '2e1', '-1', '+1', '01', '201', '1' * 302):
            run = self.run_cli('counts', '--max-n', value)
            self.assertEqual(run.returncode, 2, value)
            self.assertEqual(run.stdout, '')
            self.assertNotIn('Traceback', run.stderr)
        run = self.run_cli('verify', '--max-n', 10, '--enumerate-to', 11)
        self.assertEqual(run.returncode, 2)
        run = self.run_cli('counts', '--max-n', 0, '--out', '')
        self.assertEqual(run.returncode, 2)
        self.assertEqual(run.stdout, '')

    def test_cli_safe_output_and_rejection(self):
        with tempfile.TemporaryDirectory() as temp:
            run = self.run_cli('counts', '--max-n', 3, '--out', 'result.json', cwd=temp)
            self.assertEqual(run.returncode, 0, run.stderr)
            self.assertEqual(run.stdout, '')
            before = (Path(temp) / 'result.json').read_bytes()
            run = self.run_cli('counts', '--max-n', 4, '--out', 'result.json', cwd=temp)
            self.assertEqual(run.returncode, 2)
            self.assertEqual((Path(temp) / 'result.json').read_bytes(), before)

    def test_verify_and_both_inverse_modes(self):
        run = self.run_cli('verify', '--max-n', 10, '--enumerate-to', 10, '--prefix-to', 3)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(json.loads(run.stdout)['status'], 'pass')
        run = self.run_cli('threshold', '--value', 1000, '--max-n', 30)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(json.loads(run.stdout)['first_n'], 26)
        run = self.run_cli('inverse-model', '--value', 1000000000)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertFalse(json.loads(run.stdout)['certified'])

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
