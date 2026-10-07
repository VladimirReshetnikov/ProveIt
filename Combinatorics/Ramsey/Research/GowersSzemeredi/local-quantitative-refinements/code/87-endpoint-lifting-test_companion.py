#!/usr/bin/env python3
"""Standard-library regression and hostile-input tests; temporary output only."""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True
from collections import Counter
from contextlib import contextmanager
import copy
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).absolute().parent.parent
SPEC = importlib.util.spec_from_file_location('report299_exact', ROOT/'companion/exact_checks.py')
CHECK = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECK)
SNAPSHOT = CHECK.capture(ROOT)
DATA = CHECK.authenticate(SNAPSHOT)
CERTIFICATE = DATA['companion/certificate.json']
PYTHON = sys.executable


@contextmanager
def copied_data():
    with tempfile.TemporaryDirectory(prefix='report299-companion-') as directory:
        root = Path(directory)/'Report299'
        root.mkdir()
        for name, data in SNAPSHOT.items():
            path = root/name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        shutil.copyfile(ROOT/'companion/exact_checks.py', root/'companion/exact_checks.py')
        try:
            yield root
        finally:
            # Tests intentionally remove write permission from these directories.
            for path in root.rglob('*'):
                if not path.is_symlink():
                    path.chmod(0o700 if path.is_dir() else 0o600)
            root.chmod(0o700)


def cli(root, optimized=False, arguments=()):
    command = [PYTHON, '-I', '-B', '-X', 'int_max_str_digits=640']
    if optimized:
        command.append('-O')
    command.extend([str(root/'companion/exact_checks.py'), *arguments])
    return subprocess.run(command, cwd='/', stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, timeout=30, check=False)


def tree_state(root):
    return {str(path.relative_to(root)): (stat.S_IMODE(path.stat().st_mode),
                path.stat().st_mtime_ns, hashlib.sha256(path.read_bytes()).hexdigest())
            for path in root.rglob('*') if path.is_file()}


class MathematicalChecks(unittest.TestCase):
    def test_complete_deterministic_diagnostics(self):
        result = CHECK.run(SNAPSHOT)
        self.assertEqual(result['status'], 'PASS')
        self.assertFalse(result['coefficients']['tower_evaluated'])
        self.assertEqual(result['coefficients']['gap'], '3/16')
        self.assertEqual(result['weighted_graph_sum']['integer_weight_cases'], 674)
        self.assertEqual(result['weighted_graph_sum']['independent_quadruple_comparisons'], 674)
        self.assertEqual(result['all_direction_fibres']['proper_progression_presentations'], 510)
        self.assertEqual(result['all_direction_fibres']['affine_comparisons'], 20670)
        self.assertEqual(result['provenance']['proof_fields'], 8)
        self.assertEqual(result, CHECK.run(SNAPSHOT))

    def test_empty_and_zero_weight_graphs(self):
        self.assertEqual(CHECK.graph_energy(7, (), (), ()), (0, 0, 0))
        self.assertEqual(CHECK.graph_energy(7, (1, 4), (2, 5), (0, 0)), (0, 0, 0))

    def test_weighted_graph_energy_known_example(self):
        # Pair multiplicities 1,4,4 give energy 1+16+16=33, mass 3.
        self.assertEqual(CHECK.graph_energy(11, (0, 1), (0, 1), (1, 2)), (33, 3, 3))
        self.assertGreaterEqual(11*33, 3**4)

    def test_zero_family_domain_need_not_be_short_interval(self):
        domain = tuple(range(7))
        weights = (1,)*7
        self.assertEqual(CHECK.simultaneous_energy(7, domain, (), weights), 7**3)
        constants = ((0,)*7, (6,)*7)
        self.assertEqual(CHECK.simultaneous_energy(7, domain, constants, weights), 7**3)

    def test_small_sumset_is_a_real_hypothesis(self):
        # Full-domain quadratic graph fails the unit endpoint bound; never
        # extrapolate the small-support lemma without its support hypothesis.
        p = 5
        energy, mass, support = CHECK.graph_energy(p, tuple(range(p)),
                                                   tuple(x*x % p for x in range(p)), (1,)*p)
        self.assertGreater(support, p)
        self.assertLess(p*energy, mass**4)

    def test_graph_input_guards(self):
        invalid = [
            (True, (0,), (0,), (1,)), (21, (0,), (0,), (1,)),
            (4, (0,), (0,), (1,)), (5, (0, 0), (0, 1), (1, 1)),
            (5, (0,), (5,), (1,)), (5, (0,), (0,), (-1,)),
            (5, (0,), (0,), (True,)), (5, (0,), (0,), (1.0,)),
            (5, (0,), (0,), (9,)), (5, (0,), (), (1,)),
            (5, range(2), (0, 1), (1, 1))]
        for args in invalid:
            with self.subTest(args=args), self.assertRaises(CHECK.CheckError):
                CHECK.graph_energy(*args)

    def test_simultaneous_guards(self):
        invalid = [
            (3, (0,), ((0,),)*6, (1,)), (3, (0,), ((True,),), (1,)),
            (3, (0,), ((3,),), (1,)), (3, (0,), (), (-1,)),
            (3, (0,), ((),), (1,)), (11, tuple(range(8)), (), (1,)*8)]
        for args in invalid:
            with self.subTest(args=args), self.assertRaises(CHECK.CheckError):
                CHECK.simultaneous_energy(*args)

    def test_formal_monomial_guard_and_order(self):
        from fractions import Fraction as F
        self.assertTrue(CHECK.monomial_le((F(4), 3), (F(5), 6)))
        self.assertFalse(CHECK.monomial_le((F(5), 3), (F(4), 6)))
        self.assertFalse(CHECK.monomial_le((F(1), 7), (F(2), 6)))
        for pair in [((-1, 1), (1, 1)), ((F(1), True), (F(1), 1)),
                     ((F(1), 1025), (F(1), 1))]:
            with self.assertRaises(CHECK.CheckError):
                CHECK.monomial_le(*pair)


class JsonAndSchemaGuards(unittest.TestCase):
    def test_duplicate_json_keys_rejected(self):
        with self.assertRaises(CHECK.CheckError):
            CHECK.parse_json(b'{"x":1,"x":2}')

    def test_float_nonfinite_and_huge_json_numbers_rejected(self):
        for raw in (b'{"x":1.0}', b'{"x":1e9}', b'{"x":NaN}', b'{"x":Infinity}',
                    b'{"x":-Infinity}', b'{"x":1000000001}', b'{"x":'+b'9'*700+b'}'):
            with self.subTest(raw=raw[:30]), self.assertRaises(CHECK.CheckError):
                CHECK.parse_json(raw)

    def test_json_size_depth_encoding_and_node_guards(self):
        for raw in (b'', b'x'*(CHECK.MAX_FILE_BYTES+1), b'['*17+b']'*17,
                    b'{"'+b'x'*65537+b'":0}',
                    b'"\xff"', b'{' , b'[]]', b'['+b'0,'*12000+b'0]'):
            with self.subTest(size=len(raw)), self.assertRaises(CHECK.CheckError):
                CHECK.parse_json(raw)
        self.assertEqual(CHECK.parse_json(b'{"x":"{[\\\"}"}'), {'x':'{["}'})

    def test_mutable_or_nonbyte_json_rejected(self):
        for value in ('{}', bytearray(b'{}'), memoryview(b'{}'), None):
            with self.assertRaises(CHECK.CheckError):
                CHECK.parse_json(value)

    def test_certificate_types_and_scope(self):
        for field, value in [('report', True), ('schema_version', True),
                            ('max_interval_length', True), ('diagnostic_primes', [2,3,5,7,11,19]),
                            ('integer_weights', [False,1,2]), ('claim_boundary', '')]:
            certificate = copy.deepcopy(CERTIFICATE)
            certificate[field] = value
            with self.subTest(field=field), self.assertRaises(CHECK.CheckError):
                CHECK.validate_certificate(certificate)
        certificate = copy.deepcopy(CERTIFICATE)
        certificate['symbolic_constants']['R_over_K'] = True
        with self.assertRaises(CHECK.CheckError):
            CHECK.validate_certificate(certificate)
        certificate = copy.deepcopy(CERTIFICATE)
        certificate['symbolic_constants']['cover_fraction'] = [True,16]
        with self.assertRaises(CHECK.CheckError):
            CHECK.validate_certificate(certificate)

    def test_certificate_unknown_fields(self):
        certificate = copy.deepcopy(CERTIFICATE)
        certificate['execute_upstream'] = True
        with self.assertRaises(CHECK.CheckError):
            CHECK.validate_certificate(certificate)

    def test_source_excerpt_semantic_corruption(self):
        corrupted = copy.deepcopy(DATA)
        excerpt = corrupted['source_excerpts.json']['excerpts'][0]
        excerpt['utf8'] = excerpt['utf8'].replace('∀ D :', '∃ D :')
        excerpt['sha256'] = hashlib.sha256(excerpt['utf8'].encode()).hexdigest()
        with self.assertRaisesRegex(CHECK.CheckError, 'source anchor missing'):
            CHECK.validate_sources(corrupted)

    def test_source_field_inventory_corruption(self):
        corrupted = copy.deepcopy(DATA)
        excerpt = next(e for e in corrupted['source_excerpts.json']['excerpts']
                       if e['file']=='Proofs16CommonBaseAssembly.lean' and e['start_line']==30)
        excerpt['utf8'] = excerpt['utf8'].replace('  Hmass :', '  wrong_mass :')
        excerpt['sha256'] = hashlib.sha256(excerpt['utf8'].encode()).hexdigest()
        with self.assertRaisesRegex(CHECK.CheckError, 'field inventory differs'):
            CHECK.validate_sources(corrupted)

    def test_source_number_and_identity_corruption(self):
        for mutation in ('count', 'boolean_line', 'blob', 'alias'):
            corrupted = copy.deepcopy(DATA)
            if mutation == 'count':
                corrupted['SOURCE_MANIFEST.json']['source_count'] = True
            elif mutation == 'boolean_line':
                corrupted['source_excerpts.json']['excerpts'][0]['start_line'] = True
            elif mutation == 'blob':
                corrupted['CURRENT_SOURCE_STATUS.json']['records'][0]['blob_sha'] = '0'*40
            else:
                corrupted['SOURCE_MANIFEST.json']['sources'][0]['repository_path'] = '../Definitions.lean'
            with self.subTest(mutation=mutation), self.assertRaises(CHECK.CheckError):
                CHECK.validate_sources(corrupted)


class SnapshotAndFilesystemGuards(unittest.TestCase):
    def test_each_data_file_opened_once(self):
        calls = Counter()
        original = CHECK._read_once
        def track(parent, leaf):
            calls[leaf] += 1
            return original(parent, leaf)
        with mock.patch.object(CHECK, '_read_once', side_effect=track):
            snapshot = CHECK.capture(ROOT)
            CHECK.authenticate(snapshot)
        self.assertEqual(calls, Counter({Path(n).name:1 for n in CHECK.DATA_PINS}))

    def test_hash_and_parser_receive_identical_bytes(self):
        observed = []
        original = CHECK.parse_json
        def track(data):
            observed.append(data)
            return original(data)
        with mock.patch.object(CHECK, 'parse_json', side_effect=track), \
             mock.patch('builtins.open', side_effect=AssertionError('authentication reopened a file')), \
             mock.patch.object(CHECK.os, 'open', side_effect=AssertionError('authentication reopened a file')):
            CHECK.authenticate(SNAPSHOT)
        expected = [SNAPSHOT[n] for n in CHECK.DATA_PINS if n.endswith('.json')]
        self.assertEqual(len(observed), len(expected))
        for seen, captured in zip(observed, expected):
            self.assertIs(seen, captured)

    def test_regression_disk_changes_after_capture_cannot_change_authenticated_meaning(self):
        # Reproduces the dangerous sequence: capture valid bytes, replace the
        # on-disk JSON before interpretation, then verify. It must use capture.
        with copied_data() as root:
            snapshot = CHECK.capture(root)
            original_certificate = root/'companion/certificate.json'
            bad = copy.deepcopy(CERTIFICATE)
            bad['symbolic_constants']['cover_fraction'] = [1,1]
            original_certificate.write_text(json.dumps(bad), encoding='utf-8')
            parsed = CHECK.authenticate(snapshot)
            self.assertEqual(parsed['companion/certificate.json']['symbolic_constants']['cover_fraction'], [5,16])
            self.assertEqual(CHECK.run(snapshot)['status'], 'PASS')
            with self.assertRaisesRegex(CHECK.CheckError, 'identity mismatch'):
                CHECK.authenticate(CHECK.capture(root))

    def test_mutation_immediately_after_the_single_read(self):
        with copied_data() as root:
            original = CHECK._read_once
            calls = Counter()
            def mutate(parent, leaf):
                data = original(parent, leaf)
                calls[leaf] += 1
                if leaf == 'certificate.json':
                    (root/'companion/certificate.json').write_bytes(b'{}\n')
                return data
            with mock.patch.object(CHECK, '_read_once', side_effect=mutate):
                snapshot = CHECK.capture(root)
            self.assertEqual(CHECK.authenticate(snapshot)['companion/certificate.json'], CERTIFICATE)
            self.assertEqual(calls['certificate.json'], 1)

    def test_snapshot_inventory_and_immutability_guards(self):
        corrupted = dict(SNAPSHOT)
        corrupted.pop('SOURCE_MANIFEST.json')
        with self.assertRaises(CHECK.CheckError):
            CHECK.authenticate(corrupted)
        corrupted = dict(SNAPSHOT)
        corrupted['unapproved.json'] = b'{}'
        with self.assertRaises(CHECK.CheckError):
            CHECK.authenticate(corrupted)
        corrupted = dict(SNAPSHOT)
        corrupted['SOURCE_MANIFEST.json'] = bytearray(corrupted['SOURCE_MANIFEST.json'])
        with self.assertRaises(CHECK.CheckError):
            CHECK.authenticate(corrupted)

    def test_symlink_data_file_rejected(self):
        with copied_data() as root:
            target = root/'SOURCE_MANIFEST.json'
            moved = root/'saved-manifest.json'
            target.rename(moved)
            target.symlink_to(moved)
            with self.assertRaises((CHECK.CheckError, OSError)):
                CHECK.capture(root)

    def test_hardlink_data_file_rejected(self):
        with copied_data() as root:
            os.link(root/'SOURCE_MANIFEST.json', root/'alias.json')
            with self.assertRaisesRegex(CHECK.CheckError, 'hard-link'):
                CHECK.capture(root)

    def test_symlink_data_directory_rejected(self):
        with copied_data() as root:
            directory = root/'provenance'
            moved = root/'saved-provenance'
            directory.rename(moved)
            directory.symlink_to(moved, target_is_directory=True)
            with self.assertRaises((CHECK.CheckError, OSError)):
                CHECK.capture(root)

    def test_symlink_root_and_ancestor_rejected(self):
        with copied_data() as root:
            alias = root.parent/'alias'
            alias.symlink_to(root, target_is_directory=True)
            with self.assertRaises(OSError):
                CHECK.capture(alias)
            parent_alias = root.parent/'parent-alias'
            parent_alias.symlink_to(root.parent, target_is_directory=True)
            with self.assertRaises(OSError):
                CHECK.capture(parent_alias/root.name)

    def test_fifo_and_directory_data_rejected_without_blocking(self):
        for kind in ('fifo', 'directory'):
            with copied_data() as root:
                target = root/'SOURCE_MANIFEST.json'
                target.unlink()
                if kind == 'fifo':
                    os.mkfifo(target)
                else:
                    target.mkdir()
                with self.assertRaises(CHECK.CheckError):
                    CHECK.capture(root)

    def test_oversized_data_rejected_before_parse(self):
        with copied_data() as root:
            (root/'SOURCE_MANIFEST.json').write_bytes(b'x'*(CHECK.MAX_FILE_BYTES+1))
            with self.assertRaisesRegex(CHECK.CheckError, 'byte limit'):
                CHECK.capture(root)

    def test_data_mutation_during_read_rejected(self):
        with copied_data() as root:
            target = root/'SOURCE_MANIFEST.json'
            original = CHECK.os.read
            altered = False
            def mutate(descriptor, size):
                nonlocal altered
                data = original(descriptor, size)
                if not altered and data and data.startswith(b'{\n  "commit"'):
                    altered = True
                    target.write_bytes(target.read_bytes()+b' ')
                return data
            with mock.patch.object(CHECK.os, 'read', side_effect=mutate):
                with self.assertRaisesRegex(CHECK.CheckError, 'changed during read'):
                    CHECK.capture(root)
            self.assertTrue(altered)

    def test_bad_root_types_and_paths(self):
        for root in (True, 12, 'relative', '/tmp/../tmp', '//tmp', '/tmp/./x', '/tmp/\x00x'):
            with self.subTest(root=root), self.assertRaises(CHECK.CheckError):
                CHECK.capture(root)


class CommandLineChecks(unittest.TestCase):
    def test_normal_optimized_readonly_outputs_identical_without_writes(self):
        normal = cli(ROOT)
        optimized = cli(ROOT, True)
        self.assertEqual(normal.returncode, 0, normal.stderr)
        self.assertEqual(optimized.returncode, 0, optimized.stderr)
        self.assertEqual(normal.stdout, optimized.stdout)
        with copied_data() as root:
            for path in root.rglob('*'):
                path.chmod(0o555 if path.is_dir() else 0o444)
            root.chmod(0o555)
            before = tree_state(root)
            for mode in (False, True):
                readonly = cli(root, mode)
                self.assertEqual(readonly.returncode, 0, readonly.stderr)
                self.assertEqual(readonly.stdout, normal.stdout)
                self.assertEqual(readonly.stderr, b'')
            self.assertEqual(tree_state(root), before)
            self.assertFalse(list(root.rglob('__pycache__')))

    def test_each_data_file_corruption_rejected_normal_and_optimized(self):
        for name in CHECK.DATA_PINS:
            with copied_data() as root:
                target = root/name
                target.write_bytes(target.read_bytes()+b' ')
                for mode in (False, True):
                    with self.subTest(file=name, optimized=mode):
                        result = cli(root, mode)
                        self.assertEqual(result.returncode, 1)
                        self.assertEqual(result.stdout, b'')
                        self.assertIn(b'identity mismatch', result.stderr)

    def test_missing_data_rejected_normal_and_optimized(self):
        with copied_data() as root:
            (root/'companion/certificate.json').unlink()
            for mode in (False, True):
                result = cli(root, mode)
                self.assertEqual(result.returncode, 1)
                self.assertEqual(result.stdout, b'')

    def test_explicit_guards_survive_optimization(self):
        # This subprocess test independently exercises the actual guard code
        # when this test suite itself was launched without -O.
        code = (
            'import importlib.util; '
            's=importlib.util.spec_from_file_location("checked",'+repr(str(ROOT/'companion/exact_checks.py'))+'); '
            'm=importlib.util.module_from_spec(s); s.loader.exec_module(m); '
            'm.graph_energy(5,(0,),(0,),(-1,))')
        result = subprocess.run([PYTHON,'-I','-B','-O','-c',code], cwd='/',
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=10)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(b'CheckError', result.stderr)

    def test_arguments_cannot_authorize_writes(self):
        for mode in (False, True):
            result = cli(ROOT, mode, ('--output', '/tmp/report299-no-write'))
            self.assertEqual(result.returncode, 2)
            self.assertIn(b'read-only; no arguments', result.stderr)


if __name__ == '__main__':
    unittest.main(verbosity=2)
