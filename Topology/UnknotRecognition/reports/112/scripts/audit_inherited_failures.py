#!/usr/bin/env python3
"""Reproduce two stale maintained expectations in isolated pinned/current workers."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

PIN = 'e0b2f802f336fcb51e9ec5f29174cfe28dfb9d39'
FAST = Path('Topology/UnknotRecognition/fast')
VERIFIER = 'fastunknot/weighted_orbit_verify.py'
TESTS = [
    'tests.test_core_primitive_annuli.CorePrimitiveAnnuliTests.test_binary_multiplicity_and_remaining_failures',
    'tests.test_disk_bundle_absorption.DiskBundleAbsorptionTests.test_nondisk_annuli_and_stalled_augmented_cores_remain_unresolved',
]


def worker(runtime, expected_hash):
    import unittest
    sys.path.insert(0, str(runtime))
    import fastunknot.weighted_orbit_verify as verifier
    import fastunknot.normal_cut_handlebodies as producer
    actual = hashlib.sha256(Path(verifier.__file__).read_bytes()).hexdigest()
    if actual != expected_hash:
        raise AssertionError('wrong verifier was imported')
    suite = unittest.TestLoader().loadTestsFromNames(TESTS)
    result = unittest.TextTestRunner(stream=sys.stderr, verbosity=2).run(suite)
    origins = {}
    for name, module in list(sys.modules.items()):
        if name == 'fastunknot' or name.startswith('fastunknot.'):
            path = Path(module.__file__).resolve()
            origins[name] = str(path.relative_to(runtime))
    print(json.dumps(dict(tests_run=result.testsRun,
                         failures=[dict(test=test.id(), traceback=trace)
                                   for test, trace in result.failures],
                         errors=[dict(test=test.id(), traceback=trace)
                                 for test, trace in result.errors],
                         imported_verifier_sha256=actual,
                         verifier_module=verifier.__name__,
                         verifier_function_module=verifier.verify_weighted_orbit_certificate.__module__,
                         native_import_origins=origins)))
    return 0 if result.wasSuccessful() else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--baseline-verifier', type=Path,
                        default=Path(__file__).resolve().parents[1] /
                        'integration/reference/weighted_orbit_verify_baseline.py')
    parser.add_argument('--worker', type=Path)
    parser.add_argument('--expected-hash')
    args = parser.parse_args()
    if args.worker:
        raise SystemExit(worker(args.worker.resolve(), args.expected_hash))
    repo, output = args.repo.resolve(), args.output.resolve()
    selection = [str(FAST / path) for path in (
        'fastunknot', 'tests/test_core_primitive_annuli.py',
        'tests/test_disk_bundle_absorption.py', 'tests/test_normal_surface_orbits.py',
        'normal_orbit_research/fixtures.py', 'marked_parallelity_research/corpus.json')]
    command = ['git', 'ls-tree', '-r', '-z', PIN, '--'] + selection
    pinned_entries = subprocess.check_output(command, cwd=repo).split(b'\0')
    record = dict(pin=PIN, python=sys.version, tests=TESTS,
                  baseline_construction='local source copies authenticated against every exact pinned Git blob ID',
                  current_construction='same pinned files plus current verifier and weighted run rope only',
                  producer_unchanged=True, workers={},
                  reproduction=[sys.executable, '-B', str(Path(__file__).resolve()),
                                '--repo', str(repo), '--output', str(output),
                                '--baseline-verifier', str(args.baseline_verifier.resolve())])
    logs = []
    with tempfile.TemporaryDirectory(prefix='proveit-inherited-failures-') as temporary:
        temporary = Path(temporary)
        baseline = temporary / 'baseline'
        baseline.mkdir()
        authenticated = []
        for entry in pinned_entries:
            if not entry:
                continue
            metadata, name = entry.decode().split('\t', 1)
            mode, kind, blob_id = metadata.split()
            path = Path(name)
            relative = path.relative_to(FAST)
            if relative.parts[0] == 'fastunknot' and relative.suffix != '.py':
                continue
            if kind != 'blob' or '..' in relative.parts:
                raise AssertionError('unexpected pinned source path')
            data = (args.baseline_verifier.read_bytes() if str(relative) == VERIFIER
                    else (repo / path).read_bytes())
            actual = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
            if actual != blob_id:
                raise AssertionError('source differs from exact pin: ' + name)
            target = baseline / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
            authenticated.append(dict(path=name, git_blob_id=blob_id,
                                      sha256=hashlib.sha256(data).hexdigest()))
        record['pinned_files_authenticated'] = authenticated
        for package in ('tests', 'normal_orbit_research'):
            (baseline / package / '__init__.py').touch()
        current = temporary / 'current'
        shutil.copytree(baseline, current)
        for name in (VERIFIER, 'fastunknot/weighted_run_rope.py'):
            (current / name).write_bytes((repo / FAST / name).read_bytes())
        for label, runtime in (('baseline', baseline), ('current', current)):
            expected_hash = hashlib.sha256((runtime / VERIFIER).read_bytes()).hexdigest()
            command = [sys.executable, '-B', str(Path(__file__).resolve()), '--worker', str(runtime),
                       '--expected-hash', expected_hash]
            environment = dict(os.environ)
            environment.pop('PYTHONPATH', None)
            completed = subprocess.run(command, cwd=runtime, env=environment,
                                       capture_output=True, text=True, check=False)
            record['workers'][label] = json.loads(completed.stdout)
            record['workers'][label]['returncode'] = completed.returncode
            record['workers'][label]['command'] = command
            logs.append('=== ' + label + ' ===\n' + completed.stderr + '\n')
        record['identical_failing_test_ids'] = (
            [f['test'] for f in record['workers']['baseline']['failures']] ==
            [f['test'] for f in record['workers']['current']['failures']])
        record['both_have_two_failures_and_no_errors'] = all(
            worker['tests_run'] == 2 and len(worker['failures']) == 2 and not worker['errors']
            for worker in record['workers'].values())
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(record, indent=2) + '\n')
    output.with_suffix('.log').write_text(''.join(logs))
    print(json.dumps({key: record[key] for key in (
        'identical_failing_test_ids', 'both_have_two_failures_and_no_errors')}, indent=2))


if __name__ == '__main__':
    main()
