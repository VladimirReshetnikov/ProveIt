#!/usr/bin/env python3
"""Verify this research package in a temporary copy; no archived file is changed."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2] / 'reports' / '24'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='optional new JSON verification report')
    args = parser.parse_args()
    if sys.flags.optimize:
        parser.error('verification requires assertions; run without -O or PYTHONOPTIMIZE')
    if args.output and args.output.exists():
        parser.error('output already exists; choose a new name to preserve archived results')
    started = time.monotonic()
    # The delivered package omits SHA256_MANIFEST.json. Verify the supplied
    # integration manifest instead and state the narrower provenance claim.
    changes = json.loads((ROOT / 'integration/changes.json').read_text())
    for entry in changes:
        name = entry['path'].removeprefix('Topology/UnknotRecognition/')
        if hashlib.sha256((ROOT / name).read_bytes()).hexdigest() != entry['sha256']:
            raise SystemExit(f'Hash mismatch: {name}')
    report = {'status': 'running', 'files_verified': len(changes),
              'manifest': 'integration/changes.json',
              'missing_manifest': 'SHA256_MANIFEST.json',
              'python': sys.version, 'checks': {}}
    print(f'Integration hashes verified: {len(changes)} files.', flush=True)

    with tempfile.TemporaryDirectory(prefix='unknot-kernels-verify-') as directory:
        tmp = Path(directory)
        for name in ('fast', 'reference', 'dihedral_covers', 'verification'):
            shutil.copytree(ROOT / name, tmp / name,
                            ignore=shutil.ignore_patterns('__pycache__', '.pytest_cache'))

        def run(name, argv, cwd):
            print(f'Checking {name} ...', flush=True)
            tick = time.monotonic()
            completed = subprocess.run([sys.executable, '-B', *argv], cwd=cwd,
                                       text=True, capture_output=True, timeout=600)
            record = {'returncode': completed.returncode,
                      'seconds': time.monotonic() - tick,
                      'stdout': completed.stdout, 'stderr': completed.stderr}
            report['checks'][name] = record
            if completed.returncode:
                print(completed.stdout, file=sys.stderr)
                print(completed.stderr, file=sys.stderr)
                raise RuntimeError(f'{name} failed')
            return completed.stdout + completed.stderr

        log = run('scanner_suite', ['-m', 'unittest', 'discover', '-s', 'tests'], tmp / 'fast')
        match = re.search(r'Ran (\d+) tests', log)
        assert match and int(match.group(1)) == 268, log
        report['checks']['scanner_suite']['test_count'] = int(match.group(1))

        log = run('dihedral_cover_suite', ['test_dihedral_cover.py'], tmp / 'dihedral_covers')
        assert 'Ran 10 tests' in log and 'Expanded-sheet topology comparisons: 13846' in log
        report['checks']['dihedral_cover_suite'].update(test_groups=10, expanded_comparisons=13846)

        run('independent_transfer', ['audit_corridor.py'], tmp / 'verification')
        actual = json.loads((tmp / 'verification/corridor_independent_audit.json').read_text())
        expected = json.loads((ROOT / 'verification/corridor_independent_audit.json').read_text())
        for name in ('status', 'seed', 'diagrams', 'stages', 'comparisons',
                     'complete_special_contractions', 'partial_sparse_stages',
                     'nonzero_minimal_stages', 'reference_sha256', 'corridor_sha256',
                     'dependency_sha256'):
            assert actual[name] == expected[name], (name, actual[name], expected[name])
        report['checks']['independent_transfer']['deterministic_summary'] = {
            name: actual[name] for name in ('diagrams', 'stages', 'comparisons',
                                          'complete_special_contractions')}

        run('graded_support', ['audit_graded_support.py', '--output', str(tmp / 'support.json')], tmp / 'fast')
        actual = json.loads((tmp / 'support.json').read_text())
        expected = json.loads((ROOT / 'fast/results/graded_support_20261008.json').read_text())
        for name in ('seed', 'diagrams', 'stages', 'degree_gap_shortcuts',
                     'graded_support_shortcuts', 'additional_shortcuts', 'total_schur_updates'):
            assert actual[name] == expected[name], (name, actual[name], expected[name])
        report['checks']['graded_support']['deterministic_summary'] = {
            key: value for key, value in actual.items() if key != 'data'}

        run('scalar_representation', ['audit_scalar_representation.py', '--output',
                                      str(tmp / 'scalar.json')], tmp / 'fast')
        actual = json.loads((tmp / 'scalar.json').read_text())
        expected = json.loads((ROOT / 'fast/results/scalar_representation_20261008.json').read_text())
        assert actual['status'] == 'passed' and actual['cases'] == expected['cases']
        report['checks']['scalar_representation']['case_count'] = len(actual['cases'])

    report.update(status='passed', seconds=time.monotonic() - started)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'status': report['status'], 'files_verified': report['files_verified'],
                      'checks': list(report['checks']), 'seconds': report['seconds']}, indent=2))


if __name__ == '__main__':
    main()
