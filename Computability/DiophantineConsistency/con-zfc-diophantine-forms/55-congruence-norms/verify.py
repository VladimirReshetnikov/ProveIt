#!/usr/bin/env python3
"""Offline release audit; new mathematics is proved in report.tex and PROOF.md.

Only Python's standard library is required. The delivered tree is not rewritten
by component builders: they run in a temporary copy. REPRODUCTION.json is the
only normal output written alongside this script and is excluded from the seal.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def check_manifest(skip=False):
    path = ROOT / 'MANIFEST.json'
    if skip:
        return {'status': 'SKIPPED', 'reason': 'explicit --skip-manifest authoring option'}
    require(path.is_file(), 'Missing MANIFEST.json; do not treat an unsealed tree as the delivered release.')
    manifest = json.loads(path.read_text())
    for record in manifest['files']:
        p = ROOT / record['path']
        require(p.is_file(), 'Missing sealed file: ' + record['path'])
        require(p.stat().st_size == record['bytes'], 'Size mismatch: ' + record['path'])
        require(digest(p) == record['sha256'], 'Hash mismatch: ' + record['path'])
    return {'status': 'PASS', 'files': len(manifest['files']), 'sha256': digest(path)}


def critical_outputs():
    paths = ['ten/generated/signed10_b2.json', 'ten/generated/source_records.json',
             'ten/generated/METRICS.json', 'fourteen/polynomial.json']
    for component in ('nine_fast', 'nine_majorant'):
        paths.append(component + '/generated/LEDGER.json')
        for domain in ('positive', 'natural'):
            prefix = component + '/generated/calibrated_' + domain
            paths.extend(prefix + suffix + '.json' for suffix in ('', '_certificate', '_degree'))
    return paths


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-manifest', action='store_true',
                        help='Authoring only: run finite checks after intentional local edits.')
    args = parser.parse_args()
    started = time.monotonic()
    seal = check_manifest(args.skip_manifest)
    # The four arithmetic branches must use the exact same complete native tuple.
    native_binding = json.loads((ROOT/'native/coefficients/COEFFICIENT_BINDING.json').read_text())
    for record in native_binding['files']:
        canonical = gzip.decompress((ROOT/'native/coefficients'/record['file']).read_bytes())
        for folder in ('ten/data', 'nine_fast/coefficients', 'nine_majorant/coefficients', 'fourteen/coefficients'):
            candidate = gzip.decompress((ROOT/folder/(record['port']+'.bin.gz')).read_bytes())
            require(candidate == canonical, 'Mixed or altered fixed tuple in ' + folder)
    expected = {p: digest(ROOT / p) for p in critical_outputs()}
    stages = [
        ('Native coefficient regeneration and dependency inventory', ['native/verify_native.py']),
        ('Ten-variable circuit rebuild', ['ten/build.py']),
        ('Ten-variable independent source and degree checks', ['ten/verify.py']),
        ('Fast nine-variable circuit rebuild', ['nine_fast/build_nine.py']),
        ('Independent positive source extraction', ['nine_fast/verify_source.py']),
        ('Fast nine-variable independent circuit and degree checks', ['nine_fast/check_circuits.py']),
        ('Majorant nine-variable circuit rebuild', ['nine_majorant/build_nine.py']),
        ('Majorant exact ring identities', ['nine_majorant/check_ring_identities.py']),
        ('Majorant independent circuit and degree checks', ['nine_majorant/check_circuits.py']),
        ('Fourteen-variable circuit rebuild', ['fourteen/build.py']),
        ('Fourteen-variable independent checks', ['fourteen/verify.py']),
        ('Independent residual-text parser and source DAG check', ['audits/audit_fused_positive_source.py']),
        ('Independent signed guard and constructive Lucas checks',
         ['audits/ten_root_audit.py', '--component', 'ten']),
    ]
    results = []
    environment = os.environ.copy()
    environment['PYTHONDONTWRITEBYTECODE'] = '1'
    with tempfile.TemporaryDirectory(prefix='proveit_congruence_audit_') as tmp:
        release = Path(tmp) / 'release'
        shutil.copytree(ROOT, release,
                        ignore=shutil.ignore_patterns('__pycache__', '*.pyc', 'REPRODUCTION.json'))
        for index, (name, command) in enumerate(stages, 1):
            print(f'[{index}/{len(stages)}] {name}', flush=True)
            t0 = time.monotonic()
            process = subprocess.run([sys.executable, '-B', *command], cwd=release,
                                     env=environment, text=True, capture_output=True)
            if process.returncode:
                sys.stderr.write(process.stdout)
                sys.stderr.write(process.stderr)
                raise RuntimeError(f'Stage failed ({process.returncode}): {name}')
            results.append({'name': name, 'command': [sys.executable, '-B', *command],
                            'status': 'PASS', 'seconds': round(time.monotonic()-t0, 3),
                            'stdout_sha256': hashlib.sha256(process.stdout.encode()).hexdigest(),
                            'stdout': process.stdout.strip(), 'stderr': process.stderr.strip()})
        rebuilt = []
        for path, sha in expected.items():
            require(digest(release / path) == sha, 'Rebuild is not byte-identical: ' + path)
            rebuilt.append({'path': path, 'sha256': sha})
        reports = {}
        for path in ['native/VERIFICATION.json', 'ten/generated/VERIFIED.json',
                     'nine_fast/CIRCUIT_AUDIT.json', 'nine_fast/SOURCE_FUSION_AUDIT.json',
                     'nine_majorant/CIRCUIT_AUDIT.json', 'fourteen/AUDIT.json',
                     'audits/fused_positive_source_audit.json', 'audits/TEN_ROOT_CHECKS.json']:
            if (release / path).is_file():
                reports[path] = json.loads((release / path).read_text())
    result = {'schema': 'proveit-congruence-release-audit-v1', 'status': 'PASS',
              'python_version': sys.version.split()[0], 'manifest': seal,
              'stages_passed': len(results), 'byte_identical_rebuilds': rebuilt,
              'stages': results, 'component_reports': reports,
              'seconds': round(time.monotonic()-started, 3),
              'scope': 'Finite algebra, binding, degree, regeneration, and implementation checks. '
                       'The unbounded semantic equivalences are the stated mathematical proofs. '
                       'No new end-to-end Lean/Rocq or object-language ZFC derivation is asserted.'}
    (ROOT / 'REPRODUCTION.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'status': 'PASS', 'stages': len(results),
                      'byte_identical_generated_files': len(rebuilt),
                      'seconds': result['seconds'], 'report': 'REPRODUCTION.json'}, indent=2))


if __name__ == '__main__':
    main()
