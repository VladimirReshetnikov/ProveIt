#!/usr/bin/env python3
"""Recheck the delivered polynomials in a disposable copy, using only stdlib.

This checks finite algebra and certificate data, not the consistency of ZFC.
It deliberately does not overwrite any delivered equation or receipt.
"""
import argparse
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


def require(condition, explanation):
    if not condition:
        raise ValueError(explanation)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--optimized', action='store_true',
                        help='run component checks with Python -O')
    parser.add_argument('--output', type=Path,
                        help='optional JSON receipt destination')
    args = parser.parse_args()
    optimized = args.optimized or not __debug__
    python = [sys.executable] + (['-O'] if optimized else [])
    records, comparisons = [], []
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    started = time.monotonic()
    with tempfile.TemporaryDirectory(prefix='conzfc-verification-') as td:
        work = Path(td)
        for component in ('nine', 'integer14', 'direct'):
            shutil.copytree(ROOT / component, work / component,
                            ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))

        def run(relative_script, *arguments):
            script = work / relative_script
            print('Checking ' + relative_script, flush=True)
            result = subprocess.run(python + [str(script)] + list(map(str, arguments)),
                                    cwd=script.parent, env=env, capture_output=True,
                                    text=True)
            require(result.returncode == 0,
                    relative_script + ' failed:\n' + result.stdout + result.stderr)
            records.append({'script': relative_script, 'status': 'PASS',
                            'stdout_sha256': hashlib.sha256(result.stdout.encode()).hexdigest()})

        def same(relative, rebuilt):
            actual = ROOT / relative
            require(actual.read_bytes() == rebuilt.read_bytes(),
                    'Reconstruction differs: ' + relative)
            comparisons.append({'path': relative, 'sha256': digest(actual)})

        # First check the delivered data, before running any producer.
        for script in ('verify.py', 'normalization_check.py', 'exact_audit.py',
                       'verify_coefficients.py'):
            run('nine/' + script)
        run('integer14/verify.py')
        run('direct/code/audit_projected.py', '--equations', work / 'direct/equations_v3',
            '--output', work / 'direct_audit.json')
        run('direct/code/check_domain_certificate.py')
        run('direct/code/domain_negative_controls.py')
        run('direct/code/verify_integer.py')

        # Reconstruct literal artifacts, then compare with the delivered bytes.
        run('nine/build.py')
        for path in sorted((ROOT / 'nine/equations').glob('*.json')):
            rel = path.relative_to(ROOT).as_posix()
            same(rel, work / rel)
        for path in sorted((ROOT / 'nine/fixed').rglob('*')):
            if path.is_file():
                rel = path.relative_to(ROOT).as_posix()
                same(rel, work / rel)
        run('integer14/build.py')
        for name in ('crt14_degree540.json', 'crt14_degree568.json'):
            rel = 'integer14/' + name
            same(rel, work / rel)
        run('direct/code/build_projected.py', '--output', work / 'rebuilt_direct')
        for sub in ('source', 'cap64'):
            for path in sorted((ROOT / 'direct/equations_v3' / sub).glob('*.json')):
                rel = path.relative_to(ROOT).as_posix()
                same(rel, work / 'rebuilt_direct' / sub / path.name)
        run('direct/code/build_domain_certificate.py')
        for name in ('DOMAIN_CERTIFICATE.json', 'RAW_FRAME_INTERFACE.json'):
            same('direct/' + name, work / 'direct' / name)
        run('direct/code/build_integer.py', '--output', work / 'rebuilt_integer')
        for path in sorted((ROOT / 'direct/integer977').glob('*.json')):
            same(path.relative_to(ROOT).as_posix(), work / 'rebuilt_integer' / path.name)

        # Verify the pinned immediate logical sources as literal files.
        calibration = ROOT / 'direct/provenance/upstream/calibration'
        pins = json.loads((calibration / 'CALIBRATION_PINS.json').read_text())
        pin_checks = []
        for item in pins['files']:
            source = calibration / item['local_file']
            if not source.exists():
                source = calibration.parent / item['local_file']
            require(source.is_file(), 'Missing calibration source: ' + item['local_file'])
            require(digest(source) == item['sha256'], 'Calibration digest mismatch: ' + str(source))
            pin_checks.append(item['local_file'])

    receipt = {
        'status': 'PASS', 'optimized_python': optimized,
        'component_checks': records, 'byte_exact_reconstructions': comparisons,
        'calibration_pins_checked': pin_checks,
        'elapsed_seconds': round(time.monotonic() - started, 3),
        'scope': 'Exact finite algebra, reconstruction and rejection controls. '
                 'The unbounded existence equivalence uses the ordinary proofs and '
                 'explicit inherited calibration. No consistency decision or new kernel proof.'}
    rendered = json.dumps(receipt, indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)
    print(rendered, end='')


if __name__ == '__main__':
    main()
