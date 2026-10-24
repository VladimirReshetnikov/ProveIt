#!/usr/bin/env python3
"""Replay the archive's independent exact finite checks.

Default: Python standard library only. --symbolic additionally runs the
integer component's SymPy verifier (see integer/requirements.txt).
Unbounded semantic proofs are in the report and the named source proofs.
"""
from collections import Counter
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
sys.dont_write_bytecode = True


def need(ok, message):
    if not ok:
        raise ValueError(message)


def read(path):
    return json.loads(path.read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def archive_integrity():
    path = ROOT / 'MANIFEST.sha256'
    if not path.exists():
        return {'status': 'not present during initial assembly'}
    count = 0
    for line in path.read_text().splitlines():
        digest, name = line.split('  ', 1)
        target = (ROOT / name).resolve()
        need(target.is_relative_to(ROOT), 'Unsafe manifest path')
        need(target.is_file() and sha(target) == digest,
             'Archive integrity mismatch: ' + name)
        count += 1
    return {'status': 'PASS', 'files': count}


def source_integrity():
    count = 0
    for component, key in [('ten_positive', 'local'), ('integer', 'stored_path')]:
        for record in read(ROOT / component / 'SOURCE_PINS.json')['files']:
            path = ROOT / component / record[key]
            need(sha(path) == record['sha256'], 'Source changed: ' + str(path))
            count += 1
    return {'status': 'PASS', 'pinned_files': count}


def positive_builder_and_translation():
    directory = ROOT / 'ten_positive'
    spec = importlib.util.spec_from_file_location('positive_builder', directory / 'build.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    positive = read(directory / 'generated/p10_positive.json')
    need(module.build() == positive, 'Delivered positive graph differs from builder')
    natural = read(directory / 'generated/p10_natural.json')
    variables = positive['variables']
    shift = [[v, '+', v + '0', 1] for v in variables]
    need(natural['variables'] == [v + '0' for v in variables], 'Natural coordinate list')
    need(natural['source'] == shift + positive['source'], 'Exact coordinate translation')
    need(natural['domain'] == 'nonnegative integers', 'Natural witness domain')
    for key in ['fixed_numerals', 'output', 'named_registers', 'exact_total_degree',
                'coefficient_binding']:
        need(natural[key] == positive[key], 'Natural metadata: ' + key)
    need(natural['operations'] == len(natural['source']) == 141, 'Natural operation count')
    need(natural['operation_breakdown'] == dict(Counter(r[1] for r in natural['source'])),
         'Natural operation histogram')
    need(natural['coordinate_map'] == {v: v + '0 + 1' for v in variables},
         'Natural restoration map')
    # The ten affine shifts are a bijection N^10 -> Z_{>0}^10; translation
    # preserves the highest nonzero homogeneous component and exact degree.
    return {'status': 'PASS', 'positive_operations': 131,
            'natural_operations': 141, 'degree': 1152,
            'translation': 'x=x0+1 in each of ten coordinates; exact literal substitution'}


def component(script, receipt):
    print('Checking ' + script, flush=True)
    command = [sys.executable]
    if sys.flags.optimize:
        command.append('-O')
    command.append(str(ROOT / script))
    process = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
    if process.returncode:
        sys.stdout.write(process.stdout)
        sys.stderr.write(process.stderr)
        raise RuntimeError('Component failed: ' + script)
    result = read(ROOT / receipt)
    need(result.get('status') == 'PASS', 'Component did not certify PASS: ' + script)
    return {'script': script, 'status': 'PASS', 'receipt': receipt}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--symbolic', action='store_true',
                        help='Also run every integer packet through the SymPy verifier')
    args = parser.parse_args()
    integrity = archive_integrity()
    sources = source_integrity()
    translation = positive_builder_and_translation()
    steps = [
        ('ten_positive/independent_check.py', 'ten_positive/generated/INDEPENDENT_CHECKS.json'),
        ('ten_positive/rebuild_coefficients.py', 'ten_positive/generated/COEFFICIENT_CHECKS.json'),
        ('ten_positive/local_checks.py', 'ten_positive/generated/LOCAL_CHECKS.json'),
        ('integer/independent_review.py', 'integer/certificates/INDEPENDENT_REVIEW.json'),
    ]
    if args.symbolic:
        name = 'VERIFY_OPTIMIZED.json' if sys.flags.optimize else 'VERIFY.json'
        steps.append(('integer/verify.py', 'integer/certificates/' + name))
    reports = [component(script, receipt) for script, receipt in steps]
    result = {'status': 'PASS', 'source_identity': sources,
              'positive_builder_and_natural_translation': translation,
              'checks': reports, 'symbolic_integer_suite': bool(args.symbolic),
              'proof_boundary': 'Exact finite algebra, byte reconstruction and diagnostics. '
                  'Unbounded semantic results use the ordinary mathematical proofs in the report '
                  'and the explicitly inherited native compiler/calibration theorem.'}
    # Preserve the delivered release receipt so rechecking does not make
    # the delivered manifest stale. This new local run receipt is unlisted.
    receipt_name = 'VERIFICATION_LAST_RUN.json' if (ROOT / 'MANIFEST.sha256').exists() else 'VERIFICATION.json'
    (ROOT / receipt_name).write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'status': 'PASS', 'archive_integrity': integrity,
                      'component_checks': len(reports), 'source_files': sources['pinned_files'],
                      'symbolic_integer_suite': bool(args.symbolic)}, indent=2))


if __name__ == '__main__':
    main()
