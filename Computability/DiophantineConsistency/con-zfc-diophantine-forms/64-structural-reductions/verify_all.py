#!/usr/bin/env python3
"""Reproduce finite certificates in temporary copies; no semantic oracle.

Python 3.10+, standard library only.  The universal existence equivalences
are mathematical proofs in the paper/component proof files.  This driver
checks data, algebra, counts, degree certificates, and reproducibility.
"""
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def check_baselines():
    pins = json.loads((ROOT / 'review/BASELINE_PINS.json').read_text())
    for row in pins['files']:
        raw = (ROOT / row['path']).read_bytes()
        actual = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
        require(actual == row['git_blob_sha1'], 'Baseline blob mismatch: ' + row['path'])
    return len(pins['files'])


def raw_ports(directory):
    return {p.name: sha256(gzip.decompress(p.read_bytes()))
            for p in sorted(directory.glob('*.bin.gz'))}


def run_script(component, script, optimized, logs):
    command = [sys.executable] + (['-O'] if optimized else []) + [str(component / script)]
    env = dict(os.environ)
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    completed = subprocess.run(command, cwd=component, env=env,
                               text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    logs.append({'component': component.name, 'script': script,
                 'optimized': optimized, 'exit_code': completed.returncode,
                 'output': completed.stdout})
    require(completed.returncode == 0,
            '{} / {} failed:\n{}'.format(component.name, script, completed.stdout[-12000:]))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--optimized', action='store_true',
                        help='also replay all new checkers with python -O')
    args = parser.parse_args()
    require(sys.version_info >= (3, 10), 'Python 3.10 or later is required')
    baseline_count = check_baselines()
    logs = []
    definitions = {
        'positive14': ['polynomial.json'],
        'integer41': ['quartic44.json', 'quartic41.json', 'sextic36.json', 'octic31.json'],
        'nine-positive-111': [
            'data/split_code.json', 'data/split_kernels.json',
            'generated/split_111_positive.json', 'generated/split_111_natural.json',
            'generated/split_111_positive_certificate.json',
            'generated/split_111_positive_certificate_degree.json',
            'generated/split_111_natural_certificate.json',
            'generated/split_111_natural_certificate_degree.json'],
    }
    scripts = {
        'positive14': ['build.py', 'verify.py'],
        'integer41': ['build_verify44.py', 'build_verify41.py', 'build_companions.py'],
        'nine-positive-111': ['build_nine.py', 'materialize_fixed.py', 'verify_candidate.py'],
    }
    summaries = {}
    with tempfile.TemporaryDirectory(prefix='con-zfc-replay-') as scratch:
        scratch = Path(scratch)
        for name, selected in definitions.items():
            destination = scratch / name
            shutil.copytree(ROOT / name, destination,
                            ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
            before = {f: sha256((destination / f).read_bytes()) for f in selected}
            for script in scripts[name]:
                run_script(destination, script, False, logs)
            if args.optimized:
                for script in scripts[name]:
                    run_script(destination, script, True, logs)
            after = {f: sha256((destination / f).read_bytes()) for f in selected}
            require(before == after, 'Nonidentical literal regeneration in ' + name)
            summaries[name] = {'literal_files_checked_unchanged': len(selected),
                               'generated_outputs_reproduced_identically': len(selected) - (2 if name == 'nine-positive-111' else 0),
                               'definitions_sha256': after,
                               'normal_run': 'PASS',
                               'optimized_run': 'PASS' if args.optimized else 'not requested'}

        # Run the original native builders separately so their output never
        # alters the authenticated delivered snapshots.
        p14_native = scratch / 'positive14/native'
        old = raw_ports(p14_native / 'coefficients')
        require(len(old) == 4, 'Four compact native ports required')
        run_script(p14_native, 'build_coefficients.py', False, logs)
        require(old == raw_ports(p14_native / 'coefficients'), 'Compact native numeral rebuild')
        run_script(p14_native, 'audit_coefficients.py', False, logs)

        nine_native = scratch / 'nine-positive-111/native'
        old_nine = raw_ports(scratch / 'nine-positive-111/coefficients')
        require(len(old_nine) == 4, 'Four original native ports required')
        run_script(nine_native, 'build_coefficients.py', False, logs)
        require(old_nine == raw_ports(nine_native / 'payloads'), 'Original native numeral rebuild')
        native_summary = {
            'compact_source44_all_four_raw_payloads': 'PASS',
            'compact_source44_independent_native_audit': 'PASS',
            'mixed_source34_all_four_raw_payloads': 'PASS (integer41 auditor)',
            'original_source31_all_four_raw_payloads': 'PASS',
        }

    result = {
        'status': 'PASS',
        'source_pin': 'beb0192cb8dc36f78c369c080f2adfbc1887a486',
        'baseline_blobs_authenticated': baseline_count,
        'components': summaries,
        'native_rebuilds': native_summary,
        'subprocesses_passed': len(logs),
        'scope': 'Finite algebra, fixed data, exact degree/counts and reproduction; '
                 'unbounded equivalences use the mathematical proofs and named inherited results.',
        'not_claimed': ['global optimality', 'consistency or inconsistency',
                        'new end-to-end Lean/Rocq certificate', 'object-language ZFC proof file'],
    }
    out = ROOT / 'certificates'
    out.mkdir(exist_ok=True)
    suffix = '_OPTIMIZED' if args.optimized else ''
    (out / ('ROOT_CHECKS' + suffix + '.json')).write_text(json.dumps(result, indent=2) + '\n')
    (out / ('REPLAY_LOG' + suffix + '.json')).write_text(json.dumps(logs, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
