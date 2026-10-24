#!/usr/bin/env python3
"""Replay all finite certificates offline, using Python's standard library.

Run normally and with -O. This verifies explicit data and algebra, not ZFC's
consistency. The universal mathematical proofs and inherited proof boundary
are in report.tex/report.pdf and the retained proof texts.
"""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def require(value, message):
    if not value:
        raise ValueError(message)


def file_identity(path, sha256=None, git_blob=None):
    data = path.read_bytes()
    if sha256:
        require(hashlib.sha256(data).hexdigest() == sha256,
                'SHA-256 identity: '+str(path.relative_to(ROOT)))
    if git_blob:
        actual = hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        require(actual == git_blob, 'Git blob identity: '+str(path.relative_to(ROOT)))


def check_sources():
    count = 0
    pins = json.loads((ROOT/'SOURCE_PINS.json').read_text())
    for row in pins['files']:
        file_identity(ROOT/row['relative_path'], row['sha256'], row['git_blob'])
        count += 1
    machine = pins['literal_machine']
    file_identity(ROOT/machine['relative_path'], machine['sha256'])
    actions = []
    for line in (ROOT/machine['relative_path']).read_text().splitlines():
        if line and not line.startswith('#'):
            q, b, w, direction, target = line.split()
            require(direction in ('L', 'R'), 'literal machine direction')
            actions.append([int(q), int(b), int(w),
                            1 if direction == 'R' else -1, int(target)])
    expected = json.loads((ROOT/'positive12/native/k215_transitions.json').read_text())['transitions']
    require(sorted(actions) == sorted(expected) and len(actions) == 430,
            'literal transition equivalence with pinned native JSON')
    count += 1
    p12 = json.loads((ROOT/'positive12/PROVENANCE.json').read_text())
    for row in p12['sources']:
        file_identity(ROOT/'positive12'/row['local'], row['sha256'], row['git_blob_sha1'])
        count += 1
    p9 = json.loads((ROOT/'nine_positive/PROVENANCE.json').read_text())
    for row in p9['unchanged_imports']:
        file_identity(ROOT/'nine_positive'/row['path'], row['sha256'])
        count += 1
    return count


def main():
    require(sys.version_info >= (3, 10), 'Python 3.10 or newer is required')
    source_count = check_sources()
    print('PASS: '+str(source_count)+' pinned source identities.', flush=True)
    commands = [
        'build_coefficients.py',
        'check_determinant_guard.py',
        'build_integer_forms.py',
        'check_integer_independent.py',
        'positive12/native/build_coefficients.py',
        'positive12/build.py',
        'positive12/check.py',
        'nine_positive/coefficients/build_coefficients.py',
        'nine_positive/build_composed.py',
        'nine_positive/check_composed.py',
    ]
    env = dict(os.environ)
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    env['PYTHONHASHSEED'] = '0'
    env['PYTHONOPTIMIZE'] = str(sys.flags.optimize)
    records = []
    for script in commands:
        command = [sys.executable, '-B'] + ['-O']*sys.flags.optimize + [str(ROOT/script)]
        result = subprocess.run(command, cwd=ROOT, env=env, capture_output=True, text=True)
        if result.returncode:
            print(result.stdout)
            print(result.stderr, file=sys.stderr)
            raise SystemExit('FAILED: '+script)
        # Include deterministic hashes of each complete textual check receipt.
        records.append({'script': script, 'status': 'PASS',
                        'stdout_sha256': hashlib.sha256(result.stdout.encode()).hexdigest()})
        print('PASS: '+script, flush=True)
    summary = {
        'status': 'PASS', 'optimization': sys.flags.optimize,
        'pinned_source_identities': source_count, 'commands': records,
        'integer_forms': json.loads((ROOT/'certificates/INTEGER_AUDIT.json').read_text()),
        'positive12': {'variables': 12, 'domain': 'strictly positive integers',
                       'degree': 110, 'operations': 102},
        'positive9': {'variables': 9, 'domain': 'strictly positive integers',
                      'degree': 1379730, 'operations': 478},
        'natural9': {'variables': 9, 'domain': 'nonnegative integers',
                     'degree': 1379730, 'operations': 485},
        'scope': 'Exact finite construction and identity replay; universal reductions are ordinary mathematical proofs with explicitly inherited native/Pell/refutation dependencies.'
    }
    suffix = '_optimized' if sys.flags.optimize else '_normal'
    output = ROOT/'certificates'/('VERIFICATION'+suffix+'.json')
    output.write_text(json.dumps(summary, indent=2)+'\n')
    print('All finite certificates passed. See '+str(output.relative_to(ROOT))+'.')


if __name__ == '__main__':
    main()
