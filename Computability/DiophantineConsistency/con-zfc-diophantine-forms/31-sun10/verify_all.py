#!/usr/bin/env python3
"""Reproduce the finite audits in this self-contained research supplement.

These checks authenticate literal data and local algebra. They do not constitute
an end-to-end formal proof of the inherited compiler or decide consistency.
Only the Python standard library is required. Run without -O.
"""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'verification'
PIN = '8c6eec9d19ef80538c8e61ff6e0180040583446a'


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def source_pins():
    result = []
    for relative in ['SOURCE_PINS.json', 'coefficients/SOURCE_PINS.json',
                     'positive12/SOURCE_PINS.json', 'quartic31/SOURCE_PINS.json']:
        ledger = ROOT / relative
        data = json.loads(ledger.read_text())
        pin = data.get('commit', data.get('source_commit', data.get('repository_pin')))
        need(pin == PIN, f'Unexpected source snapshot: {ledger}')
        for row in data['files']:
            path = ledger.parent / row['local']
            raw = path.read_bytes()
            actual = hashlib.sha256(raw).hexdigest()
            need(actual == row['sha256'], f'Source SHA-256 mismatch: {path}')
            expected_blob = row.get('git_blob_sha1', row.get('remote_git_blob_sha1'))
            if expected_blob:
                blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
                need(blob == expected_blob, f'Source Git blob mismatch: {path}')
            result.append({'path': str(path.relative_to(ROOT)), 'sha256': actual})
    return result


def run_script(label, relative, *args):
    script = ROOT / relative
    env = os.environ.copy()
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    print(label, flush=True)
    completed = subprocess.run([sys.executable, str(script), *args],
                               cwd=script.parent, env=env,
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                               text=True, check=False)
    log = OUT / (label + '.log')
    log.write_text(completed.stdout)
    if completed.returncode:
        print(completed.stdout[-12000:], file=sys.stderr)
        raise RuntimeError(f'{label} failed; see {log}')
    return {'check': label, 'status': 'PASS', 'log': str(log.relative_to(ROOT))}


def machine_binding():
    raw = (ROOT / 'sources/k215.tm').read_bytes()
    exported = json.loads((ROOT / 'coefficients/upstream/k215_transitions.json').read_text())
    need(hashlib.sha256(raw).hexdigest() == exported['source_sha256']['tm'],
         'The native compiler export does not match the pinned K215 machine.')
    rows = []
    for line in raw.decode().splitlines():
        if not line or line.startswith('#'):
            continue
        q, a, b, move, target = line.split()
        need(move in ('L', 'R'), 'Unrecognized machine move.')
        rows.append([int(q), int(a), int(b), -1 if move == 'L' else 1, int(target)])
    need(rows == exported['transitions'] and len(rows) == 430,
         'Literal machine transition mismatch.')
    return {'status': 'PASS', 'literal_transitions': 430,
            'machine_sha256': hashlib.sha256(raw).hexdigest()}


def main():
    need(__debug__, 'Run without Python -O: exact assertions are part of the audits.')
    need(sys.version_info >= (3, 11), 'Python 3.11 or later is required.')
    OUT.mkdir(exist_ok=True)
    pins = source_pins()
    machine = machine_binding()
    jobs = [
        ('01_coefficients', 'coefficients/build_coefficients.py', []),
        ('02_coefficients_independent', 'positive12/audit_coefficients_independent.py', []),
        ('03_signed10_build', 'signed10/build_signed10.py', []),
        ('04_signed10_verify', 'signed10/verify_signed10.py', []),
        ('05_signed10_independent', 'signed10/audit_signed10_independent.py', []),
        ('06_signed16_build', 'signed16/build_signed16.py', []),
        ('07_signed16_verify', 'signed16/verify_signed16.py', []),
        ('08_signed16_independent', 'quartic31/audit_signed16_independent.py',
         ['--signed-dir', str(ROOT / 'signed16')]),
        ('09_positive12_build', 'positive12/build_refactored12.py', []),
        ('10_positive12_verify', 'positive12/check_refactored12.py', []),
        ('11_quartic31', 'quartic31/build_quartic60.py', []),
    ]
    results = [run_script(label, path, *args) for label, path, args in jobs]
    s10 = json.loads((ROOT / 'signed10/generated/VERIFICATION.json').read_text())
    s16 = json.loads((ROOT / 'signed16/generated/VERIFICATION.json').read_text())
    need(s10['status'] == 'PASS' and s16['status'] == 'PASS', 'Missing successful receipt.')
    primary10 = next(v for v in s10['variants'] if v['file'] == 'signed10.json')
    need(primary10['total_operations'] == 1442, 'Unexpected ten-variable gate count.')
    need(primary10['exact_degree'] == 126496 * 5**31 + 27064,
         'Unexpected ten-variable degree.')
    need(s16['total_operations'] == 1617, 'Unexpected sixteen-variable gate count.')
    need(s16['exact_degree'] == 813056 * 5**32 + 10016,
         'Unexpected sixteen-variable degree.')
    summary = {
        'status': 'PASS', 'source_commit': PIN,
        'scope': 'Finite source, data, algebra and circuit checks; ordinary semantic proofs are in report.pdf.',
        'source_files_authenticated': len(pins), 'source_checks': pins,
        'machine_binding': machine,
        'checks': results,
        'signed10': {k: primary10[k] for k in ['unknowns', 'total_operations', 'exact_degree']},
        'signed16': {k: s16[k] for k in ['variables', 'total_operations', 'exact_degree']},
        'no_new_end_to_end_kernel_certificate': True,
    }
    (OUT / 'SUMMARY.json').write_text(json.dumps(summary, indent=2) + '\n')
    print('PASS: all eleven audit stages and source authentication completed.', flush=True)


if __name__ == '__main__':
    main()
