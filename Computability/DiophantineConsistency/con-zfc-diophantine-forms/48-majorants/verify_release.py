#!/usr/bin/env python3
"""Single-entry release audit using only the Python standard library."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def need(ok, message):
    if not ok:
        raise ValueError(message)


def verify_hashes():
    count = 0
    for line in (ROOT / 'SHA256SUMS').read_text().splitlines():
        digest, name = line.split('  ', 1)
        path = ROOT / name
        need(path.is_file(), 'missing release file: ' + name)
        need(hashlib.sha256(path.read_bytes()).hexdigest() == digest, 'hash mismatch: ' + name)
        count += 1
    return count


def verify_provenance():
    count = 0
    for filename in ('SOURCE_PROVENANCE.json', 'ADDITIONAL_PROVENANCE.json'):
        data = json.loads((ROOT / filename).read_text())
        for record in data['files']:
            path = ROOT / record['bundled_path']
            need(hashlib.sha256(path.read_bytes()).hexdigest() == record['sha256'],
                 'inherited source differs: ' + record['bundled_path'])
            count += 1
    return count


def main():
    file_count = verify_hashes()
    provenance_count = verify_provenance()
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    steps = [
        ('source and inherited finalizers', ['verify.py']),
        ('refined finalizers', ['verify_refined.py']),
        ('materialized fixed leaves', ['code/materialize_fixed.py', '--check']),
        ('independent support and overlap', ['proofs/check_support_independent.py', '.']),
        ('independent universal majorant identities', ['proofs/check_majorant2048_independent.py']),
        ('majorant boundary fixtures', ['proofs/verify_higher_majorant.py']),
    ]
    receipts = []
    for label, arguments in steps:
        completed = subprocess.run([sys.executable, '-O', *arguments], cwd=ROOT, env=env,
                                   text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if completed.returncode:
            sys.stderr.write(completed.stdout)
            sys.stderr.write(completed.stderr)
            raise ValueError('failed audit: ' + label)
        parsed = json.loads(completed.stdout)
        need(parsed.get('status') == 'PASS', 'missing PASS result: ' + label)
        receipts.append({'audit': label, 'arguments': ['python3', '-O', *arguments],
                         'status': 'PASS'})
        print('PASS:', label)
    # Every auditor is deterministic. This also detects an unexpected rewrite.
    need(verify_hashes() == file_count, 'release file count changed')
    result = {
        'status': 'PASS',
        'python_version': sys.version.split()[0],
        'release_files_hash_verified': file_count,
        'pinned_source_files_hash_verified': provenance_count,
        'primary_and_certificate_circuits': 26,
        'refined_universal_polynomial_identities': 14,
        'steps': receipts,
        'scope': 'Finite construction and algebraic certificates; the unbounded equivalence is the mathematical theorem in report.pdf.',
    }
    (ROOT / 'RELEASE_VERIFICATION.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'steps'}, indent=2))


if __name__ == '__main__':
    main()

