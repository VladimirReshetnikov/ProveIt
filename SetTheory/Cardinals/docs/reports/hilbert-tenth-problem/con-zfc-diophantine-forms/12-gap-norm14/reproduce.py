#!/usr/bin/env python3
"""Reproduce the finite audits. Python standard library only; no network.

These computations check finite identities and compiler data. They neither
decide Con(ZFC) nor kernel-check the unbounded mathematical proof.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    if sys.flags.optimize:
        raise SystemExit("Run without -O: some exact symbolic audits use assertions.")
    provenance = json.loads((ROOT / 'provenance.json').read_text())
    source_checks = []
    for item in provenance['retained_upstream_files']:
        path = ROOT / item['archive_path']
        data = path.read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        if blob != item['git_blob_sha1']:
            raise ValueError('Upstream file identity failed: ' + item['archive_path'])
        if digest(path) != item['sha256']:
            raise ValueError('Upstream SHA-256 failed: ' + item['archive_path'])
        source_checks.append(item['archive_path'])
    steps = [
        ('ordinary arithmetic', ['arithmetic/build_improved.py']),
        ('root elimination', ['arithmetic/build_fourteen.py']),
        ('auxiliary gap', ['arithmetic/build_gap.py']),
        ('independent symbolic gap identities', ['quadratic/check_gap_identities.py']),
        ('quadratic lift', ['quadratic/build_quartic32.py']),
        ('cross compiler and source census', [
            'compiler/cross_constants.py', '--tm', 'compiler/k215.tm',
            '--output', 'compiler/cross_constants.json']),
        ('independent actual geometry', [
            'compiler/review_cross_geometry.py', '--source', 'compiler/cross_constants.json',
            '--output', 'compiler/cross_geometry_review.json']),
    ]
    receipts = []
    log_dir = ROOT / 'verification'
    log_dir.mkdir(exist_ok=True)
    for number, (name, args) in enumerate(steps, 1):
        print(f'[{number}/{len(steps)}] {name}', flush=True)
        result = subprocess.run([sys.executable, *args], cwd=ROOT,
                                text=True, capture_output=True)
        log = log_dir / f'{number:02d}.log'
        log.write_text(result.stdout + result.stderr)
        receipts.append({'name': name, 'arguments': args,
                         'exit_code': result.returncode,
                         'log': str(log.relative_to(ROOT))})
        if result.returncode:
            print(result.stdout + result.stderr)
            raise SystemExit(result.returncode)
    coefficient_packet = json.loads((ROOT / 'compiler/cross_constants.json').read_text())
    geometry = coefficient_packet['constants']['geometry']
    if geometry['cell_bits'] != 5 ** 36:
        raise ValueError('Unexpected coefficient bit length')
    circuits = []
    for path in sorted((ROOT / 'arithmetic').glob('*.json')):
        packet = json.loads(path.read_text())
        if 'source' not in packet or 'ledger' not in packet:
            continue
        circuits.append({
            'file': str(path.relative_to(ROOT)), 'name': packet['name'],
            'unknowns': len(packet['witnesses']), 'domain': packet['witness_domain'],
            'equations': len(packet.get('comparisons', [None])),
            'degree': packet.get('exact_degree', packet.get('exact_maximum_degree')),
            'operations': packet['ledger']['operations'],
            'multiplications': packet['ledger']['multiplications'],
            'sha256': digest(path),
        })
    record = {
        'status': 'PASS', 'repository_pin': provenance['repository_pin'],
        'upstream_files_authenticated': source_checks,
        'steps': receipts, 'arithmetic_presentations': circuits,
        'coefficient_geometry': geometry,
        'source_census': coefficient_packet.get('source_verification'),
        'independent_geometry': json.loads((ROOT / 'compiler/cross_geometry_review.json').read_text()),
        'independent_gap_identities': json.loads((ROOT / 'quadratic/gap_independent_review.json').read_text()),
        'formal_proof_status': 'Ordinary mathematical proof with inherited dependencies; no new Lean or Rocq kernel proof.',
        'scope': 'Exact finite identities, circuit ledgers, degree diagnostics and certificates, table identity, local census, sparse compiler geometry, and bounded cyclic checks.',
        'not_checked_by_this_program': [
            'Unbounded Pell and native compiler theorems',
            'A fresh Lean/Rocq build of the existing K215 endpoint',
            'Any accepting computation of the actual K215 machine',
            'The binary expansion of the astronomical fixed coefficients',
            'Consistency or inconsistency of ZFC',
        ],
    }
    (ROOT / 'verification.json').write_text(json.dumps(record, indent=2) + '\n')
    print(f'PASS: {len(source_checks)} exact upstream files; {len(steps)} audit stages; '
          f'{len(circuits)} arithmetic presentations.')
    print('Finite-check receipt: verification.json')


if __name__ == '__main__':
    main()
