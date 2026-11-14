#!/usr/bin/env python3
"""Rebuild and independently audit PA194Q5/Q6 using bundled files only.

Python 3.10+; standard library; assertions enabled. No network or checkout.
Outputs go to reproduced/ by default. The optional historical corpus rescan
and heuristic searches are separate from this deterministic verification.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    if sys.version_info < (3, 10):
        raise RuntimeError('Python 3.10 or later is required.')
    if not __debug__ or sys.flags.optimize:
        raise RuntimeError('Assertions must be enabled; do not use -O.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT / 'reproduced')
    args = parser.parse_args()
    output = args.output.resolve()
    require(output != ROOT, 'Choose a separate output directory.')
    output.mkdir(parents=True, exist_ok=True)
    logs = output / 'logs'
    logs.mkdir(exist_ok=True)
    started = time.monotonic()
    checks = []

    manifest = ROOT / 'SHA256SUMS'
    if manifest.exists():
        checked = 0
        for line in manifest.read_text().splitlines():
            expected, name = line.split('  ', 1)
            path = (ROOT / name).resolve()
            require(path.is_relative_to(ROOT), 'Unsafe manifest path.')
            require(path.is_file() and digest(path) == expected, f'Hash mismatch: {name}')
            checked += 1
        checks.append({'check': 'archive_manifest', 'files': checked, 'status': 'PASS'})
        print(f'Archive manifest: {checked} files PASS', flush=True)

    literal = json.loads((ROOT / 'comparison/current_census/census.json').read_text())
    encoded = json.loads((ROOT / 'comparison/json_census/census.json').read_text())
    left = {r['graph_hash'] for r in literal['identities'] if r['graph_hash']}
    right = {r['graph_hash'] for r in encoded['identities'] if r['graph_hash']}
    require((len(left), len(right - left), len(left | right)) == (497, 4, 501),
            'Census class counts differ from the report.')
    ledger = json.loads((ROOT / 'comparison/packet_ledger.json').read_text())['packets']
    require(len(ledger) == 54 and sum(p['location'] == 'placed' for p in ledger) == 51,
            'Packet coverage differs from the report.')
    require(all(p.get('principal_status') for p in ledger), 'A packet lacks its status.')
    checks.append({'check': 'recorded_census_union', 'status': 'PASS', 'classes': 501, 'packets': 54,
                   'scope': 'Checks the included recorded census, not a fresh external checkout scan.'})

    def run(label, script, arguments):
        command = [sys.executable, '-B', str(ROOT / script), *map(str, arguments)]
        print(f'{label}: running', flush=True)
        before = time.monotonic()
        with (logs / f'{label}.log').open('w') as log:
            result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
        require(result.returncode == 0, f'{label} failed; see {logs / (label + ".log")}')
        checks.append({'check': label, 'status': 'PASS', 'seconds': round(time.monotonic() - before, 3)})
        print(f'{label}: PASS', flush=True)

    exchange = output / 'exchange_certificate.json'
    run('exchange', 'verification/exchange_certificate.py', ['--output', exchange])
    require(digest(exchange) == digest(ROOT / 'verification/exchange_certificate.json'),
            'Exchange certificate is not the frozen certificate.')

    run('construction', 'construction/build.py', ['--output', output / 'machines'])
    machines = [output / 'machines' / f'PA194Q{k}' for k in (5, 6)]
    for machine in machines:
        original = ROOT / 'machines' / machine.name
        for name in ('machine.tm', 'machine.native.tm', 'raw202.native.tm', 'labels.json',
                     'nodes.json', 'folds.json', 'local_fold_cases.json', 'source_binding.json',
                     'emitter_audit.json', 'instructions.json', 'sites.json', 'macro_word.json',
                     'q_change.json', 'receipt.json'):
            require(digest(machine / name) == digest(original / name),
                    f'Reconstruction differs: {machine.name}/{name}')
    checks.append({'check': 'byte_identical_reconstruction', 'status': 'PASS', 'files': 28})

    run('independent_source', 'verification/independent/source_audit.py',
        [*machines, '--output', output / 'independent'])
    run('independent_tape', 'verification/independent/check.py',
        [*machines, '--output', output / 'independent'])
    for machine in machines:
        receipt = json.loads((output / 'independent' / machine.name / 'receipt.json').read_text())
        require(receipt['status'] == 'PASS' and receipt['dense_sha256'] == digest(machine / 'machine.tm'),
                f'Independent receipt mismatch: {machine.name}')
        novelty = output / f'{machine.name}_novelty.json'
        run(f'novelty_{machine.name}', 'comparison/novelty.py', [machine / 'machine.tm', '--output', novelty])
        proof = json.loads(novelty.read_text())
        require(proof['prior_194_classes_checked'] == 40 and not proof['matches'],
                f'Unexpected prior graph match: {machine.name}')

    result = {'status': 'PASS', 'checks': checks, 'seconds': round(time.monotonic() - started, 3),
              'proof_scope': 'Deterministic executable construction and physical/source certificates. '
              'The ordinary PA calibration is the mathematical argument in report/pa194_qradix.pdf; '
              'this is not an end-to-end proof-assistant theorem.'}
    (output / 'receipt.json').write_text(json.dumps(result, indent=2) + '\n')
    print(f'All deterministic checks PASS; receipts and logs: {output}', flush=True)


if __name__ == '__main__':
    main()
