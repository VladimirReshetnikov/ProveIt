#!/usr/bin/env python3
"""Reproduce the exact algebraic checks and builders in this research package."""
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def verify_manifest():
    manifest = ROOT / 'MANIFEST.json'
    if not manifest.exists():
        return
    entries = json.loads(manifest.read_text())['files']
    for name, entry in entries.items():
        target = ROOT / name
        if not target.is_file():
            raise ValueError('Missing delivered file: ' + name)
        data = target.read_bytes()
        if len(data) != entry['bytes'] or sha256(data).hexdigest() != entry['sha256']:
            raise ValueError('Manifest mismatch: ' + name)
    print('PASS: complete delivered-file manifest', flush=True)


def main():
    verify_manifest()
    optimized = bool(sys.flags.optimize)
    flags = ['-B'] + (['-O'] if optimized else [])
    suffix = '_OPTIMIZED' if optimized else ''
    commands = [
        ('exact inherited source and calibration identities', ['check_sources.py']),
        ('twelve-integer mixed-modulus independent algebra',
         ['crt12/check.py', '--output', f'crt12/CHECK{suffix}.json']),
        ('twelve-integer weak-carrier independent algebra',
         ['height12/check.py', '--output', f'height12/CHECK{suffix}.json']),
        ('second independent mixed-modulus audit', ['peer/peer_crt.py']),
        ('seven-sign-pair direct independent checks',
         ['direct589/check_equal_sum.py', '--output',
          f'direct589/INDEPENDENT_CHECK{suffix}.json']),
        ('even-index direct independent checks',
         ['direct566/check_even_index.py', '--output',
          f'direct566/INDEPENDENT_CHECK{suffix}.json']),
        ('mixed-modulus exact deterministic rebuild', ['crt12/build.py', '--check']),
        ('weak-carrier exact deterministic rebuild', ['height12/build.py', '--check']),
        ('seven-sign-pair exact deterministic rebuild',
         ['direct589/build_equal_sum.py', '--check']),
        ('even-index exact deterministic rebuild',
         ['direct566/build_even_index.py', '--check']),
    ]
    results = []
    for name, args in commands:
        result = subprocess.run([sys.executable] + flags + args, cwd=ROOT,
                                capture_output=True, text=True)
        if result.returncode:
            sys.stderr.write(result.stdout)
            sys.stderr.write(result.stderr)
            raise RuntimeError('Verification failed: ' + name)
        results.append({'name': name, 'arguments': flags + args,
                        'exit_code': 0, 'status': 'PASS'})
        print('PASS: ' + name, flush=True)
    report = {'status': 'PASS', 'optimized_python': optimized,
              'checks': results,
              'scope': 'Exact finite algebra, coefficient authentication, '
                       'integer restorations, corruption controls and '
                       'deterministic reproduction. Unbounded ordinary '
                       'proofs and inherited logical calibration remain '
                       'separate mathematical dependencies.'}
    directory = ROOT / 'verification'
    directory.mkdir(exist_ok=True)
    output = directory / ('optimized.json' if optimized else 'normal.json')
    output.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print('PASS: all ' + str(len(commands)) + ' stages' +
          (' (Python -O)' if optimized else ''), flush=True)


if __name__ == '__main__':
    main()
