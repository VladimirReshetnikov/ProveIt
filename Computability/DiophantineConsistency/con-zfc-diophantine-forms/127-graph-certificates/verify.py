#!/usr/bin/env python3
"""Offline release verification. No network, package installation or proof search.

Finite algebra is checked here; unbounded arithmetic and the inherited
consistency calibration are ordinary proofs in the article/source texts.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def digest(data):
    return hashlib.sha256(data).hexdigest()


def verify_manifest():
    path = ROOT / 'MANIFEST.json'
    data = json.loads(path.read_text())
    for name, entry in data['files'].items():
        p = ROOT / name
        if not p.is_file():
            raise ValueError('Missing release file: ' + name)
        raw = p.read_bytes()
        if len(raw) != entry['bytes'] or digest(raw) != entry['sha256']:
            raise ValueError('Changed release file: ' + name)
    return len(data['files'])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--receipt', type=Path)
    parser.add_argument('--optimized', action='store_true',
                        help='Run new algebra checkers with Python -O')
    parser.add_argument('--manifest-only', action='store_true')
    parser.add_argument('--skip-manifest', action='store_true',
                        help='For intentional authoring before a manifest is sealed')
    parser.add_argument('--rebuild-graphs', action='store_true')
    args = parser.parse_args()
    if not args.skip_manifest:
        count = verify_manifest()
        print('Release manifest verified: ' + str(count) + ' files', flush=True)
    if args.manifest_only:
        if args.skip_manifest:
            raise ValueError('Manifest-only cannot skip the manifest')
        return
    py = [sys.executable, '-B'] + (['-O'] if args.optimized else [])
    profiles = json.loads((ROOT / 'graph/PROFILES.json').read_text())
    commands = []
    for profile in profiles:
        commands.append(('graph/' + profile['name'], py + [
            'graph/verify_graph.py', '--source', 'graph/' + profile['source'],
            '--artifact-dir', 'graph/' + profile['name'], '--mutations']))
    commands.extend([
        ('direct/natural', py + ['direct/verify.py']),
        ('direct/integer381', py + ['direct/check_signed_cap.py', 'direct/integer381']),
        ('direct/integer391', py + ['direct/check_signed_cap.py', 'direct/integer391']),
        ('low_variable/circuits', py + ['low_variable/verify.py']),
        ('low_variable/fixed_numerals', [sys.executable, '-B', 'low_variable/verify_coefficients.py']),
        ('report/literal_residuals', py + ['report/check_residuals.py']),
    ])
    if args.rebuild_graphs:
        commands.append(('graph/deterministic_rebuild', py + ['graph/rebuild.py']))
    results = []
    for name, command in commands:
        print('Checking ' + name, flush=True)
        process = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
        if process.returncode:
            raise RuntimeError(name + ' failed\n' + process.stdout[-4000:] + '\n' + process.stderr[-4000:])
        result = {'stage': name, 'exit_code': process.returncode,
                  'command': ['python3'] + command[1:],
                  'stdout_sha256': digest(process.stdout.encode()),
                  'stderr_sha256': digest(process.stderr.encode())}
        try:
            result['checker_report'] = json.loads(process.stdout)
        except json.JSONDecodeError:
            result['stdout_bytes'] = len(process.stdout.encode())
        results.append(result)
    receipt = {'status': 'PASS', 'optimized_new_checkers': args.optimized,
               'stages': results,
               'scope': 'Exact finite algebra, literal coefficient identities, provenance and restoration certificates. '
                        'Unbounded arithmetic and consistency calibration remain the identified ordinary proofs. '
                        'The source coefficient recipe is deliberately replayed normally.'}
    body = json.dumps(receipt, indent=2, sort_keys=True) + '\n'
    if args.receipt:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(body)
    print('PASS: ' + str(len(results)) + ' stages; ordinary proofs and formalization boundaries remain as documented.')


if __name__ == '__main__':
    main()
