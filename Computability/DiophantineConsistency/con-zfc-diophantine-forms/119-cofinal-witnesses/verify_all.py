#!/usr/bin/env python3
"""Offline finite verification of the complete ConZFC witness-reuse packet.

This program checks artifacts and finite regressions, not the unbounded
semantic theorem or the absence of solutions. Python's standard library only.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def manifest_check() -> dict:
    manifest = ROOT / 'MANIFEST.sha256'
    require(manifest.is_file(), 'Release manifest is missing')
    seen = set()
    for line in manifest.read_text(encoding='utf-8').splitlines():
        digest, name = line.split('  ', 1)
        require(len(digest) == 64 and all(c in '0123456789abcdef' for c in digest),
                'Invalid manifest digest')
        require(name not in seen, 'Duplicate manifest path: ' + name)
        relative = Path(name)
        require(not relative.is_absolute() and '..' not in relative.parts,
                'Unsafe manifest path: ' + name)
        path = ROOT / relative
        require(path.is_file() and not path.is_symlink(), 'Missing regular file: ' + name)
        require(sha(path) == digest, 'Release hash mismatch: ' + name)
        seen.add(name)
    require(bool(seen), 'Empty release manifest')
    return {'status': 'PASS', 'files': len(seen)}


def source_check() -> dict:
    ledger = json.loads((ROOT / 'SOURCE_LEDGER.json').read_text())
    require(ledger['commit'] == '45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6',
            'Unexpected source snapshot')
    for row in ledger['files']:
        require(sha(ROOT / row['delivered']) == row['sha256'],
                'Inherited source hash mismatch: ' + row['delivered'])
    return {'status': 'PASS', 'files': len(ledger['files']), 'commit': ledger['commit']}


def run(relative_script: str, *arguments: str) -> dict:
    script = ROOT / relative_script
    command = [sys.executable, '-B']
    if sys.flags.optimize:
        command.append('-O')
    command.extend([str(script), *map(str, arguments)])
    environment = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    result = subprocess.run(command, cwd=script.parent, env=environment,
                            capture_output=True, text=True)
    require(result.returncode == 0,
            relative_script + ' failed:\n' + result.stdout + '\n' + result.stderr)
    try:
        receipt = json.loads(result.stdout)
    except json.JSONDecodeError as error:
        raise ValueError(relative_script + ' did not return a JSON receipt') from error
    require(receipt.get('status', 'PASS') == 'PASS', relative_script + ' reported failure')
    print('PASS ' + relative_script, flush=True)
    return receipt


def regenerate(directory: str, destination: Path, expected_count: int) -> dict:
    run(directory + '/build.py', '--output', str(destination))
    emitted = sorted(destination.glob('*.json'))
    require(len(emitted) == expected_count, 'Unexpected rebuilt artifact count: ' + directory)
    hashes = {}
    for path in emitted:
        original = ROOT / directory / path.name
        require(original.is_file(), 'No released counterpart for ' + path.name)
        require(path.read_bytes() == original.read_bytes(),
                'Rebuilt artifact differs: ' + directory + '/' + path.name)
        hashes[path.name] = sha(path)
    return {'status': 'PASS', 'byte_identical_json_files': hashes}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-manifest', action='store_true',
                        help='For intentionally edited working copies only')
    parser.add_argument('--regenerate', action='store_true',
                        help='Also rebuild both direct constructions in temporary directories')
    parser.add_argument('--output', type=Path, help='Optional new aggregate receipt path')
    args = parser.parse_args()
    receipt = {
        'status': 'PASS',
        'optimized_python': bool(sys.flags.optimize),
        'scope': 'Finite artifact identities and explicitly finite semantic regressions; '
                 'not a proof of consistency or an end-to-end proof-assistant derivation.',
        'release_manifest': {'status': 'SKIPPED_FOR_WORKING_COPY'} if args.skip_manifest else manifest_check(),
        'inherited_sources': source_check(),
    }
    with tempfile.TemporaryDirectory(prefix='conzfc-verify-') as temporary:
        temp = Path(temporary)
        receipt['principal'] = run('direct/principal/verify.py')
        receipt['checkpoint'] = run('direct/verify.py')
        receipt['positive_build'] = run('positive/build.py', '--check')
        receipt['positive'] = run('positive/verify.py')
        receipt['semantic_regressions'] = run('checks/check_cofinal_semantics.py',
            '--proof-dir', str(ROOT / 'proofs'), '--output', str(temp / 'semantic.json'))
        receipt['residual_appendix'] = run('report/generate_residuals.py', '--check')
        if args.regenerate:
            receipt['principal_regeneration'] = regenerate('direct/principal', temp / 'principal', 11)
            receipt['checkpoint_regeneration'] = regenerate('direct', temp / 'checkpoint', 5)
    if args.output:
        args.output.write_text(json.dumps(receipt, sort_keys=True, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'status': 'PASS', 'optimized_python': bool(sys.flags.optimize),
                      'regenerated': bool(args.regenerate),
                      'manifest_checked': not args.skip_manifest,
                      'principal_metrics': receipt['principal']['metrics'],
                      'receipt': str(args.output) if args.output else None}, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError) as error:
        print('FAIL: ' + str(error), file=sys.stderr)
        raise SystemExit(1)
