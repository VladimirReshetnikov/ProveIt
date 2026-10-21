#!/usr/bin/env python3
"""Rebuild the quotient calculus from source with no imported local .oleans.

Example (Lean 4.32.0):
  python3 verify_quotient.py --build-dir /tmp/quotient-check

All 110 module sources are bound to quotient_source_hashes.json. This script
copies them into a fresh build directory, sets LEAN_PATH to that directory,
and compiles them in dependency order. It uses only the Python standard
library, the bundled Lean sources, and Lean's standard library. An optional
--repo checkout can supply upstream sources instead of the bundled copies.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import time

OVERLAY = Path(__file__).resolve().parent
NEW_MODULES = {'QuotientDetachment', 'Quotient222', 'QuotientCalibration', 'QuotientEquivalence'}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path)
    parser.add_argument('--lean', default='lean')
    parser.add_argument('--build-dir', type=Path, required=True)
    parser.add_argument('--check-only', action='store_true', help='Check source hashes without compiling.')
    args = parser.parse_args()
    destination = args.build_dir.resolve()
    if args.repo:
        repo = args.repo.resolve()
        roots = [repo / p for p in [
            'Computability/BusyBeaver/Lean',
            'Logic/FirstOrder/Lean',
            'SetTheory/ZF/Lean',
            'SetTheory/BoundedConsistency/Lean',
        ]]
    else:
        roots = [OVERLAY / 'lean']
    expected = json.loads((OVERLAY / 'quotient_source_hashes.json').read_text())
    sources = {}
    visiting = set()
    ordered = []

    def visit(module):
        if module in sources:
            return
        if module.split('.')[0] in {'Init', 'Lean', 'Std'}:
            return
        if module in visiting:
            raise RuntimeError('Cyclic import: ' + module)
        visiting.add(module)
        relative = Path(*module.split('.')).with_suffix('.lean')
        choices = [OVERLAY / 'lean' / relative, OVERLAY / relative] if module in NEW_MODULES else [r / relative for r in roots]
        source = next((p for p in choices if p.is_file()), None)
        if source is None:
            raise FileNotFoundError('Missing module ' + module)
        content = source.read_bytes()
        sha = hashlib.sha256(content).hexdigest()
        if expected.get(module) != sha:
            raise ValueError(f'Source hash mismatch for {module}: {sha}; expected {expected.get(module)}')
        for dependency in re.findall(r'^import\s+(\S+)', content.decode(), re.MULTILINE):
            visit(dependency)
        sources[module] = (source, relative, sha)
        ordered.append(module)
        visiting.remove(module)

    visit('QuotientEquivalence')
    if set(ordered) != set(expected):
        raise ValueError('The import closure differs from the source manifest.')
    print(f'Verified source hashes for {len(ordered)} modules.', flush=True)
    if args.check_only:
        return 0
    if destination.exists() and any(destination.iterdir()):
        raise ValueError('The build directory must be empty; old .oleans are not reused.')
    version = subprocess.check_output([args.lean, '--version'], text=True).strip()
    if '4.32.0' not in version:
        raise ValueError('This artifact was checked with Lean 4.32.0; found ' + version)
    destination.mkdir(parents=True, exist_ok=True)
    for source, relative, _ in sources.values():
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
    env = dict(os.environ, LEAN_PATH=str(destination))
    records = []
    for index, module in enumerate(ordered, 1):
        source, relative, sha = sources[module]
        target = destination / relative
        log = target.with_suffix('.log')
        started = time.monotonic()
        with log.open('w') as stream:
            result = subprocess.run([args.lean, '-o', str(target.with_suffix('.olean')), str(target)],
                cwd=destination, env=env, stdout=stream, stderr=subprocess.STDOUT)
        record = {'module': module, 'sha256': sha, 'returncode': result.returncode,
            'seconds': time.monotonic() - started, 'log': str(log.relative_to(destination))}
        records.append(record)
        (destination / 'build_manifest.json').write_text(json.dumps(
            {'lean': version, 'modules': records}, indent=2) + '\n')
        print(f'{index}/{len(ordered)} {module}: returncode {result.returncode}', flush=True)
        if result.returncode:
            print(log.read_text())
            return result.returncode
    print((destination / 'QuotientEquivalence.log').read_text())
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
