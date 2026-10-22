#!/usr/bin/env python3
"""Replay a source-pinned, serial Lean component check in a fresh directory.

No network access, repository mutation, package manager, or repository generator
is used. Only the requested source overlays and their actual import closure are
compiled. The default combined mode checks both proposals and three audit files.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time
import tomllib

PIN = '6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95'
HERE = Path(__file__).resolve().parent

def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path, required=True)
    ap.add_argument('--lean', type=Path, required=True)
    ap.add_argument('--build-dir', type=Path, required=True)
    ap.add_argument('--mode', choices=['combined', 'envelope', 'baseline'], default='combined')
    args = ap.parse_args()
    repo, lean, build = args.repo.resolve(), args.lean.resolve(), args.build_dir.resolve()
    head = subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip()
    if head != PIN:
        raise SystemExit(f'Expected repository revision {PIN}; found {head}')
    version = subprocess.check_output([str(lean), '--version'], text=True).strip()
    if 'version 4.32.0,' not in version:
        raise SystemExit(f'Expected Lean 4.32.0, found {version}')
    if build.exists():
        raise SystemExit('Use a fresh --build-dir; existing proof objects are never silently reused.')
    build.mkdir(parents=True)
    objects, logs = build / 'objects', build / 'logs'
    objects.mkdir(); logs.mkdir()
    config = tomllib.loads((repo / 'lakefile.toml').read_text())
    source_roots = list(dict.fromkeys([repo / lib.get('srcDir', '.') for lib in config['lean_lib']]))
    overlays = {}
    if args.mode != 'baseline':
        names = ['KLowerTag', 'KLowerQHyp']
        if args.mode == 'combined':
            names += ['KLowerRaw', 'KSeedFunctional']
        for name in names:
            overlays['BusyBeaver.ZFC.' + name] = HERE / 'overlay/BusyBeaver/ZFC' / (name + '.lean')
    roots = {
        'combined': ['AuditSeedInterfaces', 'AuditRawAxioms', 'SeedClosureCounterexample'],
        'envelope': ['AuditEnvelope'],
        'baseline': ['AuditRawAxioms'],
    }[args.mode]
    for name in roots:
        overlays[name] = HERE / 'audits' / (name + '.lean')
    sources, dependencies, order, active = {}, {}, [], set()

    def visit(name: str) -> None:
        if name in active:
            raise RuntimeError(f'Import cycle at {name}')
        if name in sources or name.split('.')[0] in {'Init', 'Std', 'Lean'}:
            return
        if name in overlays:
            path = overlays[name]
        else:
            relative = Path(*name.split('.')).with_suffix('.lean')
            choices = [r / relative for r in source_roots if (r / relative).is_file()]
            if len(choices) != 1:
                raise RuntimeError(f'Expected one source for {name}, found {choices}; check sparse checkout.')
            path = choices[0]
        if not path.is_file():
            raise RuntimeError(f'Missing source {path}')
        deps = []
        for line in path.read_text().splitlines():
            match = re.match(r'^(?:public\s+)?import\s+(.+)', line)
            if match:
                deps.extend(match.group(1).split('--', 1)[0].split())
        active.add(name)
        for dep in deps:
            visit(dep)
        active.remove(name)
        sources[name], dependencies[name] = path, deps
        order.append(name)

    for name in roots:
        visit(name)
    records = []
    receipt = {
        'status': 'RUNNING', 'scope': 'semantic component, not physical-machine endpoint',
        'mode': args.mode, 'repository_commit': head, 'toolchain': version,
        'project_module_count': len(order) - len(roots), 'audit_module_count': len(roots),
        'records': records,
    }
    env = dict(os.environ, LEAN_PATH=str(objects))
    for index, name in enumerate(order):
        source = sources[name]
        output = objects / (name.replace('.', '/') + '.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
        command = [str(lean), '-o', str(output), str(source)]
        print(f'{index + 1}/{len(order)} {name}', flush=True)
        start = time.monotonic()
        completed = subprocess.run(command, text=True, capture_output=True, env=env)
        log = logs / (name + '.log')
        log.write_text(completed.stdout + completed.stderr)
        ref = ('packet:' + str(source.relative_to(HERE))) if source.is_relative_to(HERE) else ('repo:' + str(source.relative_to(repo)))
        record = {
            'module': name, 'source': ref, 'sha256': digest(source),
            'imports': dependencies[name], 'command': command,
            'exit_code': completed.returncode, 'elapsed_seconds': round(time.monotonic() - start, 6),
            'log': str(log.relative_to(build)), 'log_sha256': digest(log),
        }
        records.append(record)
        if completed.returncode or 'sorryAx' in log.read_text():
            receipt['status'] = 'FAIL'
            (build / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
            print(log.read_text())
            return 1
        (build / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    if args.mode in {'combined', 'baseline'}:
        expected = HERE / 'evidence/baseline-RawAxioms.log'
        actual = logs / 'AuditRawAxioms.log'
        receipt['raw_axiom_profiles_match_baseline'] = actual.read_bytes() == expected.read_bytes()
        if not receipt['raw_axiom_profiles_match_baseline']:
            receipt['status'] = 'FAIL_ASSUMPTION_PROFILE'
            (build / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
            return 1
    receipt['status'] = 'PASS_FRESH_COMPONENT_CHECK'
    receipt['elapsed_seconds_sum'] = round(sum(r['elapsed_seconds'] for r in records), 6)
    (build / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: v for k, v in receipt.items() if k != 'records'}, indent=2))
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
