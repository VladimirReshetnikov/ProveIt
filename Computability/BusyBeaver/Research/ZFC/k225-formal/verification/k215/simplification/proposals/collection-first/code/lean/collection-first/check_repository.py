#!/usr/bin/env python3
"""Kernel-check the proposed GIC module against the pinned local repository.

Usage: python3 check_repository.py PATH_TO_PROVEIT PATH_TO_LEAN
Builds the actual repository imports required by the proposed quotient route.
No installed Mathlib, network operation, or repository source edit is needed.
"""
import os
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

repo, lean = (Path(x).resolve() for x in sys.argv[1:])
here = Path(__file__).resolve().parent
build = here / 'build'
roots = [here, repo / 'Computability/BusyBeaver/Lean',
         repo / 'Logic/FirstOrder/Lean', repo / 'SetTheory/ZF/Lean']
seen, ordered = set(), []

def uncomment(text):
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            i += 2
        elif not depth and text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            if not depth or text[i] == '\n':
                out.append(text[i])
            i += 1
    return ''.join(out)

def visit(name):
    if name in seen:
        return
    seen.add(name)
    candidates = [r.joinpath(*name.split('.')).with_suffix('.lean') for r in roots]
    source = next((p for p in candidates if p.exists()), None)
    if source is None:
        raise RuntimeError(f'Unexpected external module: {name}')
    for line in uncomment(source.read_text()).splitlines():
        if line.startswith('import '):
            for dep in line.split()[1:]:
                visit(dep)
    ordered.append((name, source))

visit('QuotientConsequenceAdapters')
visit('WFSeparationAdapter')
ordered.insert(0, ('CollectionFirst', here / 'CollectionFirst.lean'))
env = dict(os.environ, LEAN_PATH=str(build))
build.mkdir(exist_ok=True)
snapshot = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip()
expected = '6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95'
if snapshot != expected:
    raise RuntimeError(f'Expected repository snapshot {expected}; found {snapshot}')
version = subprocess.check_output([str(lean), '--version'], text=True).strip()
evidence = {'baseline_commit': snapshot, 'compiler': version, 'modules': [],
            'scope': 'Standalone core and actual repository schema adapters; full endpoint not rebuilt'}
with (here / 'repository-check.log').open('w') as log:
    for name, source in ordered:
        target = build.joinpath(*name.split('.')).with_suffix('.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        print(f'CHECK {name}', flush=True)
        log.write(f'CHECK {name}\n')
        log.flush()
        result = subprocess.run([str(lean), '-o', str(target), str(source)],
            cwd=repo if source.is_relative_to(repo) else here,
            env=env, capture_output=True, text=True)
        log.write(result.stdout + result.stderr)
        log.write(f'EXIT {result.returncode}\n')
        log.flush()
        data = source.read_bytes()
        evidence['modules'].append({'module': name, 'exit_code': result.returncode,
            'source_sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data),
            'physical_lines': len(data.splitlines()),
            'source_kind': 'baseline' if source.is_relative_to(repo) else 'proposal'})
        (here / 'repository-check.json').write_text(json.dumps(evidence, indent=2) + '\n')
        if result.returncode:
            print(result.stdout + result.stderr, flush=True)
            sys.exit(result.returncode)
    print(f'PASS: {len(ordered)} modules; see repository-check.log', flush=True)
