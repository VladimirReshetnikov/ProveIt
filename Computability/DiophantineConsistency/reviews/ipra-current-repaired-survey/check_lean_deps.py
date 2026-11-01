#!/usr/bin/env python3
"""Compare frozen survey header imports with Lean's own dependency parser."""
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import subprocess

D = Path(__file__).resolve().parent
M = D / 'manifest.json'
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PROJECT = Path('/tmp/ipra-frozen-ancestry-repair-6ftdeyrq/lib')
PACKAGE = Path('/tmp/pra14-full-transitive-2x6o__to/package-lib')
TOOL = LEAN.parent.parent / 'lib/lean'
digest = lambda data: hashlib.sha256(data).hexdigest()
data = json.loads(M.read_text())
env = dict(os.environ, LEAN_PATH=str(PROJECT) + ':' + str(PACKAGE))

def check(item):
    name, info = item
    path = D / 'sources' / (name.replace('.', '/') + '.lean')
    assert digest(path.read_bytes()) == info['sha256'], name
    proc = subprocess.run([str(LEAN), '--deps', str(path)], env=env, capture_output=True, text=True)
    if proc.returncode:
        return name, {'exit': proc.returncode, 'stderr': proc.stderr, 'stdout': proc.stdout}
    modules = set()
    for line in proc.stdout.splitlines():
        p = Path(line)
        rel = next((p.relative_to(root) for root in (PROJECT, PACKAGE, TOOL)
                    if p.is_relative_to(root)), None)
        if rel is None or not str(rel).endswith('.olean'):
            return name, {'error': 'unrecognized Lean dependency', 'line': line}
        modules.add(str(rel)[:-len('.olean')].replace('/', '.'))
    # Lean supplies Init implicitly, sometimes twice, even without an import.
    expected = set(info['imports']) - {'Init'}
    actual = modules - {'Init'}
    if expected != actual:
        return name, {'expected': sorted(expected), 'actual': sorted(actual)}
    return name, {'stdout_sha256': digest(proc.stdout.encode()), 'count': len(actual)}

with ThreadPoolExecutor(max_workers=4) as pool:
    rows = dict(pool.map(check, sorted(data['sources'].items())))
errors = {k: v for k, v in rows.items() if 'exit' in v or 'error' in v or 'expected' in v}
receipt = {'manifest_sha256': digest(M.read_bytes()), 'checker_sha256': digest(Path(__file__).read_bytes()),
           'lean_sha256': digest(LEAN.read_bytes()), 'count': len(rows), 'errors': errors, 'rows': rows,
           'scope': 'Lean --deps agrees with captured explicit imports; not a compiled proof.'}
(D / 'lean-deps-receipt.json').write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
print(json.dumps({'count': len(rows), 'errors': len(errors)}, sort_keys=True))
if errors:
    raise SystemExit(1)
