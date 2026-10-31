#!/usr/bin/env python3
"""Rebuild the affected project suffix for the generic PRA bound bridge.

The parent project objects and Foundation/package boundary are inherited;
hash guards are not a claim that their entire transitive ancestry was rebuilt.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[4]
SRC = ROOT / 'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
PARENT = Path('/tmp/pra-after-open-bound-merge-refresh-9m9dtqdk')
ENV_STATE = Path('/tmp/pra-witness-fold-refresh-6xz3_lem/state.json')
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
parent_state = json.loads((PARENT / 'state.json').read_text())
assert parent_state['status'] == 'PASS'
known = parent_state['initial_source_sha256']
seen, affected, order, deps, hashes = set(), set(), [], {}, {}

def visit(name):
    if name in seen:
        return
    seen.add(name)
    src = SRC / (name + '.lean')
    hashes[name] = sha(src)
    ds = re.findall(r'^import DiophantineConsistency\.(\w+)', src.read_text(), re.M)
    deps[name] = ds
    for dep in ds:
        visit(dep)
    obj = PARENT / 'lib/DiophantineConsistency' / (name + '.olean')
    if known.get(name) != hashes[name] or not obj.is_file() or any(d in affected for d in ds):
        affected.add(name)
        order.append(name)

visit('PRAWitnessBoundCertificateChecks')
work = Path(tempfile.mkdtemp(prefix='pra-witness-bound-certificate-'))
lib = work / 'lib'
dest = lib / 'DiophantineConsistency'
dest.mkdir(parents=True)
logs = work / 'logs'
logs.mkdir()
parentlib = PARENT / 'lib'
for top in parentlib.iterdir():
    if top.name != 'DiophantineConsistency':
        (lib / top.name).symlink_to(top.resolve(), target_is_directory=top.is_dir())
for obj in (parentlib / 'DiophantineConsistency').glob('*.olean'):
    if obj.stem not in affected:
        (dest / obj.name).symlink_to(obj.resolve())
inherited = {n: sha(dest / (n + '.olean')) for n in seen - affected}
parent_hash = sha(PARENT / 'state.json')
base_path = json.loads(ENV_STATE.read_text())['LEAN_PATH']
env = dict(os.environ, LEAN_PATH=str(lib) + ':' + base_path, LEAN_NUM_THREADS='1')
env.pop('LEAN_SRC_PATH', None)
state = {'status': 'RUNNING', 'root': str(work), 'parent': str(PARENT),
         'parent_state_sha256': parent_hash, 'sources': hashes, 'deps': deps,
         'inherited_project_objects': inherited, 'order': order, 'records': [],
         'boundary': 'Inherited parent/project and Foundation/package ancestry; not a full clean rebuild.'}

def save():
    tmp = work / 'state.tmp'
    tmp.write_text(json.dumps(state, indent=2) + '\n')
    tmp.replace(work / 'state.json')

def audit():
    assert sha(PARENT / 'state.json') == parent_hash
    assert all(sha(SRC / (n + '.lean')) == h for n, h in hashes.items())
    assert all(sha(dest / (n + '.olean')) == h for n, h in inherited.items())

save()
print('ROOT', work, 'closure', len(seen), 'rebuild', len(order), flush=True)
try:
    audit()
    for name in order:
        state['module'] = name
        save()
        src = SRC / (name + '.lean')
        log = logs / (name + '.log')
        out = dest / (name + '.olean')
        start = time.monotonic()
        with log.open('w') as f:
            result = subprocess.run(['lean', '-M6000', '-j1', '-DElab.async=false',
                                     str(src), '-o', str(out)], cwd=ROOT, env=env,
                                    stdout=f, stderr=subprocess.STDOUT)
        row = {'module': name, 'exit': result.returncode,
               'seconds': time.monotonic() - start, 'source_sha256': sha(src),
               'object_sha256': sha(out) if out.is_file() else None, 'log_sha256': sha(log)}
        state['records'].append(row)
        save()
        assert result.returncode == 0 and not re.search(r'\b(?:warning|error|sorryAx)\b', log.read_text())
        assert sha(src) == hashes[name]
        print('PASS', name, flush=True)
    audit()
    state['module'] = None
    state['status'] = 'PASS'
    save()
    print('PASS', work, flush=True)
except BaseException as exc:
    state.update(status='FAILED', failure=repr(exc))
    save()
    raise
